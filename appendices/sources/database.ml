open Lwt.Infix
open Type
open Printf
open Astring

let ( ++ ) = Int64.add

let map_snd f = Lwt_list.map_p (fun (a, b) -> f b >|= fun b -> (a, b))

module Make
    (Hash : S.HASH) (Backend : S.BACKEND)
    (Branch_T : S.TYPE) (Step_T : S.TYPE) (Blob_T : S.TYPE) =
struct
  (** {3 Basic type declarations.} *)

  type branch = Branch_T.t
  let branch_t = Branch_T.t

  type step = Step_T.t
  let step_t = Step_T.t

  type path = step list

  type blob = Blob_T.t
  let blob_t = Blob_T.t

  type tree = [ `Blob of blob | `Node of (step * tree) list ]
  type commit_hash = CH of string [@@unboxed] [@@deriving irmin]
  type node_hash = NH of string [@@unboxed] [@@deriving irmin]
  type blob_hash = BH of string [@@unboxed] [@@deriving irmin]

  let string_of_hash h =
    h |> Hash.Digest.unserialize |> Result.get_ok |> Hash.Digest.to_hex

  type node = (step * [ `Node of node_hash | `Blob of blob_hash ]) list
  [@@deriving irmin]

  type commit = {
    parents : commit_hash list;
    node : node_hash;
    message : string;
  }
  [@@deriving irmin]

  module Commit_T = struct
    type t = commit
    let t = commit_t
  end

  module Node_T = struct
    type t = node
    let t = node_t
  end

  (** {3 Type declarations for the object graph.} *)

  type graph_label = step option [@@deriving irmin]
  (** Type of edge labels in the graph. *)

  type graph_vertex =
    [ `Branch of branch
    | `Commit of commit_hash
    | `Node of node_hash
    | `Blob of blob_hash ]
  [@@deriving irmin]
  (** Type of vertices in the graph. *)

  module Graph_Label_T = struct
    type t = graph_label
    let t = graph_label_t
  end

  module Graph_Vertex_T = struct
    type t = graph_vertex
    let t = graph_vertex_t

    let print = function
      | `Branch b -> Printf.sprintf "b:%s" (Irmin.Type.to_string branch_t b)
      | `Commit (CH h) -> Printf.sprintf "c:%s" (string_of_hash h)
      | `Node (NH h) -> Printf.sprintf "n:%s" (string_of_hash h)
      | `Blob (BH h) -> Printf.sprintf "b:%s" (string_of_hash h)
  end

  module OGraph = Object_graph.Make (Graph_Label_T) (Graph_Vertex_T)

  (** {3 Type declarations for the database.} *)

  type config = Backend.config

  module Branch = Hashable (Hash) (Branch_T)
  module Commit = Hashable (Hash) (Commit_T)
  module Node = Hashable (Hash) (Node_T)
  module Blob = Hashable (Hash) (Blob_T)
  module Backend = Backend.Make (Branch) (Commit) (Node) (Blob)

  type t = {
    backend : Backend.t;
    config : config;
    (* Whether a pass of garbage collection is currently taking place. *)
    mutable gc_active : bool;
    (* Set of objects which are being considered by the garbage collector. *)
    gc_pending : (OGraph.Table.key * int) Stack.t;
    (* Set of objects which have been marked as "in use" by the garbage collector. *)
    gc_marked : int OGraph.Table.t;
    (* Various statistics about the current instance. *)
    mutable blobs_count : int64;
    mutable nodes_count : int64;
    mutable commits_count : int64;
  }

  let branches_store t = Backend.branches_t t.backend

  let commits_store t = Backend.commits_t t.backend

  let nodes_store t = Backend.nodes_t t.backend

  let blobs_store t = Backend.blobs_t t.backend

  type workspace = {
    t : t;
    (* Pointer to the current branch or the current detached commit. *)
    head : [ `Branch of branch | `Head of commit_hash option ref ];
  }

  (** Adds an object to the list of marked objects if needed.

      This is crucial to allow incremental garbage collection: when the tracing
      algorithm is currently running, keeping track of newly allocated objects
      avoids the "lost object" problem. *)
  let mark_newly_allocated t h =
    if t.gc_active then OGraph.Table.add t.gc_marked h (-1)

  (** Adds an branch target to the list of pending objects if needed. *)
  let mark_updated_branch t h =
    if t.gc_active && (not OGraph.Table.mem t.gc_marked h) then
      Stack.push (h, -1) t.gc_pending

  (** {3 Operations on blobs.} *)

  module Blobs = struct
    let set t b =
      t.blobs_count <- t.blobs_count ++ 1L;
      Backend.Blobs.set (blobs_store t) b >|= fun d ->
      let hash = BH (Blob.Digest.serialize d) in
      mark_newly_allocated t (`Blob hash);
      hash

    let to_hash b = BH (Blob.hash b |> Blob.Digest.serialize)

    let of_hash t (BH h) =
      Backend.Blobs.find (blobs_store t)
        (Blob.Digest.unserialize h |> Result.get_ok)
      >|= Option.get
  end

  (** {3 Operations on nodes.} *)

  module Nodes = struct
    let set t n =
      t.nodes_count <- t.nodes_count ++ 1L;
      Backend.Nodes.set (nodes_store t) n >|= fun d ->
      let hash = NH (Node.Digest.serialize d) in
      mark_newly_allocated t (`Node hash);
      hash

    let to_hash n = NH (Node.hash n |> Node.Digest.serialize)

    let of_hash t (NH h) =
      Backend.Nodes.find (nodes_store t)
        (Node.Digest.unserialize h |> Result.get_ok)
      >|= Option.get

    let children t n =
      n
      |> map_snd (function
           | `Blob b -> Blobs.of_hash t b >|= fun b -> `Blob b
           | `Node n -> of_hash t n >|= fun b -> `Node b)

    let tree t n =
      let rec aux n =
        n
        |> map_snd (function
             | `Blob b -> Blobs.of_hash t b >|= fun b -> `Blob b
             | `Node n -> of_hash t n >>= aux >|= fun b -> `Node b)
      in
      aux n >|= fun n -> `Node n
  end

  (** {3 Operations on commits.} *)

  module Commits = struct
    let set t c =
      t.commits_count <- t.commits_count ++ 1L;
      Backend.Commits.set (commits_store t) c >|= fun d ->
      let hash = CH (Commit.Digest.serialize d) in
      mark_newly_allocated t (`Commit hash);
      hash

    let to_hash c = CH (Commit.hash c |> Commit.Digest.serialize)

    let of_hash t (CH h) =
      Backend.Commits.find (commits_store t)
        (Commit.Digest.unserialize h |> Result.get_ok)
      >|= Option.get

    let parents t c = c.parents |> Lwt_list.map_p (of_hash t)

    let node t c = Nodes.of_hash t c.node

    let tree t c = node t c >>= Nodes.tree t

    let message c = c.message
  end

  (** {3 Operations on branches.} *)

  module Branches = struct
    let mem t = Backend.Branches.mem (branches_store t)

    let get_commit_hash t b =
      Backend.Branches.find (branches_store t) b >|= function
      | Some h -> CH (Commit.Digest.serialize h)
      | _ -> invalid_arg "Branch not found."

    let set_commit_hash t b (CH h) =
      (* The commit might needs to be colored grey. *)
      mark_updated_branch (`Commit (CH h));

      Backend.Branches.set (branches_store t) b
        (Commit.Digest.unserialize h |> Result.get_ok)

    let get t b = get_commit_hash t b >>= fun h -> Commits.of_hash t h

    let set t b c = Commits.to_hash c |> set_commit_hash t b

    let remove t = Backend.Branches.remove (branches_store t)

    let list t = Backend.Branches.list (branches_store t)
  end

  (** {3 Creating database instances.} *)

  let create config =
    {
      backend = Backend.create config;
      config;
      gc_active = false;
      gc_pending = Stack.create ();
      gc_marked = OGraph.Table.create 2048;
      blobs_count = 0L;
      nodes_count = 0L;
      commits_count = 0L;
    }

  let initialize ~master t =
    let message = "Initial commit." in
    let%lwt node_hash = Nodes.set t [] in
    let commit = { parents = []; node = node_hash; message } in
    let%lwt commit_hash = Commits.set t commit in
    Branches.set_commit_hash t master commit_hash

  let close t = Backend.close t.backend

  (** {3 Opening workspaces.} *)

  let checkout t branch = Lwt.return { t; head = `Branch branch }

  let detach t commit = Lwt.return { t; head = `Head (ref (Some commit)) }

  (** {3 Operations on workspaces.} *)

  let database w = w.t

  let head w =
    match w.head with
    | `Branch b -> Branches.get w.t b
    | `Head r -> (
        match !r with
        | Some c -> Commits.of_hash w.t c
        | None -> invalid_arg "Head reference is not set." )

  (** {3 Operations on the object graph.} *)

  module Graph = struct
    type vertex = graph_vertex

    type label = graph_label

    (* Returns the predecessors of the current vertex in the graph. *)
    let pred ?(full = false) t =
      let to_commit x : vertex = `Commit x in
      let to_node x : vertex = `Node x in
      let to_blob x : vertex = `Blob x in

      function
      | `Branch b ->
          Branches.get_commit_hash t b >|= fun h -> [ (None, to_commit h) ]
      | `Commit k ->
          Commits.of_hash t k >|= fun c ->
          let next_commits =
            c.parents |> List.map (fun c -> (None, to_commit c))
          in
          let next_node = (None, c.node |> to_node) in
          if full then next_node :: next_commits else next_commits
      | `Node k ->
          Nodes.of_hash t k
          >|= List.map (function
                | step, `Node n -> (Some step, to_node n)
                | step, `Blob b -> (Some step, to_blob b))
      | `Blob _ -> Lwt.return []

    let iter ?depth ?(full = false) ?(rev = true) ~min ~max ~vertex ~edge ~skip
        t =
      let pred = pred ~full t in
      OGraph.iter ?depth ~pred ~min ~max ~vertex ~edge ~skip ~rev ()

    let mark ?(roots = `Branches) ?limit_count ?limit_time t =
      let count = ref 0 in
      let start = Sys.time () in
      (* Find the entry-points for the graph traversal. *)
      ( match roots with
      | `Branches ->
          (* Lists the commits currently associated to the branches. *)
          Branches.list t >>= fun branches ->
          Lwt_list.map_p (Branches.get_commit_hash t) branches
      | `List commits ->
          (* Lets the user specify a custom list of commits as roots. *)
          commits |> List.map Commits.to_hash |> Lwt.return )
      >|= List.map (fun c -> `Commit c)
      >>= fun entrypoints ->
      let pred = pred ~full:true t in
      let mark key level = OGraph.Table.add t.gc_marked key level in
      let has_mark key = OGraph.Table.mem t.gc_marked key in
      (* Add the entrypoints to the set of pending objects. *)
      List.iter (fun k -> Stack.push (k, 0) t.gc_pending) entrypoints;
      (* Traverse the graph and mark the encountered objects. *)
      let rec visit () =
        (* Check whether an object count or time limit was reached. *)
        if
          match (limit_count, limit_time) with
          | Some c, _ -> !count > c
          | _, Some t -> !count mod 1000 = 0 && Sys.time () -. start > t
          | _ -> false
        then Lwt.return `Partial
        else
          match Stack.top t.gc_pending with
          | exception Stack.Empty ->
              Log.info (fun l -> l "Tracing duration: %fs." (Sys.time () -. start));
              Lwt.return `Done
          | key, level ->
              if has_mark key then (
                ignore (Stack.pop t.gc_pending);
                (visit [@tailcall]) () )
              else (
                incr count;
                mark key level;
                pred key >>= fun keys ->
                List.iter
                  (fun (_, k) ->
                    if not (has_mark k) then
                      Stack.push (k, level + 1) t.gc_pending)
                  keys;
                (visit [@tailcall]) () )
      in
      visit ()

    let cleanup ?roots ?limit_count ?limit_time t =
      Log.info (fun l -> l "Starting the garbage collector.");

      (* Log statistics about the current database. *)
      Log.info (fun l -> l "Current number of commits: %Ld" t.commits_count);
      Log.info (fun l -> l "Current number of nodes: %Ld" t.nodes_count);
      Log.info (fun l -> l "Current number of blobs: %Ld" t.blobs_count);

      (* When starting a new pass, clear the sets used by the previous pass. *)
      if not t.gc_active then (
        t.gc_active <- true;
        Stack.clear t.gc_pending;
        OGraph.Table.clear t.gc_marked );

      (* Start the incremental tracing algorithm.
         - If it returns [`Partial], a count or time constraint was reached and
           the tracing algorithm was forced to yield. It will continue its
           current run the next time it is called.
         - If it returns [`Done], t.gc_marked now contains the exact set of
           objects which should be treated as "in use". *)
      mark ?roots ?limit_count ?limit_time t >>= function
      | `Partial -> Lwt.return_error `Run_again
      | `Done ->
          (* Filter the stores to keep only the encountered objects. *)
          Backend.Commits.filter (commits_store t) (fun k ->
              OGraph.Table.mem t.gc_marked
                (`Commit (CH (Commit.Digest.serialize k))))
          >>= fun () ->
          Backend.Nodes.filter (nodes_store t) (fun k ->
              OGraph.Table.mem t.gc_marked
                (`Node (NH (Node.Digest.serialize k))))
          >>= fun () ->
          Backend.Blobs.filter (blobs_store t) (fun k ->
              OGraph.Table.mem t.gc_marked
                (`Blob (BH (Blob.Digest.serialize k))))
          >>= fun () ->
          t.gc_active <- false;
          Lwt.return_ok ()
  end
end

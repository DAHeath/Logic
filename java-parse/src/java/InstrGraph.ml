module JProgram = Sawja_pack.JProgram
module JBasics = Javalib_pack.JBasics
module JBir = Sawja_pack.JBir
module QID = QualifiedIdentity

open Core

module Instr = struct
  type t = QID.t * JBir.instr

  let equal (a, _) (b, _) = a = b
  let hash (id, _) = QID.to_string "/" id |> String.hash
  let compare (a, _) (b, _) =
    String.compare (QID.to_string "/" a) (QID.to_string "/" b)
end

module Branch = struct
  type t =
    Goto
    | True
    | False

  let hash = function
    | False -> 0
    | True -> 1
    | Goto -> 2
  let equal a b = a = b
  let compare a b = (hash a) - (hash b)
  let default = Goto
  let to_string = function
    | Goto -> "goto"
    | True -> "true"
    | False -> "false"
end

include Graph.Persistent.Digraph.ConcreteBidirectionalLabeled(Instr)(Branch)


let cms_to_qid cms =
  let (jclass, jmethod) = JBasics.cms_split cms in
  QID.QID [JBasics.cn_name jclass; JBasics.ms_name jmethod]


let cms_to_instrs program cms =
  let open JProgram in
  let open Javalib_pack.Javalib in

  let (entry_class, entry_method) =
    JBasics.ClassMethodMap.find cms program.parsed_methods in

  match entry_method.cm_implementation with
    | Native -> Error `Native
    | Java java -> Ok (Lazy.force java |> JBir.code)


let append_instrs
      (prefix: QID.t)
      (instrs: JBir.instr array)
      (start_graph: t)
  =
  let collect_vertices i graph instr =
    let path = QID.specify prefix (string_of_int i) in
    let vertex = (path, instr) in

    let dest_i = match instr with
      | JBir.Goto target -> [(Branch.Goto, target)]
      | JBir.Ifd (_, target) -> [(Branch.False, i + 1); (Branch.True, target)]
      | JBir.Throw _ -> []
      | JBir.Return _ -> []
      | _ -> [(Branch.Goto, i + 1)]
    in
    let connect_vertices graph (br, j) =
      let instr = Array.nget instrs j in
      let v = (QID.specify prefix (string_of_int j), instr) in
      add_edge_e graph (E.create vertex br v)
    in

    List.fold dest_i ~init:graph ~f:connect_vertices
  in
  Array.foldi instrs ~init:start_graph ~f:collect_vertices


let build_graph
      (program: JBir.t JProgram.program)
      (method_sig: JBasics.class_method_signature)
  =
  let instrs = match cms_to_instrs program method_sig with
    | Error `Native -> failwith "Cannot analyze native methods!"
    | Ok instrs -> instrs
  in
  append_instrs (cms_to_qid method_sig) instrs empty


(* let graph = match Map.find verts i with *)
(*   | Some fs -> List.map ~f:(fun f -> f (path, instr)) fs *)
(*                |> List.fold ~init:graph ~f:add_edge_e *)
(*   | None -> graph *)
(* in *)

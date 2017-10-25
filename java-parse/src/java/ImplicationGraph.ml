open Core

module QID = QualifiedIdentity
module Env = Sawja_pack.Live_bir.Env

module Edge = struct
  type t = {
      formula: Ir.expr;
    }
  [@@deriving hash, compare]

  let default = { formula = Ir.LBool true }
  let equal = (=)
end

module Vertex = struct
  type t = {
      loc: QualifiedIdentity.t;
      live: string list;
    }
  [@@deriving hash, compare]

  let equal = (=)
end

include Graph.Persistent.Digraph.ConcreteBidirectionalLabeled(Vertex)(Edge)


let to_implication
      (instr_graph: InstrGraph.t)
      vartable
  =
  let build
        ((v: InstrGraph.V.t), (e: InstrGraph.E.label), (v': InstrGraph.V.t))
        (graph: t) =
    let open Vertex in
    let open Edge in
    let live_names env = env |> Env.elements |> List.map ~f:InstrGraph.var_name in
    let start = {
        loc = v.InstrGraph.Instr.loc;
        live = live_names v.InstrGraph.Instr.live;
      } in
    let finish = {
        loc = v'.InstrGraph.Instr.loc;
        live = live_names v.InstrGraph.Instr.live;
      } in
    let instr = v.InstrGraph.Instr.instr in
    let expr = match (InstrGraph.instr_to_expr vartable instr, e) with
      | (None, _) -> Ir.LBool true
      | (Some expr, InstrGraph.Branch.True) -> expr
      | (Some expr, InstrGraph.Branch.Goto) -> expr
      | (Some expr, InstrGraph.Branch.False) -> Ir.ExprCons (Ir.Not, expr)
    in
    add_edge_e graph (E.create start { formula = expr } finish)
  in
  InstrGraph.fold_edges_e build instr_graph empty


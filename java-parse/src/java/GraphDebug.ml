module Env = Sawja_pack.Live_bir.Env

open Core

(* module for creating dot-files *)
module InstrDot = struct
  include InstrGraph

  let get_subgraph _ = None

  let branch_to_str = function
    | Branch.Goto -> ""
    | Branch.True -> "true"
    | Branch.False -> "false"

  let edge_attributes e = [
      `Label (E.label e |> branch_to_str);
      `Fontname "monospace"
    ]
  let default_edge_attributes _ = []

  let vertex_name v =
    QID.as_path v.InstrGraph.Instr.loc |> Printf.sprintf "\"%s\""

  let vertex_label v =
    let open InstrGraph.Instr in
    let instr_txt = JBir.print_instr ~show_type:false v.instr
                    |> String.substr_replace_all ~pattern:">" ~with_:"&gt;"
    in
    let live = v.live
             |> Env.elements
             |> List.map ~f:JBir.var_name_g
             |> String.concat ~sep:", "
    in
    let path = QID.as_path v.loc in
    Printf.sprintf "<font color=\"grey\" point-size=\"10\">%s</font><br/>{%s} %s"
                   path live instr_txt

  let vertex_attributes v = [
      `Shape `Box;
      `Fontname "monospace";
      `HtmlLabel (vertex_label v);
    ]
  let default_vertex_attributes _ = []

  let graph_attributes graph = [
      `Fontname "monospace";
    ]
end

module InstrDrawDot = Graph.Graphviz.Dot(InstrDot)

(* module for creating dot-files *)
module ImplicationDot = struct
  include ImplicationGraph

  let get_subgraph _ = None

  let formula_to_str (edge: ImplicationGraph.Edge.t) =
    let open ImplicationGraph.Edge in
    Ir.sexp_of_expr edge.formula |> Sexp.to_string

  let edge_attributes e = [
      `Label (E.label e |> formula_to_str);
      `Fontname "monospace"
    ]
  let default_edge_attributes _ = []

  let vertex_name (vertex: ImplicationGraph.V.t) =
    let open ImplicationGraph.Vertex in
    QID.as_path vertex.loc |> Printf.sprintf "\"%s\""

  let vertex_label (vertex: ImplicationGraph.V.t) =
    let open ImplicationGraph.Vertex in
    let path = QID.as_path vertex.loc in
    Printf.sprintf "<font color=\"grey\" point-size=\"10\">%s</font><br/>{%s}"
                   path (vertex.live |> String.concat ~sep:", ")

  let vertex_attributes v = [
      `Shape `Box;
      `Fontname "monospace";
      `HtmlLabel (vertex_label v);
    ]
  let default_vertex_attributes _ = []

  let graph_attributes graph = [
      `Fontname "monospace";
    ]
end

module ImplicationDrawDot = Graph.Graphviz.Dot(ImplicationDot)

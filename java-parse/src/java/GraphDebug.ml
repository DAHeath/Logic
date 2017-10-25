open Core

(* module for creating dot-files *)
module Dot = struct
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

  let vertex_name (qid, _) =
    QID.as_path qid |> Printf.sprintf "\"%s\""

  let vertex_label (qid, instr) =
    let instr_txt = JBir.print_instr ~show_type:false instr
                    |> String.substr_replace_all ~pattern:">" ~with_:"&gt;"
    in
    let path = QID.as_path qid in
    Printf.sprintf "<font color=\"grey\" point-size=\"10\">%s</font><br/>%s"
                   path instr_txt

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

module DrawDot = Graph.Graphviz.Dot(Dot)

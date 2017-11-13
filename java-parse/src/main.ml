module JProgram = Sawja_pack.JProgram
module JBir = Sawja_pack.JBir
module QID = QualifiedIdentity

open Core

(* Some Utility functions *)

let classpath file =
  let default_cp = [
    (Sys.getcwd ());
    (Filename.dirname file);
  ] in
  let with_env_vars = match (Sys.getenv "CLASSPATH") with
                          | Some env -> env :: default_cp
                          | None -> default_cp
  in
  String.concat ~sep:":" with_env_vars



let class_file =
  Command.Spec.Arg_type.create
    (fun filename ->
      let filename_with_ext =
        if String.is_suffix filename ~suffix:".class" then
          filename
        else
          filename ^ ".class"
      in
      match Sys.is_file filename_with_ext with
      | `Yes -> Filename.realpath filename
      | `No | `Unknown ->
         eprintf "'%s' is not a java class file.\n%!" filename;
         exit 1
    )


let collect_files_methods min files methods =
  if List.length files < min
  then failwith "Must provide at least two files! (-c)\n"
  else if List.length methods > List.length files
  then failwith "More methods than files specified!\n"
  else
    let methods_missing = max 0 (List.length files - List.length methods) in
    let methods = List.concat [
                      List.init methods_missing (fun _ -> None);
                      List.map ~f:(fun m -> Some m) methods
                    ]
    in
    List.zip_exn files methods

(* print out implication graph *)

let print_implication files methods output () =
  let parse (file, jmethod) = ParseJava.parse (classpath file) file jmethod in
  let serialize (graph, jmethod) =
    match output with
    | None ->
       let serialized = ImplicationGraph.serialize graph in
       Printf.printf "%s\n" serialized
    | Some out_path ->
       let () = Unix.mkdir_p out_path in
       let path = InstrGraph.cms_to_qid jmethod |> QID.to_string "-" in
       let file = Out_channel.create (Printf.sprintf "%s/%s.dot" out_path path) in
       GraphDebug.ImplicationDrawDot.output_graph file graph
  in

  collect_files_methods 1 files methods
  |> List.map ~f:parse
  |> List.map ~f:(fun (p, m, v) -> (InstrGraph.build_graph p m, m, v))
  |> List.map ~f:(fun (g, m, v) -> (g, m, InstrGraph.infer_bools v g))
  |> List.map ~f:(fun (g, m, v) -> (ImplicationGraph.to_implication g v, m))
  |> List.iter ~f:serialize


let print_implication_command =
  Command.basic
    ~summary:"Print out implication graph (in JSON) of many classes and methods."
    Command.Spec.(
    empty
    +> flag "-c" (listed class_file)
            ~doc:"class file to analyze (put before method name)."
    +> flag "-m" (listed string)
            ~doc:"method name in classfile to target."
    +> flag "-o" (optional string)
            ~doc:"output to dot instead of json and specify out folder."
  )
  print_implication

(* print out program graph *)

let print_dot files methods output () =
  let out_path = Option.value output ~default:"dot-out" in
  let () = Unix.mkdir_p out_path in

  let parse (file, jmethod) = ParseJava.parse (classpath file) file jmethod in
  let save_dot (graph, jmethod) =
    let path = InstrGraph.cms_to_qid jmethod |> QID.to_string "-" in
    let file = Out_channel.create (Printf.sprintf "%s/%s.dot" out_path path) in
    GraphDebug.InstrDrawDot.output_graph file graph
  in

  collect_files_methods 1 files methods
  |> List.map ~f:parse
  |> List.map ~f:(fun (p, m, _) -> (InstrGraph.build_graph p m), m)
  |> List.iter ~f:save_dot


let print_dot_command =
  Command.basic
    ~summary:"Print out dot file of many classes and methods."
    Command.Spec.(
    empty
    +> flag "-c" (listed class_file)
            ~doc:"class file to analyze (put before method name)."
    +> flag "-m" (listed string)
            ~doc:"method name in classfile to target."
    +> flag "-o" (optional string)
            ~doc:"output folder to write dot data to."
  )
  print_dot

(* Java bytecode html printing *)

let print_jbir class_file method_sig output () =
  let out_folder = Option.value output ~default:"jbir-html" in
  let () = Unix.mkdir_p out_folder in

  let (program, _, _) = ParseJava.parse (classpath class_file) class_file method_sig in
  let () = JBir.print_program program out_folder in
  Printf.printf "Wrote results to: '%s'.\n" out_folder


let print_jbir_command =
  Command.basic
    ~summary:"Print out the JBir representation of java bytecode."
    Command.Spec.(
    empty
    +> flag "-c" (required class_file)
            ~doc:"class file to print."
    +> flag "-m" (optional string)
            ~doc:"method name in class file to target."
    +> flag "-o" (optional string)
            ~doc:"output folder to write html to."
  )
    print_jbir

(* Main entry *)

let command =
  Command.group ~summary:"Verify equivalence of Java programs."
                [
                  "print-jbir", print_jbir_command;
                  "print-graph", print_dot_command;
                  "print-implication", print_implication_command;
                ]
let () = Command.run ~version:"0.1.0" command


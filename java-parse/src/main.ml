open Core

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
         exit 1)

let print_ir class_file method_sig () =
  let (program, m, _) = ParseJava.parse (classpath class_file) class_file method_sig in
  let program' = ToIr.program program m in
  Printf.printf "%s" (Ir.show_program program')

let print_ir_command =
  Command.basic
    ~summary:"Print out the unstructured representation of java bytecode."
    Command.Spec.(
    empty
    +> flag "-c" (required class_file)
            ~doc:"class file to print."
    +> flag "-m" (optional string)
            ~doc:"method name in class file to target.")
    print_ir

let command =
  Command.group ~summary:"Convert java programs to an unstructured representation."
                [
                  "print-ir", print_ir_command;
                ]
let () = Command.run ~version:"0.1.0" command

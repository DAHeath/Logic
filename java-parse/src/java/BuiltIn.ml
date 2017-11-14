module JBasics = Javalib_pack.JBasics

open Core

let is_built_in_class cn =
  let name = JBasics.cn_name cn in
     name = "java.util.Scanner"
  || name = "java.util.Properties"
  || name = "java.util.Arrays"
  || name = "java.util.ArrayList$SubList"
  || name = "java.util.Collections$UnmodifiableList"
  || name = "java.io.BufferedInputStream"
  || name = "java.lang.Boolean"
  || name = "java.lang.Integer"
  || name = "java.lang.Long"
  || name = "java.lang.System"
  || name = "java.lang.Object"
  || name = "java.lang.Class"
  || name = "java.lang.Math"
  || name = "java.lang.Throwable"
  || name = "sun.misc.VM"
  || String.is_substring name ~substring:"String"
  || String.is_substring name ~substring:"Error"
  || String.is_substring name ~substring:"Exception"

let built_in_list =
  [ "hasNextShort"
  ; "hasNextInt"
  ; "hasNextLong"
  ; "hasNextBigInteger"
  ; "hasNextFloat"
  ; "hasNextDouble"
  ; "hasNextBoolean"
  ; "nextBoolean"
  ; "nextShort"
  ; "nextInt"
  ; "nextLong"
  ; "nextBigInteger"
  ; "nextFloat"
  ; "nextDouble"
  ; "print"
  ; "println"
  ; "close"
  ; "flush"
  ; "getClass"
  ; "getComponentType"
  ; "desiredAssertionStatus"
  ; "getPrimitiveClass"
  ; "getSavedProperty"
  ; "outOfBoundsMsg"
  ; "floatToRawIntBits"
  ; "doubleToRawLongBits"
  ; "toString"
  ; "stringSize"
  ; "getChars"
  ; "checkForComodification"
  ; "newArray"
  ; "hugeCapacity"
  ; "copyOf"
  ]

let call_built_in_method cn ms v args =
  let mname = JBasics.ms_name ms in
  let cname = JBasics.cn_name cn in

  match (cname, mname, args) with
  | ("Wunderhorn", "ensure", [(q, _)]) -> Some (Ir.LBool true, Ir.Query q)
  | _ -> Printf.sprintf "Method %s.%s not supported." cname mname |> failwith

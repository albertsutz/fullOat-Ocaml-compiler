open Assert
open Ast

(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let fun_type_test : suite = [
  Test("subtype_fun", [
    "sub_subrfunt:positiv1", (fun () ->
      let tc = { Tctxt.empty with structs=[
        "B", [{fieldName="sutz1"; ftyp=TRef RString}];
        "A", [{fieldName="sutz1"; ftyp=TRef RString}; {fieldName="sutz2"; ftyp=TRef RString}];
      ]} in
      let funtyp1 = TRef (RFun ([TRef (RStruct "B")], RetVal (TRef (RStruct "A")))) in
      let funtyp2 = TRef (RFun ([TRef (RStruct "A")], RetVal (TRef (RStruct "B")))) in
      if Typechecker.subtype tc funtyp1 funtyp2
        then ()
        else failwith "function type error"
    );
    "sub_subrfunt:positive2", (fun () ->
      let tc = { Tctxt.empty with structs=[
        "B", [{fieldName="sutz2"; ftyp=TRef RString}];
        "A", [{fieldName="sutz1"; ftyp=TRef RString}; {fieldName="sutz2"; ftyp=TRef RString}];
      ]} in
      let funtyp1 = TRef (RFun ([TRef (RStruct "B")], RetVal (TRef (RStruct "A")))) in
      let funtyp2 = TRef (RFun ([TRef (RStruct "A")], RetVal (TRef (RStruct "B")))) in
      if Typechecker.subtype tc funtyp1 funtyp2
        then ()
        else failwith "function type error"
    );
    "sub_subrfunt:negativ1", (fun () ->
      let tc = { Tctxt.empty with structs=[
        "B", [{fieldName="sutz1"; ftyp=TRef RString}];
        "A", [{fieldName="sutz1"; ftyp=TRef RString}; {fieldName="sutz2"; ftyp=TRef RString}];
      ]} in
      let funtyp1 = TRef (RFun ([TRef (RStruct "A")], RetVal (TRef (RStruct "B")))) in
      let funtyp2 = TRef (RFun ([TRef (RStruct "B")], RetVal (TRef (RStruct "A")))) in
      if Typechecker.subtype tc funtyp1 funtyp2
        then failwith "function type error"
        else ()
    );
    "sub_subrfunt:negative2", (fun () ->
      let tc = { Tctxt.empty with structs=[
        "B", [{fieldName="sutz1"; ftyp=TInt}];
        "A", [{fieldName="sutz1"; ftyp=TRef RString}; {fieldName="sutz2"; ftyp=TRef RString}];
      ]} in
      let funtyp1 = TRef (RFun ([TRef (RStruct "B")], RetVal (TRef (RStruct "A")))) in
      let funtyp2 = TRef (RFun ([TRef (RStruct "A")], RetVal (TRef (RStruct "B")))) in
      if Typechecker.subtype tc funtyp1 funtyp2
        then failwith "function type error"
        else ()
    )
  ]);
]

let provided_tests : suite = fun_type_test
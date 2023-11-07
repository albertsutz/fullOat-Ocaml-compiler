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
    (* "sub_subrfunt:positive2", (fun () ->
      let tc = { Tctxt.empty with structs=[
        "B", [{fieldName="sutz2"; ftyp=TRef RString}];
        "A", [{fieldName="sutz1"; ftyp=TRef RString}; {fieldName="sutz2"; ftyp=TRef RString}];
      ]} in
      let funtyp1 = TRef (RFun ([TRef (RStruct "B")], RetVal (TRef (RStruct "A")))) in
      let funtyp2 = TRef (RFun ([TRef (RStruct "A")], RetVal (TRef (RStruct "B")))) in
      if Typechecker.subtype tc funtyp1 funtyp2
        then ()
        else failwith "function type error"
    ); *)
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
    (* "sub_subrfunt:negative2", (fun () ->
      let tc = { Tctxt.empty with structs=[
        "B", [{fieldName="sutz1"; ftyp=TInt}];
        "A", [{fieldName="sutz1"; ftyp=TRef RString}; {fieldName="sutz2"; ftyp=TRef RString}];
      ]} in
      let funtyp1 = TRef (RFun ([TRef (RStruct "B")], RetVal (TRef (RStruct "A")))) in
      let funtyp2 = TRef (RFun ([TRef (RStruct "A")], RetVal (TRef (RStruct "B")))) in
      if Typechecker.subtype tc funtyp1 funtyp2
        then failwith "function type error"
        else ()
    ) *)
  ]);
]

(* added 0 for return value *)
let oatyytoa_test : suite = [
  Test("Reversed a linked list", Gradedtests.executed_oat_file [
    ("oatyytoa.oat", "1 2 3 4 5", "5 4 3 2 1 0");
    ("oatyytoa.oat", "10 105 302 1212 12345 23123", "23123 12345 1212 302 105 10 0");
    ("oatyytoa.oat", "1212 2323 3434 4545", "4545 3434 2323 1212 0");
    ("oatyytoa.oat", "1", "1 0");
  ])
]

let struct_type_test : suite = [
  Test("subtype_struct", [
    "subtype_struct:positive", (fun () ->
      let tc = { Tctxt.empty with structs=[
        "SuperType", [{fieldName="a"; ftyp=TRef (RArray TInt) }; {fieldName="b"; ftyp= TBool }];
        "SubType", [{fieldName="a"; ftyp=TRef (RArray TInt) }; {fieldName="b"; ftyp= TBool }; {fieldName="c"; ftyp=TRef RString }];
      ]} in
      let str1 = TRef (RStruct "SubType") in
      let str2 = TRef (RStruct "SuperType") in
      if Typechecker.subtype tc str1 str2
        then ()
        else failwith "array subtype error"
    );
    "subtype_struct:negative", (fun () ->
      let tc = { Tctxt.empty with structs=[
        "SuperType", [{fieldName="a"; ftyp=TRef (RArray TInt) }; {fieldName="b"; ftyp= TBool }];
        "SubType", [{fieldName="a"; ftyp=TRef (RArray TInt) }; {fieldName="b"; ftyp= TBool }; {fieldName="c"; ftyp=TRef RString }];
      ]} in
      let str1 = TRef (RStruct "SubType") in
      let str2 = TRef (RStruct "SuperType") in
      if not (Typechecker.subtype tc str2 str1)
        then ()
        else failwith "array subtype error"
    );
  ]);
]

let provided_tests : suite = fun_type_test @ struct_type_test @ oatyytoa_test
  

open Ast
open Astlib
open Tctxt

(* Error Reporting ---------------------------------------------------------- *)
(* NOTE: Use type_error to report error messages for ill-typed programs. *)

exception TypeError of string

let type_error (l : 'a node) err = 
  let (_, (s, e), _) = l.loc in
  raise (TypeError (Printf.sprintf "[%d, %d] %s" s e err))


(* initial context: G0 ------------------------------------------------------ *)
(* The Oat types of the Oat built-in functions *)
let builtins =
  [ "array_of_string",  ([TRef RString],  RetVal (TRef(RArray TInt)))
  ; "string_of_array",  ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", ([TRef RString],  RetVal TInt)
  ; "string_of_int",    ([TInt], RetVal (TRef RString))
  ; "string_cat",       ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     ([TRef RString],  RetVoid)
  ; "print_int",        ([TInt], RetVoid)
  ; "print_bool",       ([TBool], RetVoid)
  ]

(* binary operation types --------------------------------------------------- *)
let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)
  | Eq | Neq -> failwith "typ_of_binop called on polymorphic == or !="

(* unary operation types ---------------------------------------------------- *)
let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* subtyping ---------------------------------------------------------------- *)
(* Decides whether H |- t1 <: t2 
    - assumes that H contains the declarations of all the possible struct types

    - you will want to introduce addition (possibly mutually recursive) 
      helper functions to implement the different judgments of the subtyping
      relation. We have included a template for subtype_ref to get you started.
      (Don't forget about OCaml's 'and' keyword.)
*)
let rec subtype (c : Tctxt.t) (t1 : Ast.ty) (t2 : Ast.ty) : bool =
  begin match (t1, t2) with
  | (TInt, TInt) -> true
  | (TBool, TBool) -> true
  | (TNullRef r1, TNullRef r2) | (TRef r1, TRef r2)| (TRef r1, TNullRef r2) -> (subtype_ref c r1 r2)
  | _ -> false
  end

(* Decides whether H |-r ref1 <: ref2 *)
and subtype_ref (c : Tctxt.t) (t1 : Ast.rty) (t2 : Ast.rty) : bool =
  begin match (t1, t2) with
  | (RString, RString) -> true
  | (RArray r1, RArray r2) -> r1 = r2
  | (RFun(l1, rt1), RFun(l2, rt2)) -> 
    let rec aux_func type_list_1 type_list_2 : bool = 
      begin match (type_list_1, type_list_2) with
      | (h1::t1, h2::t2) -> (subtype c h2 h1) && (aux_func t1 t2)
      | ([], []) -> true
      | _ -> false
      end in 
    (subtype_ret_t c rt1 rt2) && (aux_func l1 l2)
  | (RStruct r1, RStruct r2) -> 
    begin match (lookup_struct_option r1 c) with
    | Some (field_li) -> 
      let rec aux_func x : bool = 
        begin match x with
        | {fieldName; ftyp}::tail -> 
          begin match (lookup_field_option r2 fieldName c) with
          | Some field_2_type -> (ftyp = field_2_type) && (aux_func tail)
          | _ -> false
          end
        | [] -> true
        end
      in aux_func field_li
    | _ -> false
    end
  | _ -> false
  end

(* Decides whether H |-r ref1 <: ref2 *)
and subtype_ret_t (c : Tctxt.t) (ret_t1 : Ast.ret_ty) (ret_t2 : Ast.ret_ty) : bool = 
  begin match (ret_t1, ret_t2) with
  | (RetVoid, RetVoid) -> true
  | (RetVal r1, RetVal r2) -> (subtype c r1 r2)
  | _ -> false
  end


(* well-formed types -------------------------------------------------------- *)
(* Implement a (set of) functions that check that types are well formed according
   to the H |- t and related inference rules. Intuitively, this check can fail if an undefined reference appears as a component of `t`.

    - the function should succeed by returning () if the type is well-formed
      according to the rules

    - l is just an ast node that provides source location information for
      generating error messages (it's only needed for the type_error generation)

    - the function should fail using the "type_error" helper function if the 
      type is not well formed. Use `l` to indicate the location in the error.

    - tc contains the structure definition context
 *)
let rec typecheck_ty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ty) : unit =
  (match t with 
    | Ast.TBool | Ast.TInt -> ()
    | Ast.TRef ref | Ast.TNullRef ref->  typecheck_tref l tc ref
  )
and typecheck_tref (l : 'a Ast.node) (tc : Tctxt.t) (ref : Ast.rty) : unit = 
  (match ref with 
    | Ast.RString -> ()
    | Ast.RArray t -> typecheck_ty l tc t 
    | Ast.RStruct i -> 
      (match lookup_struct_option i tc with 
        | Some r -> ()
        | None -> failwith "type error"
      )
    | Ast.RFun (ts, rt) -> 
      ignore(List.map (typecheck_ty l tc) ts);
      (match rt with 
        | Ast.RetVoid -> ()
        | Ast.RetVal rtyp -> typecheck_ty l tc rtyp 
      )
  )



(* A helper function to determine whether a type allows the null value *)
let is_nullable_ty (t : Ast.ty) : bool =
  match t with
  | TNullRef _ -> true
  | _ -> false

(* typechecking expressions ------------------------------------------------- *)
(* Typechecks an expression in the typing context c, returns the type of the
   expression.  This function should implement the inference rules given in the
   oat.pdf specification.  There, they are written:

       H; G; L |- exp : t

   See tctxt.ml for the implementation of the context c, which represents the
   four typing contexts: H - for structure definitions G - for global
   identifiers L - for local identifiers

   Returns the (most precise) type for the expression, if it is type correct
   according to the inference rules.

   Uses the type_error function to indicate a (useful!) error message if the
   expression is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   Notes: - Structure values permit the programmer to write the fields in any
   order (compared with the structure definition).  This means that, given the
   declaration struct T { a:int; b:int; c:int } The expression new T {b=3; c=4;
   a=1} is well typed.  (You should sort the fields to compare them.)

*)
let rec typecheck_exp (c : Tctxt.t) (e : Ast.exp node) : Ast.ty =
  failwith "todo: implement typecheck_exp"

(* statements --------------------------------------------------------------- *)

(* Typecheck a statement 
   This function should implement the statment typechecking rules from oat.pdf.  

   Inputs:
    - tc: the type context
    - s: the statement node
    - to_ret: the desired return type (from the function declaration)

   Returns:
     - the new type context (which includes newly declared variables in scope
       after this statement)

     - A boolean indicating the return behavior of a statement:
        false:  might not return
        true:   definitely returns 

        in the branching statements, the return behavior of the branching 
        statement is the conjunction of the return behavior of the two 
        branches: both both branches must definitely return in order for 
        the whole statement to definitely return.

        Intuitively: if one of the two branches of a conditional does not 
        contain a return statement, then the entire conditional statement might 
        not return.
  
        looping constructs never definitely return 

   Uses the type_error function to indicate a (useful!) error message if the
   statement is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   - You will probably find it convenient to add a helper function that implements the 
     block typecheck rules.
*)
let rec typecheck_stmt (tc : Tctxt.t) (s:Ast.stmt node) (to_ret:ret_ty) : Tctxt.t * bool =
  failwith "todo: implement typecheck_stmt"


(* struct type declarations ------------------------------------------------- *)
(* Here is an example of how to implement the TYP_TDECLOK rule, which is 
   is needed elswhere in the type system.
 *)

(* Helper function to look for duplicate field names *)
let rec check_dups fs =
  match fs with
  | [] -> false
  | h :: t -> (List.exists (fun x -> x.fieldName = h.fieldName) t) || check_dups t

let typecheck_tdecl (tc : Tctxt.t) id fs  (l : 'a Ast.node) : unit =
  if check_dups fs
  then type_error l ("Repeated fields in " ^ id) 
  else List.iter (fun f -> typecheck_ty l tc f.ftyp) fs

(* function declarations ---------------------------------------------------- *)
(* typecheck a function declaration 
    - extends the local context with the types of the formal parameters to the 
      function
    - typechecks the body of the function (passing in the expected return type
    - checks that the function actually returns
*)

let typecheck_blk (tc : Tctxt.t) (blk : Ast.block) (to_ret:ret_ty) : Tctxt.t * bool =
  List.fold_left (
    fun (acc_tc, acc_ret_val) x -> 
      let stmt_tc, stmt_return = typecheck_stmt (acc_tc) (x) (to_ret) in 
      begin match (acc_ret_val, stmt_return) with
      | (true, true) -> type_error (no_loc blk) "double return in block error"
      | (false, false) -> (stmt_tc, false)
      | _ -> (stmt_tc, true)
      end
  ) (tc, false) (blk)

let distinct_id (ids: id list): bool = 
  let sorted_list = List.sort_uniq compare ids in 
  List.length sorted_list = List.length ids 

let create_context (tc : Tctxt.t) (f : Ast.fdecl): Tctxt.t = 
  let add_arg acc (ty, id) = add_local acc id ty in
  List.fold_left add_arg tc f.args 

let typecheck_fdecl (tc : Tctxt.t) (f : Ast.fdecl) (l : 'a Ast.node) : unit =
  let types, ids = List.split(f.args) in 
  let distinct = distinct_id ids in 
  let new_ctx = create_context tc f in 
  let _, returns = typecheck_blk new_ctx f.body f.frtyp in 
  
  if (distinct && returns) then () else failwith "type error" 

(* creating the typchecking context ----------------------------------------- *)

(* The following functions correspond to the
   judgments that create the global typechecking context.

   create_struct_ctxt: - adds all the struct types to the struct 'S'
   context (checking to see that there are no duplicate fields

     H |-s prog ==> H'


   create_function_ctxt: - adds the the function identifiers and their
   types to the 'G' context (ensuring that there are no redeclared
   function identifiers)

     H ; G1 |-f prog ==> G2


   create_global_ctxt: - typechecks the global initializers and adds
   their identifiers to the 'G' global context

     H ; G1 |-g prog ==> G2    


   NOTE: global initializers may mention function identifiers as
   constants, but can mention only other global values that were declared earlier
*)

let create_struct_ctxt (p:Ast.prog) : Tctxt.t =
  failwith "todo: create_struct_ctxt"

let create_function_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  failwith "todo: create_function_ctxt"

let create_global_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  failwith "todo: create_function_ctxt"


(* This function implements the |- prog and the H ; G |- prog 
   rules of the oat.pdf specification.   
*)
let typecheck_program (p:Ast.prog) : unit =
  let sc = create_struct_ctxt p in
  let fc = create_function_ctxt sc p in
  let tc = create_global_ctxt fc p in
  List.iter (fun p ->
    match p with
    | Gfdecl ({elt=f} as l) -> typecheck_fdecl tc f l
    | Gtdecl ({elt=(id, fs)} as l) -> typecheck_tdecl tc id fs l 
    | _ -> ()) p

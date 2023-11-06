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
  | (TInt, TInt) | (TBool, TBool) -> true
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
    begin match (lookup_struct_option r2 c) with
    | Some (field_li) -> 
      let rec aux_func x : bool = 
        begin match x with
        | {fieldName; ftyp}::tail -> 
          begin match (lookup_field_option r1 fieldName c) with
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

(* Decides whether H |-rt ref1 <: ref2 *)
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
        | Some _ -> ()
        | None -> type_error l "type error tref Rstruct"
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
  (match e.elt with 
    | CNull rt -> typecheck_tref e c rt; Ast.TNullRef rt
    | CBool _ -> Ast.TBool 
    | CInt _ -> Ast.TInt
    | CStr _ -> Ast.TRef (RString)
    | Id i -> typecheck_id e c i  
    | CArr (t, es) -> typecheck_carr c e t es
    | NewArr (t, e) -> typecheck_newarr c e t 
    | NewArrInit (t, e1, i, e2) -> 
      typecheck_ty e c t; 
      (match typecheck_exp c e1 with | TInt -> () | _ -> type_error e "type error new arr init"); 
      let local = lookup_local_option i c in 
      (match local with | Some _ -> type_error e "type error new arr init" | _ -> ()); 
      let new_ctxt = add_local c i t in 
      let nt = typecheck_exp new_ctxt e2 in 
      if subtype c nt t then TRef (RArray t) else type_error e "type error new arr init"
    | Index (e1, e2) -> 
      let t1 = typecheck_exp c e1 in 
      let t2 = typecheck_exp c e2 in 
      (match (t1, t2) with 
        | (TRef (RArray t), TInt) -> t 
        | _ ->  type_error e "Does not index an non-null Array"
      )
    | Length e -> 
      let t = typecheck_exp c e in 
      (match t with 
        | TRef _ -> TInt 
        | _ -> type_error e "type error length" 
      )
    | CStruct (i, fs) -> 
      let ids, es = List.split fs in 
      let types = List.map (typecheck_exp c) es in 
      let check_subtype_field (f, t) acc = 
        let t2 = (match lookup_field_option i f c with | Some t -> t | _ -> type_error e "type error Cstruct") in
        (subtype c t t2) && acc in 
      let id_types = List.combine ids types in 
      let valid = List.fold_right check_subtype_field id_types true in  
      if (valid) then TRef (RStruct i) else type_error e "type error Cstruct"
    | Proj (e, i) -> 
      let s = typecheck_exp c e in 
      let st_name = (match s with | TRef (RStruct id) -> id | _ -> type_error e "type error Proj") in 
      let field = lookup_field_option st_name i c in 
      (match field with 
        | Some t -> t 
        | _ -> type_error e "type error Proj" 
      )
    | Call (f, es) -> 
      let ts, rt = 
      (match typecheck_exp c f with 
        | TRef (RFun (ty_ls, ret)) -> (ty_ls, ret) 
        | _ -> type_error e "type error Call"
      ) in 
      let types = List.map (typecheck_exp c) es in 
      let eq_len = List.length es = List.length ts in 
      let combined_lst = 
        if (eq_len) then List.combine ts types else type_error e "type error Call" in 
      let subtype_and_acc (e1, e2) acc = (subtype c e1 e2) && acc in
      let valid_args = List.fold_right subtype_and_acc combined_lst true  in 
      let ret = (match rt with | RetVal typ -> typ | _ -> type_error e "type error Call") in 
      if (valid_args) then ret else type_error e "type error Call"
    | Bop (bop, e1, e2) -> 
      let t1 = typecheck_exp c e1 in 
      let t2 = typecheck_exp c e2 in  
      (match bop with 
        | Eq | Neq -> 
          let sub1 = subtype c t1 t2 in 
          let sub2 = subtype c t2 t1 in 
          if (sub1 && sub2) then TBool else type_error e "type error Bop" 
        | _ -> 
          let (t1', t2', rt) = typ_of_binop bop in 
          if (t1 = t1' && t2 = t2') then rt else type_error e "type error Bop"
      )
    | Uop (unop, e) -> 
      let t = typecheck_exp c e in 
      let (t', rt) = typ_of_unop unop in 
      if (t=t') then rt else type_error e "type error Uop"
  )

and typecheck_id (e: Ast.exp node) (c : Tctxt.t) (i: id) : Ast.ty = 
  let local = lookup_local_option i c in 
  let global = lookup_global_option i c in 
  (match (local, global) with 
    | (Some t, _) -> t 
    | (None, Some t) -> t 
    | _ -> type_error e "id is not declared within the scope"
  )
and typecheck_carr (c : Tctxt.t) (e: Ast.exp node) (t: ty) (es: exp node list): Ast.ty = 
  typecheck_ty e c t; 
  let types = List.map (typecheck_exp c) es in 
  let subtype_and_acc e acc = (subtype c e t) && acc in
  let valid = List.fold_right subtype_and_acc types true in 
  if (valid) then TRef (RArray t) else type_error e "type error Carr"
and typecheck_newarr (c : Tctxt.t) (e: Ast.exp node) (t: ty): Ast.ty = 
  typecheck_ty e c t; 
  (match typecheck_exp c e with | TInt -> () | _ -> type_error e "error Newarr"); 
  (match t with 
    | TInt | TBool | TNullRef _ -> ()
    | _ -> type_error e "error newArr"
  ); 
  TRef (RArray t) 



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
  begin match s.elt with
  | Assn (lhs, e) -> 
    let lhs_ty = typecheck_exp tc lhs in 
    (* lhs not a global function id *)
    begin match lhs.elt with
    | Id (id) -> 
      begin match (lookup_global_option id tc) with
      | Some(x) -> 
        begin match lhs_ty with 
        | TRef(RFun(_)) -> type_error s "assignment with global function id for lhs"
        | _ -> ()
        end
      | _ -> ()
      end
    | _ -> () 
    end;
    let e_ty = typecheck_exp tc e in 
    if (subtype tc e_ty lhs_ty) then (tc, false) 
    else type_error s "assignment rhs is not subtype of lhs"

  | Decl (v) -> 
    let v_id, v_exp = v in 
    begin match lookup_local_option v_id tc with
    | Some(x) -> type_error s "redeclaration of variable"
    | None -> 
        let v_type = typecheck_exp tc v_exp in 
        let new_tc = add_local tc v_id v_type in 
        (new_tc, false)
    end

  | Ret (e_option) -> 
    begin match e_option with
    | Some (e) -> 
      let ret_type = typecheck_exp tc e in 
      begin match to_ret with
      | RetVal (act_ret_to) -> if (subtype tc ret_type act_ret_to) then (tc, true)
        else type_error s "return expression type different from ret_to 1"
      | _ -> type_error s "return expression type different from ret_to 2"
      end
    | None -> if (to_ret = RetVoid) then (tc, true) else type_error s "return expression is None but ret_to isnt void"
    end

  | SCall (e, e_li) -> 
    let func_type = typecheck_exp tc e in 
    begin match func_type with
    | TRef(RFun(param_ty_li, RetVoid)) -> 
      let exp_li_type = List.map (fun x -> (typecheck_exp tc x)) e_li in 
      let rec aux_func param_ty_li exp_ty_li : bool = 
        begin match (param_ty_li, exp_ty_li) with
        | (par_ty::t1, exp_ty::t2) -> (subtype tc exp_ty par_ty) && (aux_func t1 t2)
        | ([], []) -> true
        | _ -> false
        end in
      if (aux_func param_ty_li exp_li_type) then (tc, false)
      else type_error s "scall params and expression different type"
    | _ -> type_error s "scall expression is not a function that returns void"
    end

  | If (if_exp, blk1, blk2) ->
    begin match (typecheck_exp tc if_exp) with
    | TBool -> 
      let _, ret_val_1 = typecheck_blk tc blk1 to_ret in 
      let _, ret_val_2 = typecheck_blk tc blk2 to_ret in 
      (tc, ret_val_1 && ret_val_2)
    | _ -> type_error s "if statement expression not boolean"
    end

  | Cast (ref, id, exp, blk1, blk2) -> 
    begin match (typecheck_exp tc exp) with
    | TNullRef x -> 
      if (subtype tc (TRef x) (TRef ref)) then
        let tc2 = add_local (tc) (id) (TRef ref) in 
        let _, ret_val_1 = typecheck_blk tc2 blk1 to_ret in 
        let _, ret_val_2 = typecheck_blk tc blk2 to_ret in 
        (tc, ret_val_1 && ret_val_2)
      else type_error s "expression type is not subtype of ref"
    | _ -> type_error s "expression for IFQ is not a trefnull"
    end


  | For (v_li, exp, stmt, blk) ->
    let tc2 = List.fold_left (
      fun acc x -> let new_tc, _ = (typecheck_stmt (acc) (no_loc (Decl x)) (to_ret)) in new_tc
    ) (tc) (v_li) in 
    let _ = begin match (exp) with
    | Some (e) -> if ((typecheck_exp tc2 e) = TBool) then () else type_error s "expression in for loop not boolean"
    | None -> ()
    end in 
    let _ = begin match (stmt) with
    | Some(s) -> ignore(typecheck_stmt tc2 s to_ret);
    | None -> ()
    end in 
    let _ = typecheck_blk tc2 blk to_ret in 
    (tc, false)

  | While (e, blk) -> 
    begin match (typecheck_exp tc e) with
    | TBool -> 
      ignore(typecheck_blk tc blk to_ret);
      (tc, false)
    | _ -> type_error s "condition in while loop is not a bool type"
    end
  end

and typecheck_blk (tc : Tctxt.t) (blk : Ast.block) (to_ret:ret_ty) : Tctxt.t * bool =
  List.fold_left (
    fun (acc_tc, acc_ret_val) x -> 
      let stmt_tc, stmt_return = typecheck_stmt (acc_tc) (x) (to_ret) in 
      begin match (acc_ret_val, stmt_return) with
      | (true, true) -> type_error (no_loc blk) "double return in block error"
      | (false, false) -> (stmt_tc, false)
      | _ -> (stmt_tc, true)
      end
  ) (tc, false) (blk)


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
  
  if (distinct && returns) then () else type_error l "type error fdecl" 

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
let check_dups_context ctxt : bool =
  let ids, _ = List.split(ctxt) in 
  not (distinct_id ids)

let create_initial_ctxt : Tctxt.t = 
  List.fold_left (
    fun acc (f_name, (fdecl_types, frtyp)) -> add_global (acc) (f_name) (TRef(RFun(fdecl_types, frtyp)))
  ) (empty) (builtins)

let create_struct_ctxt (p:Ast.prog) : Tctxt.t =
  let initial_ctxt = create_initial_ctxt in 
  let result = List.fold_left (
    fun acc x -> 
      begin match x with
      | Gtdecl (t) -> 
        let tdecl_id, tdecl_field_list = t.elt in 
        if (check_dups tdecl_field_list) then type_error t ("duplicate in fields of global struct" ^ tdecl_id)
        else add_struct acc tdecl_id tdecl_field_list
      | _ -> acc
      end
  ) (initial_ctxt) (p) in 
  if (check_dups_context result.structs) then type_error (no_loc p) "duplicate in structs context"
  else result

let create_function_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  let result = List.fold_left (
    fun acc x -> 
      begin match x with
      | Gfdecl (f) -> 
        let {frtyp;fname;args;_} = f.elt in 
          let fdecl_types, fdecl_ids = List.split args in 
          add_global (acc) (fname) (TRef(RFun(fdecl_types, frtyp)))
      | _ -> acc
      end
  ) (tc) (p) in
  if (check_dups_context result.globals) then type_error (no_loc p) "duplicate in global function context"
  else result

let create_global_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  let result = List.fold_left (
    fun acc x -> 
      begin match x with
      | Gvdecl (g) -> 
        let {name;init} = g.elt in 
        add_global (acc) (name) (typecheck_exp acc init)
      | _ -> acc
      end
  ) (tc) (p) in 
  if (check_dups_context result.globals) then type_error (no_loc p) "duplicate in global identifier context"
  else result




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

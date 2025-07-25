(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

%{
  open Why3
  open Ptree
  open Py_ast

  let () = Exn_printer.register (fun fmt exn -> match exn with
    | Error -> Format.pp_print_string fmt "syntax error"
    | _ -> raise exn)

  let py_floc s e = Loc.extract (s,e)
  let py_mk_id id s e = { id_str = id; id_ats = []; id_loc = py_floc s e }
  let py_mk_pat  d s e = { pat_desc  = d; pat_loc  = py_floc s e }
  let py_mk_expr loc d = { expr_desc = d; expr_loc = loc }
  let mk_stmt loc d = Dstmt { stmt_desc = d; stmt_loc = loc }
  let mk_var id = py_mk_expr id.id_loc (Eident id)

  let mk_ebinop loc o e1 e2 =
    match !Py_type.py_type_tbl with
    | None -> Ebinop (o, e1, e2)
    | Some tbl ->
        let (_fn,l1,c1,l2,c2) = Loc.get loc in
        let key = (l1,c1,l2,c2) in
        match Hashtbl.find_opt tbl key with
        | None -> Ebinop (o, e1, e2)
        | Some (op, arg_types, ret_type) ->
            (match o with
            | Badd -> assert (op = "+")
            | Bsub -> assert (op = "-")
            | Bmul -> assert (op = "*")
            | Bdiv -> assert (op = "//")
            | BdivR -> assert (op = "/")
            | _ -> ());
            let real_op =
              match o with
              | Badd -> BaddR
              | Bsub -> BsubR
              | Bmul -> BmulR
              | _ -> o
            in
            match arg_types, ret_type with
            | ["float"; "float"], "float" -> Ebinop (real_op, e1, e2)
            | ["float"; "int"], "float" -> Ebinop (real_op, e1, py_mk_expr e2.expr_loc (Eunop (Ufloat, e2)))
            | ["int"; "float"], "float" -> Ebinop (real_op, py_mk_expr e1.expr_loc (Eunop (Ufloat, e1)), e2)
            | _ -> Ebinop (o, e1, e2)

  let py_variant_union v1 v2 = match v1, v2 with
    | _, [] -> v1
    | [], _ -> v2
    | _, ({term_loc = loc},_)::_ -> Loc.errorm ~loc
        "multiple `variant' clauses are not allowed"

  let py_empty_spec = {
    sp_pre     = [];    sp_post    = [];  sp_xpost  = [];
    sp_reads   = [];    sp_writes  = [];  sp_alias  = [];
    sp_variant = [];
    sp_checkrw = false; sp_diverge = false; sp_partial = false;
  }

  let py_spec_union s1 s2 = {
    sp_pre     = s1.sp_pre @ s2.sp_pre;
    sp_post    = s1.sp_post @ s2.sp_post;
    sp_xpost   = s1.sp_xpost @ s2.sp_xpost;
    sp_reads   = s1.sp_reads @ s2.sp_reads;
    sp_writes  = s1.sp_writes @ s2.sp_writes;
    sp_alias   = s1.sp_alias @ s2.sp_alias;
    sp_variant = py_variant_union s1.sp_variant s2.sp_variant;
    sp_checkrw = s1.sp_checkrw || s2.sp_checkrw;
    sp_diverge = s1.sp_diverge || s2.sp_diverge;
    sp_partial = s1.sp_partial || s2.sp_partial;
  }

  let fresh_type_var =
    let r = ref 0 in
    fun loc -> incr r;
      PTtyvar { id_str = "a" ^ string_of_int !r; id_loc = loc; id_ats = [] }

  let logic_type loc = function
  | None    -> fresh_type_var loc
  | Some ty -> ty

  let logic_param loc (id, ty) = id, logic_type loc ty

%}

%token <string> PyINTEGER
%token <Py_ast.real> PyREAL
%token <string> PySTRING
%token <Py_ast.binop> PyCMP
%token <string> PyIDENT PyTVAR
%token PyDEF PyIF PyELSE PyELIF PyRETURN PyWHILE PyFOR PyIN PyAND PyOR PyNOT PyNONE PyTRUE PyFALSE PyPASS
%token PyFROM PyIMPORT PyBREAK PyCONTINUE
%token PyEOF
%token PyLEFTPAR PyRIGHTPAR PyLEFTSQ PyRIGHTSQ PyCOMMA PyEQUAL PyCOLON PyBEGIN PyEND PyNEWLINE
       PyPLUSEQUAL PyMINUSEQUAL PyTIMESEQUAL PyDIVEQUAL PyMODEQUAL
       PyLEFTBR PyRIGHTBR
%token PyPLUS PyMINUS PyTIMES PyDIV PyMOD
%token PyPLUSR PyMINUSR PyTIMESR PyDIVR
(* annotations *)
%token PyINVARIANT PyVARIANT PyASSUME PyASSERT PyCHECK PyREQUIRES PyENSURES PyLABEL
%token PyFUNCTION PyPREDICATE PyAXIOM PyLEMMA PyCONSTANT PyCALL
%token PyARROW PyDOT

(* precedences *)

%nonassoc PyELSE
%nonassoc PyIF
%right PyOR
%right PyAND
%nonassoc PyNOT
%right PyCMP
%left PyPLUS PyMINUS PyPLUSR PyMINUSR
%left PyTIMES PyDIV PyMOD PyTIMESR PyDIVR
%nonassoc py_unary_minus
%nonassoc PyLEFTSQ

%start py_file

%type <Py_ast.file> py_file
%type <Py_ast.decl> py_stmt

%start <unit> dummy

%%

py_file:
| PyNEWLINE* PyEOF
    { [] }
| PyNEWLINE? dl=nonempty_list(py_decl) PyNEWLINE? PyEOF
    { dl }
;

py_decl:
| py_import { $1 }
| py_def    { $1 }
| py_stmt   { $1 }
| py_func   { $1 }
| py_prop   { $1 }
| py_const  { $1 }

py_import:
| PyFROM m=py_ident PyIMPORT l=separated_list(PyCOMMA, py_ident) PyNEWLINE
  { Dimport (m, l) }

py_const:
| PyCONSTANT PyNEWLINE id = py_ident PyEQUAL e = py_expr PyNEWLINE
  { Dconst (id,e) }

py_prop:
| PyLEMMA id=py_ident PyCOLON t=term PyNEWLINE
  { Dprop (Decl.Plemma, id, t) }
| PyAXIOM id=py_ident PyCOLON t=term PyNEWLINE
  { Dprop (Decl.Paxiom, id, t) }

py_func:
| PyFUNCTION id=py_ident PyLEFTPAR l=separated_list(PyCOMMA, py_param) PyRIGHTPAR
  ty=option(py_function_type) var = option(py_fp_variant) py_def=option(py_logic_body)
  PyNEWLINE
  { let loc = py_floc $startpos $endpos in
    Dlogic (id, List.map (logic_param loc) l, Some (logic_type loc ty),
            var, py_def) }
| PyPREDICATE id=py_ident PyLEFTPAR l=separated_list(PyCOMMA, py_param) PyRIGHTPAR
  var=option(py_fp_variant) py_def=option(py_logic_body) PyNEWLINE
  { let loc = py_floc $startpos $endpos in
    Dlogic (id, List.map (logic_param loc) l, None, var, py_def) }

py_fp_variant:
| PyLEFTBR PyVARIANT v=term PyRIGHTBR { v }

py_logic_body:
| PyEQUAL t=term
  { t }

py_param:
| id=py_ident ty=option(py_param_type)
  { id, ty }

py_param_type:
| PyCOLON ty=py_typ
  { ty }

py_function_type:
| PyARROW ty=py_typ
  { ty }

/* Note: "list" is a legal type annotation in Python; we make it a
 * polymorphic type "list 'a" in WhyML  */
py_typ:
| id=py_type_var
  { PTtyvar id }
| id=py_ident
  { if id.id_str = "list"
    then PTtyapp (Qident id, [fresh_type_var (py_floc $startpos $endpos)])
    else if id.id_str = "float" then PTtyapp (Qident { id with id_str="real" }, [])
    else PTtyapp (Qident id, []) }
| id=py_ident PyLEFTSQ tyl=separated_nonempty_list(PyCOMMA, py_typ) PyRIGHTSQ
    {
      if id.id_str = "Tuple" then PTtuple tyl else PTtyapp (Qident id, tyl)
    }

py_def:
| fct = py_as_funct
  PyDEF f = py_ident PyLEFTPAR x = separated_list(PyCOMMA, py_param) PyRIGHTPAR
  ty=option(py_function_type) PyCOLON PyNEWLINE PyBEGIN s=py_spec l=py_body PyEND
    {
      if f.id_str = "range" then
        let loc = py_floc $startpos $endpos in
        Loc.errorm ~loc "micro Python does not allow shadowing 'range'"
      else if fct && ty = None then
        let loc = py_floc $startpos $endpos in
        Loc.errorm ~loc "a logical function should not return a unit type"
      else Ddef (f, x, ty, s, l ty s, fct)
    }
;

py_as_funct:
| PyFUNCTION PyNEWLINE { true  }
| (* epsilon *)    { false }
;

py_body:
| nonempty_list(py_stmt)
  { fun _ _ -> $1 }
| PyPASS PyNEWLINE
  { fun ty s -> [mk_stmt (py_floc $startpos $endpos) (Spass (ty, s))] }

py_spec:
| (* epsilon *)     { py_empty_spec }
| py_single_spec py_spec  { py_spec_union $1 $2 }

py_single_spec:
| PyREQUIRES t=term PyNEWLINE
    { { py_empty_spec with sp_pre = [t] } }
| PyENSURES e=py_ensures PyNEWLINE
    { { py_empty_spec with sp_post = [py_floc $startpos(e) $endpos(e), e] } }
| py_variant
    { { py_empty_spec with sp_variant = $1 } }

py_ensures:
| term
    { let id = py_mk_id "result" $startpos $endpos in
      [py_mk_pat (Pvar id) $startpos $endpos, $1] }
;

py_expr_dot:
| d = py_expr_dot_
   { py_mk_expr (py_floc $startpos $endpos) d }
;

py_expr_dot_:
| id = py_ident
    { Eident id }
| PyLEFTPAR e = py_expr PyRIGHTPAR
    { e.expr_desc }
;

py_expr:
| d = py_expr_desc
   { py_mk_expr (py_floc $startpos $endpos) d }
;

/*
py_expr_desc:
  e = py_expr_nt { e.py_expr_desc }
| e1 = py_expr_nt PyCOMMA el = separated_list(PyCOMMA, py_expr_nt)
    { Etuple (e1::el) }
;
*/
py_expr_desc:
  e = py_expr_nt_desc { e }
| e = py_expr_nt PyCOMMA el = separated_list(PyCOMMA, py_expr_nt) { Etuple (e::el) }
;

py_expr_nt:
| d = py_expr_nt_desc
   { py_mk_expr (py_floc $startpos $endpos) d }
;

py_expr_nt_desc:
| PyNONE
    { Enone }
| PyTRUE
    { Ebool true }
| PyFALSE
    { Ebool false }
| c = PyINTEGER
    { Eint c }
| c = PyREAL
    { Ereal c }
| s = PySTRING
    { Estring s }
| e1 = py_expr_nt PyLEFTSQ e2 = py_expr_nt PyRIGHTSQ
    { Eget (e1, e2) }
| e1 = py_expr_nt PyLEFTSQ e2=option(py_expr_nt) PyCOLON e3=option(py_expr_nt) PyRIGHTSQ
    {
      let f = py_mk_id "slice" $startpos $endpos in
      let none = py_mk_expr (py_floc $startpos $endpos) Enone in
      let e2, e3 = match e2, e3 with
        | None, None -> none, none
        | Some e, None -> e, none
        | None, Some e -> none, e
        | Some e, Some e' -> e, e'
      in
      Ecall(f,[e1;e2;e3])
    }
| PyMINUS e1 = py_expr_nt %prec py_unary_minus
    { Eunop (Uneg, e1) }
| PyNOT e1 = py_expr_nt
    { Eunop (Unot, e1) }
| e1 = py_expr_nt o = py_binop e2 = py_expr_nt
    { mk_ebinop (py_floc $startpos $endpos) o e1 e2 }
| e1 = py_expr_nt PyTIMES e2 = py_expr_nt
    { match e1.expr_desc with
      | Elist [e1] -> Emake (e1, e2)
      | _ -> mk_ebinop (py_floc $startpos $endpos) Bmul e1 e2 }
| e=py_expr_dot PyDOT f=py_ident PyLEFTPAR el=separated_list(PyCOMMA, py_expr_nt) PyRIGHTPAR
    {
      match f.id_str with
      | "pop" | "append" | "reverse" | "clear" | "copy" | "sort" ->
        Edot (e, f, el)
      | m -> let loc = py_floc $startpos $endpos in
             Loc.errorm ~loc "The method '%s' is not implemented" m
    }
| f = py_ident PyLEFTPAR e = separated_list(PyCOMMA, py_expr_nt) PyRIGHTPAR
    { Ecall (f, e) }
| PyLEFTSQ l = separated_list(PyCOMMA, py_expr_nt) PyRIGHTSQ
    { Elist l }
| e1=py_expr_nt PyIF c=py_expr_nt PyELSE e2=py_expr_nt
    { Econd(c,e1,e2) }
| e=py_expr_dot_
    { e }
;

%inline py_binop:
| PyPLUS  { Badd }
| PyMINUS { Bsub }
| PyDIV   { Bdiv }
| PyMOD   { Bmod }
| PyPLUSR  { BaddR }
| PyMINUSR  { BsubR }
| PyTIMESR  { BmulR }
| PyDIVR  { BdivR }
| c=PyCMP { c    }
| PyAND   { Band }
| PyOR    { Bor  }
;

py_located(X):
| X { mk_stmt (py_floc $startpos $endpos) $1 }
;

py_suite:
| s = py_simple_stmt PyNEWLINE
    { [s] }
| PyNEWLINE PyBEGIN l = nonempty_list(py_stmt) PyEND
    { l }
;

py_stmt:
| py_located(py_stmt_desc)      { $1 }
| s = py_simple_stmt PyNEWLINE { s }

py_stmt_desc:
| PyIF c = py_expr_nt PyCOLON s1 = py_suite s2=py_else_branch
    { Sif (c, s1, s2) }
| PyWHILE e = py_expr_nt PyCOLON b=py_loop_body
    { let i, v, l = b in Swhile (e, i, v, l) }
| PyFOR x = py_ident PyIN e = py_expr PyCOLON b=py_loop_body
    { let i, _, l = b in Sfor (x, e, i, l) }
;

py_else_branch:
| /* epsilon */
    { [] }
| PyELSE PyCOLON s2=py_suite
    { s2 }
| PyELIF c=py_expr_nt PyCOLON s1=py_suite s2=py_else_branch
    { [mk_stmt (py_floc $startpos $endpos) (Sif (c, s1, s2))] }


py_loop_body:
| s = py_simple_stmt PyNEWLINE
  { [], [], [s] }
| PyNEWLINE PyBEGIN a=py_loop_annotation l=nonempty_list(py_stmt) PyEND
  { fst a, snd a, l }

py_loop_annotation:
| (* epsilon *)
    { [], [] }
| py_invariant py_loop_annotation
    { let (i, v) = $2 in ($1::i, v) }
| py_variant py_loop_annotation
    { let (i, v) = $2 in (i, py_variant_union $1 v) }

py_invariant:
| PyINVARIANT i=term PyNEWLINE { i }

py_variant:
| PyVARIANT l=py_comma_list1(term) PyNEWLINE { List.map (fun t -> t, None) l }

py_simple_stmt: py_located(py_simple_stmt_desc) { $1 };

py_simple_stmt_desc:
| PyRETURN e = py_expr
    { Sreturn e }
| lhs = py_expr option(py_param_type) PyEQUAL rhs = py_expr { Sassign (lhs, rhs) }
| id=py_ident o=py_binop_equal e=py_expr_nt
    { let loc = py_floc $startpos $endpos in
      Sassign (mk_var id,
               py_mk_expr loc (Ebinop (o, py_mk_expr loc (Eident id), e))) }
| e0 = py_expr_nt PyLEFTSQ e1 = py_expr_nt PyRIGHTSQ o=py_binop_equal e2 = py_expr
    {
      let loc = py_floc $startpos $endpos in
      let mk_expr_floc = py_mk_expr loc in
      let id = py_mk_id "'i" $startpos $endpos in
      let expr_id = mk_expr_floc (Eident id) in
      let a = py_mk_id "'a" $startpos $endpos in
      let expr_a = mk_expr_floc (Eident a) in
      let operation =
        mk_expr_floc (Ebinop (o, mk_expr_floc (Eget(expr_a, expr_id)), e2)) in
      let s1 =
        Dstmt ({ stmt_desc = Sassign (mk_var a, e0); stmt_loc = loc }) in
      let s2 =
        Dstmt ({ stmt_desc = Sassign (mk_var id, e1); stmt_loc = loc }) in
      let s3 =
        Dstmt ({ stmt_desc = Sset (expr_a, expr_id, operation);
                 stmt_loc = loc }) in
      Sblock [s1; s2; s3]
    }
| k=py_assertion_kind t = term
    { Sassert (k, t) }
| e = py_expr
    { Seval e }
| PyCALL f = py_ident PyLEFTPAR e = separated_list(PyCOMMA, term) PyRIGHTPAR
    { Scall_lemma (f, e) }
| PyBREAK
    { Sbreak }
| PyCONTINUE
    { Scontinue }
| PyLABEL id=py_ident
    { Slabel id }
;

%inline py_binop_equal:
| PyPLUSEQUAL  { Badd }
| PyMINUSEQUAL { Bsub }
| PyDIVEQUAL   { Bdiv }
| PyTIMESEQUAL { Bmul }
| PyMODEQUAL   { Bmod }
;

py_assertion_kind:
| PyASSERT  { Expr.Assert }
| PyASSUME  { Expr.Assume }
| PyCHECK   { Expr.Check }

py_ident:
| id = PyIDENT { py_mk_id id $startpos $endpos }
;
py_type_var:
| id = PyTVAR { py_mk_id id $startpos $endpos }
;

py_comma_list1(X):
| separated_nonempty_list(PyCOMMA, X) { $1 }

/* silent Menhir's errors about unreachable non terminal symbols */

dummy:
| module_head_parsing_only scope_head_parsing_only dummy_decl* EOF
    { }

dummy_decl:
| meta_decl {}
| use_clone_parsing_only {}
| prog_decl {}
| pure_decl {}


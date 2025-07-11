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

  let floc s e = Loc.extract (s,e)
  let mk_id id s e = { id_str = id; id_ats = []; id_loc = floc s e }
  let mk_pat  d s e = { pat_desc  = d; pat_loc  = floc s e }
  let mk_term d s e = { term_desc = d; term_loc = floc s e }
  let mk_expr loc d = { expr_desc = d; expr_loc = loc }
  let mk_stmt loc d = Dstmt { stmt_desc = d; stmt_loc = loc }
  let mk_var id = mk_expr id.id_loc (Eident id)

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
            | ["float"; "int"], "float" -> Ebinop (real_op, e1, mk_expr e2.expr_loc (Eunop (Ufloat, e2)))
            | ["int"; "float"], "float" -> Ebinop (real_op, mk_expr e1.expr_loc (Eunop (Ufloat, e1)), e2)
            | _ -> Ebinop (o, e1, e2)

  let variant_union v1 v2 = match v1, v2 with
    | _, [] -> v1
    | [], _ -> v2
    | _, ({term_loc = loc},_)::_ -> Loc.errorm ~loc
        "multiple `variant' clauses are not allowed"

  let get_op s e = Qident (mk_id (Ident.op_get "") s e)
  let upd_op s e = Qident (mk_id (Ident.op_update "") s e)

  let empty_spec = {
    sp_pre     = [];    sp_post    = [];  sp_xpost  = [];
    sp_reads   = [];    sp_writes  = [];  sp_alias  = [];
    sp_variant = [];
    sp_checkrw = false; sp_diverge = false; sp_partial = false;
  }

  let spec_union s1 s2 = {
    sp_pre     = s1.sp_pre @ s2.sp_pre;
    sp_post    = s1.sp_post @ s2.sp_post;
    sp_xpost   = s1.sp_xpost @ s2.sp_xpost;
    sp_reads   = s1.sp_reads @ s2.sp_reads;
    sp_writes  = s1.sp_writes @ s2.sp_writes;
    sp_alias   = s1.sp_alias @ s2.sp_alias;
    sp_variant = variant_union s1.sp_variant s2.sp_variant;
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
%token <string> PyIDENT PyQIDENT PyTVAR
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
%token PyARROW PyLARROW PyLRARROW PyFORALL PyEXISTS PyDOT PyTHEN PyLET PyOLD PyAT PyBY PySO

(* precedences *)

%nonassoc PyIN
%nonassoc PyDOT PyELSE
%right PyARROW PyLRARROW PyBY PySO
%nonassoc PyIF
%right PyOR
%right PyAND
%nonassoc PyNOT
%right PyCMP
%left PyPLUS PyMINUS PyPLUSR PyMINUSR
%left PyTIMES PyDIV PyMOD PyTIMESR PyDIVR
%nonassoc unary_minus prec_prefix_op
%nonassoc PyLEFTSQ

%start file
(* Transformations entries *)
%start <Why3.Ptree.term> term_eof
%start <Why3.Ptree.term list> term_comma_list_eof
%start <Why3.Ptree.ident list> ident_comma_list_eof

%type <Py_ast.file> file
%type <Py_ast.decl> stmt

%%

file:
| PyNEWLINE* PyEOF
    { [] }
| PyNEWLINE? dl=nonempty_list(decl) PyNEWLINE? PyEOF
    { dl }
;

decl:
| import { $1 }
| def    { $1 }
| stmt   { $1 }
| func   { $1 }
| prop   { $1 }
| const  { $1 }

import:
| PyFROM m=ident PyIMPORT l=separated_list(PyCOMMA, ident) PyNEWLINE
  { Dimport (m, l) }

const:
| PyCONSTANT PyNEWLINE id = ident PyEQUAL e = expr PyNEWLINE
  { Dconst (id,e) }

prop:
| PyLEMMA id=ident PyCOLON t=term PyNEWLINE
  { Dprop (Decl.Plemma, id, t) }
| PyAXIOM id=ident PyCOLON t=term PyNEWLINE
  { Dprop (Decl.Paxiom, id, t) }

func:
| PyFUNCTION id=ident PyLEFTPAR l=separated_list(PyCOMMA, param) PyRIGHTPAR
  ty=option(function_type) var = option(fp_variant) def=option(logic_body)
  PyNEWLINE
  { let loc = floc $startpos $endpos in
    Dlogic (id, List.map (logic_param loc) l, Some (logic_type loc ty),
            var, def) }
| PyPREDICATE id=ident PyLEFTPAR l=separated_list(PyCOMMA, param) PyRIGHTPAR
  var=option(fp_variant) def=option(logic_body) PyNEWLINE
  { let loc = floc $startpos $endpos in
    Dlogic (id, List.map (logic_param loc) l, None, var, def) }

fp_variant:
| PyLEFTBR PyVARIANT v=term PyRIGHTBR { v }

logic_body:
| PyEQUAL t=term
  { t }

param:
| id=ident ty=option(param_type)
  { id, ty }

param_type:
| PyCOLON ty=typ
  { ty }

function_type:
| PyARROW ty=typ
  { ty }

/* Note: "list" is a legal type annotation in Python; we make it a
 * polymorphic type "list 'a" in WhyML  */
typ:
| id=type_var
  { PTtyvar id }
| id=ident
  { if id.id_str = "list"
    then PTtyapp (Qident id, [fresh_type_var (floc $startpos $endpos)])
    else if id.id_str = "float" then PTtyapp (Qident { id with id_str="real" }, [])
    else PTtyapp (Qident id, []) }
| id=ident PyLEFTSQ tyl=separated_nonempty_list(PyCOMMA, typ) PyRIGHTSQ
    {
      if id.id_str = "Tuple" then PTtuple tyl else PTtyapp (Qident id, tyl)
    }

def:
| fct = as_funct
  PyDEF f = ident PyLEFTPAR x = separated_list(PyCOMMA, param) PyRIGHTPAR
  ty=option(function_type) PyCOLON PyNEWLINE PyBEGIN s=spec l=body PyEND
    {
      if f.id_str = "range" then
        let loc = floc $startpos $endpos in
        Loc.errorm ~loc "micro Python does not allow shadowing 'range'"
      else if fct && ty = None then
        let loc = floc $startpos $endpos in
        Loc.errorm ~loc "a logical function should not return a unit type"
      else Ddef (f, x, ty, s, l ty s, fct)
    }
;

as_funct:
| PyFUNCTION PyNEWLINE { true  }
| (* epsilon *)    { false }
;

body:
| nonempty_list(stmt)
  { fun _ _ -> $1 }
| PyPASS PyNEWLINE
  { fun ty s -> [mk_stmt (floc $startpos $endpos) (Spass (ty, s))] }

spec:
| (* epsilon *)     { empty_spec }
| single_spec spec  { spec_union $1 $2 }

single_spec:
| PyREQUIRES t=term PyNEWLINE
    { { empty_spec with sp_pre = [t] } }
| PyENSURES e=ensures PyNEWLINE
    { { empty_spec with sp_post = [floc $startpos(e) $endpos(e), e] } }
| variant
    { { empty_spec with sp_variant = $1 } }

ensures:
| term
    { let id = mk_id "result" $startpos $endpos in
      [mk_pat (Pvar id) $startpos $endpos, $1] }
;

expr_dot:
| d = expr_dot_
   { mk_expr (floc $startpos $endpos) d }
;

expr_dot_:
| id = ident
    { Eident id }
| PyLEFTPAR e = expr PyRIGHTPAR
    { e.expr_desc }
;

expr:
| d = expr_desc
   { mk_expr (floc $startpos $endpos) d }
;

/*
expr_desc:
  e = expr_nt { e.expr_desc }
| e1 = expr_nt PyCOMMA el = separated_list(PyCOMMA, expr_nt)
    { Etuple (e1::el) }
;
*/
expr_desc:
  e = expr_nt_desc { e }
| e = expr_nt PyCOMMA el = separated_list(PyCOMMA, expr_nt) { Etuple (e::el) }
;

expr_nt:
| d = expr_nt_desc
   { mk_expr (floc $startpos $endpos) d }
;

expr_nt_desc:
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
| e1 = expr_nt PyLEFTSQ e2 = expr_nt PyRIGHTSQ
    { Eget (e1, e2) }
| e1 = expr_nt PyLEFTSQ e2=option(expr_nt) PyCOLON e3=option(expr_nt) PyRIGHTSQ
    {
      let f = mk_id "slice" $startpos $endpos in
      let none = mk_expr (floc $startpos $endpos) Enone in
      let e2, e3 = match e2, e3 with
        | None, None -> none, none
        | Some e, None -> e, none
        | None, Some e -> none, e
        | Some e, Some e' -> e, e'
      in
      Ecall(f,[e1;e2;e3])
    }
| PyMINUS e1 = expr_nt %prec unary_minus
    { Eunop (Uneg, e1) }
| PyNOT e1 = expr_nt
    { Eunop (Unot, e1) }
| e1 = expr_nt o = binop e2 = expr_nt
    { mk_ebinop (floc $startpos $endpos) o e1 e2 }
| e1 = expr_nt PyTIMES e2 = expr_nt
    { match e1.expr_desc with
      | Elist [e1] -> Emake (e1, e2)
      | _ -> mk_ebinop (floc $startpos $endpos) Bmul e1 e2 }
| e=expr_dot PyDOT f=ident PyLEFTPAR el=separated_list(PyCOMMA, expr_nt) PyRIGHTPAR
    {
      match f.id_str with
      | "pop" | "append" | "reverse" | "clear" | "copy" | "sort" ->
        Edot (e, f, el)
      | m -> let loc = floc $startpos $endpos in
             Loc.errorm ~loc "The method '%s' is not implemented" m
    }
| f = ident PyLEFTPAR e = separated_list(PyCOMMA, expr_nt) PyRIGHTPAR
    { Ecall (f, e) }
| PyLEFTSQ l = separated_list(PyCOMMA, expr_nt) PyRIGHTSQ
    { Elist l }
| e1=expr_nt PyIF c=expr_nt PyELSE e2=expr_nt
    { Econd(c,e1,e2) }
| e=expr_dot_
    { e }
;

%inline binop:
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

located(X):
| X { mk_stmt (floc $startpos $endpos) $1 }
;

suite:
| s = simple_stmt PyNEWLINE
    { [s] }
| PyNEWLINE PyBEGIN l = nonempty_list(stmt) PyEND
    { l }
;

stmt:
| located(stmt_desc)      { $1 }
| s = simple_stmt PyNEWLINE { s }

stmt_desc:
| PyIF c = expr_nt PyCOLON s1 = suite s2=else_branch
    { Sif (c, s1, s2) }
| PyWHILE e = expr_nt PyCOLON b=loop_body
    { let i, v, l = b in Swhile (e, i, v, l) }
| PyFOR x = ident PyIN e = expr PyCOLON b=loop_body
    { let i, _, l = b in Sfor (x, e, i, l) }
;

else_branch:
| /* epsilon */
    { [] }
| PyELSE PyCOLON s2=suite
    { s2 }
| PyELIF c=expr_nt PyCOLON s1=suite s2=else_branch
    { [mk_stmt (floc $startpos $endpos) (Sif (c, s1, s2))] }


loop_body:
| s = simple_stmt PyNEWLINE
  { [], [], [s] }
| PyNEWLINE PyBEGIN a=loop_annotation l=nonempty_list(stmt) PyEND
  { fst a, snd a, l }

loop_annotation:
| (* epsilon *)
    { [], [] }
| invariant loop_annotation
    { let (i, v) = $2 in ($1::i, v) }
| variant loop_annotation
    { let (i, v) = $2 in (i, variant_union $1 v) }

invariant:
| PyINVARIANT i=term PyNEWLINE { i }

variant:
| PyVARIANT l=comma_list1(term) PyNEWLINE { List.map (fun t -> t, None) l }

simple_stmt: located(simple_stmt_desc) { $1 };

simple_stmt_desc:
| PyRETURN e = expr
    { Sreturn e }
| lhs = expr option(param_type) PyEQUAL rhs = expr { Sassign (lhs, rhs) }
| id=ident o=binop_equal e=expr_nt
    { let loc = floc $startpos $endpos in
      Sassign (mk_var id,
               mk_expr loc (Ebinop (o, mk_expr loc (Eident id), e))) }
| e0 = expr_nt PyLEFTSQ e1 = expr_nt PyRIGHTSQ o=binop_equal e2 = expr
    {
      let loc = floc $startpos $endpos in
      let mk_expr_floc = mk_expr loc in
      let id = mk_id "'i" $startpos $endpos in
      let expr_id = mk_expr_floc (Eident id) in
      let a = mk_id "'a" $startpos $endpos in
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
| k=assertion_kind t = term
    { Sassert (k, t) }
| e = expr
    { Seval e }
| PyCALL f = ident PyLEFTPAR e = separated_list(PyCOMMA, term) PyRIGHTPAR
    { Scall_lemma (f, e) }
| PyBREAK
    { Sbreak }
| PyCONTINUE
    { Scontinue }
| PyLABEL id=ident
    { Slabel id }
;

%inline binop_equal:
| PyPLUSEQUAL  { Badd }
| PyMINUSEQUAL { Bsub }
| PyDIVEQUAL   { Bdiv }
| PyTIMESEQUAL { Bmul }
| PyMODEQUAL   { Bmod }
;

assertion_kind:
| PyASSERT  { Expr.Assert }
| PyASSUME  { Expr.Assume }
| PyCHECK   { Expr.Check }

ident:
| id = PyIDENT { mk_id id $startpos $endpos }
;
quote_ident:
| id = PyQIDENT { mk_id id $startpos $endpos }
;
type_var:
| id = PyTVAR { mk_id id $startpos $endpos }
;

/* logic */

mk_term(X): d = X { mk_term d $startpos $endpos }

term_tuple: t = mk_term(term_tuple_) { t }

term_tuple_:
| t = term ; PyCOMMA; lt=separated_list(PyCOMMA, term)
    { Ttuple (t::lt) }
| t = term_ { t }

term: t = mk_term(term_) { t }

term_:
| term_arg_
    { match $1 with (* break the infix relation chain *)
      | Tinfix (l,o,r) -> Tinnfix (l,o,r)
      | Tbinop (l,o,r) -> Tbinnop (l,o,r)
      | d -> d }
| PyNOT term
    { Tnot $2 }
| PyOLD PyLEFTPAR t=term PyRIGHTPAR
    { Tat (t, mk_id Dexpr.old_label $startpos($1) $endpos($1)) }
| PyAT PyLEFTPAR t=term PyCOMMA l=ident PyRIGHTPAR
    { Tat (t, l) }
| o = prefix_op ; t = term %prec prec_prefix_op
    { Tidapp (Qident o, [t]) }
| l = term ; o = bin_op ; r = term
    { Tbinop (l, o, r) }
| l = term ; o = infix_op_1 ; r = term
    { Tinfix (l, o, r) }
| l = term ; o = infix_op_234 ; r = term
    { Tidapp (Qident o, [l; r]) }
| PyIF term PyTHEN term PyELSE term
    { Tif ($2, $4, $6) }
| PyLET id=ident PyEQUAL t1=term PyIN t2=term
    { Tlet (id, t1, t2) }
| q=quant l=comma_list1(param) PyDOT t=term
    { let var (id, ty) = id.id_loc, Some id, false, ty in
      Tquant (q, List.map var l, [], t) }
| id=ident PyLEFTPAR l=separated_list(PyCOMMA, term) PyRIGHTPAR
    { Tidapp (Qident id, l) }

quant:
| PyFORALL  { Dterm.DTforall }
| PyEXISTS  { Dterm.DTexists }

term_arg: mk_term(term_arg_) { $1 }

term_arg_:
| quote_ident { Tident (Qident $1) }
| ident       { Tident (Qident $1) }
| PyINTEGER     { Tconst (Constant.ConstInt Number.(int_literal ILitDec ~neg:false $1)) }
| PyREAL        { Tconst (Constant.ConstReal Number.(real_literal ~radix:10 ~neg:false ~int:$1.intpart ~frac:$1.fracpart ~exp:$1.exppart)) }
| PyNONE        { Ttuple [] }
| PyTRUE        { Ttrue }
| PyFALSE       { Tfalse }
| term_sub_                 { $1 }

term_sub_:
| PyLEFTPAR term_tuple PyRIGHTPAR                             { $2.term_desc }
| term_arg PyLEFTSQ term PyRIGHTSQ
    { Tidapp (get_op $startpos($2) $endpos($2), [$1;$3]) }
| term_arg PyLEFTSQ term PyLARROW term PyRIGHTSQ
    { Tidapp (upd_op $startpos($2) $endpos($2), [$1;$3;$5]) }
| e1 = term_arg PyLEFTSQ e2=option(term) PyCOLON e3=option(term) PyRIGHTSQ
    {
      let slice = mk_id "slice" $startpos $endpos in
      let len = mk_id "len" $startpos $endpos in
      let z = Tconst (Constant.int_const_of_int 0) in
      let l = Tidapp(Qident len, [e1]) in
      let z = mk_term z $startpos $endpos in
      let l = mk_term l $startpos $endpos in
      let e2, e3 = match e2, e3 with
        | None, None -> z, l
        | Some e, None -> e, l
        | None, Some e -> z, e
        | Some e, Some e' -> e, e'
      in
      Tidapp(Qident slice,[e1;e2;e3])
    }

%inline bin_op:
| PyARROW   { Dterm.DTimplies }
| PyLRARROW { Dterm.DTiff }
| PyOR      { Dterm.DTor }
| PyAND     { Dterm.DTand }
| PyBY      { Dterm.DTby }
| PySO      { Dterm.DTso }

%inline infix_op_1:
| c=PyCMP  { let op = match c with
          | Beq  -> "="
          | Bneq -> "<>"
          | Blt  -> "<"
          | Ble  -> "<="
          | Bgt  -> ">"
          | Bge  -> ">="
          | Badd|Bsub|Bmul|Bdiv|Bmod|BaddR|BsubR|BmulR|BdivR|Band|Bor -> assert false in
           mk_id (Ident.op_infix op) $startpos $endpos }

%inline prefix_op:
| PyMINUS { mk_id (Ident.op_prefix "-")  $startpos $endpos }

%inline infix_op_234:
| PyDIV    { mk_id (Ident.op_infix "//") $startpos $endpos }
| PyMOD    { mk_id (Ident.op_infix "%") $startpos $endpos }
| PyPLUS   { mk_id (Ident.op_infix "+") $startpos $endpos }
| PyMINUS  { mk_id (Ident.op_infix "-") $startpos $endpos }
| PyTIMES  { mk_id (Ident.op_infix "*") $startpos $endpos }
| PyPLUSR  { mk_id (Ident.op_infix "+.") $startpos $endpos }
| PyMINUSR { mk_id (Ident.op_infix "-.") $startpos $endpos }
| PyTIMESR { mk_id (Ident.op_infix "*.") $startpos $endpos }
| PyDIVR   { mk_id (Ident.op_infix "/.") $startpos $endpos }

comma_list1(X):
| separated_nonempty_list(PyCOMMA, X) { $1 }

(* Parsing of a list of qualified identifiers for the ITP *)

(* parsing of a single term *)

term_eof:
| term PyNEWLINE PyEOF { $1 }

ident_comma_list_eof:
| comma_list1(ident) PyNEWLINE PyEOF { $1 }

term_comma_list_eof:
| comma_list1(term) PyNEWLINE PyEOF { $1 }
(* we use single_term to avoid conflict with tuples, that
   do not need parentheses *)

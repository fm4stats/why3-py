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

{
  open Lexing
  open Py_ast
  open Py_parser

  exception Lexing_error of string

  let () = Why3.Exn_printer.register (fun fmt exn -> match exn with
  | Lexing_error s -> Format.fprintf fmt "syntax error: %s" s
  | _ -> raise exn)

  let id_or_kwd =
    let h = Hashtbl.create 32 in
    List.iter (fun (s, tok) -> Hashtbl.add h s tok)
      ["def", PyDEF; "if", PyIF; "else", PyELSE; "elif", PyELIF;
       "return", PyRETURN; "while", PyWHILE; "pass", PyPASS;
       "for", PyFOR; "in", PyIN;
       "and", PyAND; "or", PyOR; "not", PyNOT;
       "True", PyTRUE; "False", PyFALSE; "None", PyNONE;
       "from", PyFROM; "import", PyIMPORT; "break", PyBREAK; "continue", PyCONTINUE;
       (* annotations *)
       "variant", PyVARIANT; "call", PyCALL;
      ];
   fun s -> try Hashtbl.find h s with Not_found -> PyIDENT s

  let annotation =
    let h = Hashtbl.create 32 in
    List.iter (fun (s, tok) -> Hashtbl.add h s tok)
      ["invariant", PyINVARIANT; "variant", PyVARIANT;
       "assert", PyASSERT; "assume", PyASSUME; "check", PyCHECK;
       "requires", PyREQUIRES; "ensures", PyENSURES;
       "axiom", PyAXIOM; "lemma", PyLEMMA; "call", PyCALL; "constant", PyCONSTANT;
       "label", PyLABEL; "function", PyFUNCTION; "predicate", PyPREDICATE;
      ];
    fun s -> try Hashtbl.find h s with Not_found ->
      raise (Lexing_error ("no such annotation '" ^ s ^ "'"))

  let string_buffer = Buffer.create 1024

  let stack = ref [0]  (* indentation stack *)

  let rec unindent n = match !stack with
    | m :: _ when m = n -> []
    | m :: st when m > n -> stack := st; PyEND :: unindent n
    | _ -> raise (Lexing_error "bad indentation")

  let update_stack n =
    match !stack with
    | m :: _ when m < n ->
      stack := n :: !stack;
      [PyNEWLINE; PyBEGIN]
    | _ ->
      PyNEWLINE :: unindent n

}

let letter = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let digitpart = digit ('_'? digit)*
let ident = (letter | '_')+ (letter | digit | '_')*
let integer = ['0'-'9']+
let space = ' ' | '\t'
let comment = "#" [^'@''\n'] [^'\n']*

rule next_tokens = parse
  | '\n' | "#\n"
            { new_line lexbuf; update_stack (indentation lexbuf) }
  | space+ | comment
            { next_tokens lexbuf }
  | "\\" space* '\n' space* "#@"?
            { next_tokens lexbuf }
  | "#@" space* (ident as id)
            { [annotation id] }
  | "#@"    { raise (Lexing_error "expecting an annotation") }
  | ident as id
            { [id_or_kwd id] }
  | "'" (ident as id)
            { [PyTVAR id] }
  | '+'     { [PyPLUS] }
  | "+="    { [PyPLUSEQUAL] }
  | "-="    { [PyMINUSEQUAL] }
  | "*="    { [PyTIMESEQUAL] }
  | "//="   { [PyDIVEQUAL] }
  | "%="    { [PyMODEQUAL] }
  | '-'     { [PyMINUS] }
  | '*'     { [PyTIMES] }
  | "//"    { [PyDIV] }
  | '%'     { [PyMOD] }
  | "+."    { [PyPLUSR] }
  | "-."    { [PyMINUSR] }
  | "*."    { [PyTIMESR] }
  | "/"     { [PyDIVR] }
  | '='     { [PyEQUAL] }
  | "=="    { [PyCMP Beq] }
  | "!="    { [PyCMP Bneq] }
  | "<"     { [PyCMP Blt] }
  | "<="    { [PyCMP Ble] }
  | ">"     { [PyCMP Bgt] }
  | ">="    { [PyCMP Bge] }
  | '('     { [PyLEFTPAR] }
  | ')'     { [PyRIGHTPAR] }
  | '['     { [PyLEFTSQ] }
  | ']'     { [PyRIGHTSQ] }
  | '{'     { [PyLEFTBR] }
  | '}'     { [PyRIGHTBR] }
  | ','     { [PyCOMMA] }
  | ':'     { [PyCOLON] }
  (* logic symbols *)
  | "->"    { [PyARROW] }
  | "."     { [PyDOT] }
  | integer as s
            { [PyINTEGER s] }
  | ( (digitpart as i) ("" as f)
    | (digitpart as i) '.' ("" as f)
    | ("" as i) '.' (digitpart as f)
    | (digitpart as i) '.' (digitpart as f) )
    (['e' 'E'] (['-' '+']? digitpart as e))?
            { [PyREAL {
                intpart=(Why3.Lexlib.remove_underscores i);
                fracpart=(Why3.Lexlib.remove_underscores f);
                exppart=(Option.map (fun s -> Why3.Lexlib.remove_leading_plus (Why3.Lexlib.remove_underscores s)) e)}] }
  | '"'     { [PySTRING (string lexbuf)] }
  | eof     { PyNEWLINE :: unindent 0 @ [PyEOF] }
  | _ as c  { raise (Lexing_error ("illegal character: " ^ String.make 1 c)) }

(* count the indentation, i.e. the number of space characters from bol *)
and indentation = parse
  | (space+ | comment | '#')* '\n'
      (* skip empty lines *)
      { new_line lexbuf; indentation lexbuf }
  | space* as s
      { String.length s }

and string = parse
  | '"'
      { let s = Buffer.contents string_buffer in
	Buffer.reset string_buffer;
	s }
  | "\\n"
      { Buffer.add_char string_buffer '\n';
	string lexbuf }
  | "\\\""
      { Buffer.add_char string_buffer '"';
	string lexbuf }
  | _ as c
      { Buffer.add_char string_buffer c;
	string lexbuf }
  | eof
      { raise (Lexing_error "unterminated string") }

{

  let py_tokens = Queue.create ()

  let py_next_token =
    fun lb ->
      if Queue.is_empty py_tokens then begin
	let l = next_tokens lb in
	List.iter (fun t -> Queue.add t py_tokens) l
      end;
      Queue.pop py_tokens

  let quote_bytes bs =
    let buf = Buffer.create 0 in
    Buffer.add_char buf '"';
    for i = 0 to (Bytes.length bs - 1) do
      let ch = Bytes.get bs i in
      Buffer.add_string buf (Char.escaped ch)
    done;
    Buffer.add_char buf '"';
    Buffer.contents buf

  let string_of_token tok =
    match tok with
    | ABSTRACT -> "ABSTRACT"
    | ABSURD -> "ABSURD"
    | ALIAS -> "ALIAS"
    | AMP -> "AMP"
    | AMPAMP -> "AMPAMP"
    | AND -> "AND"
    | ANY -> "ANY"
    | ARROW -> "ARROW"
    | AS -> "AS"
    | ASSERT -> "ASSERT"
    | ASSUME -> "ASSUME"
    | AT -> "AT"
    | ATTRIBUTE _ -> "ATTRIBUTE"
    | AXIOM -> "AXIOM"
    | BAR -> "BAR"
    | BARBAR -> "BARBAR"
    | BARRIGHTSQ -> "BARRIGHTSQ"
    | BEGIN -> "BEGIN"
    | BREAK -> "BREAK"
    | BY -> "BY"
    | CHECK -> "CHECK"
    | CLONE -> "CLONE"
    | COINDUCTIVE -> "COINDUCTIVE"
    | COLON -> "COLON"
    | COMMA -> "COMMA"
    | CONSTANT -> "CONSTANT"
    | CONTINUE -> "CONTINUE"
    | CORE_LIDENT _ -> "CORE_LIDENT"
    | CORE_UIDENT _ -> "CORE_UIDENT"
    | DIVERGES -> "DIVERGES"
    | DO -> "DO"
    | DONE -> "DONE"
    | DOT -> "DOT"
    | DOTDOT -> "DOTDOT"
    | DOWNTO -> "DOWNTO"
    | ELSE -> "ELSE"
    | END -> "END"
    | ENSURES -> "ENSURES"
    | EOF -> "EOF"
    | EPSILON -> "EPSILON"
    | EQUAL -> "EQUAL"
    | EQUALARROW -> "EQUALARROW"
    | EXCEPTION -> "EXCEPTION"
    | EXISTS -> "EXISTS"
    | EXPORT -> "EXPORT"
    | FALSE -> "FALSE"
    | FLOAT -> "FLOAT"
    | FOR -> "FOR"
    | FORALL -> "FORALL"
    | FUN -> "FUN"
    | FUNCTION -> "FUNCTION"
    | GHOST -> "GHOST"
    | GOAL -> "GOAL"
    | GT -> "GT"
    | IF -> "IF"
    | IMPORT -> "IMPORT"
    | IN -> "IN"
    | INDUCTIVE -> "INDUCTIVE"
    | INTEGER _ -> "INTEGER"
    | INVARIANT -> "INVARIANT"
    | LABEL -> "LABEL"
    | LARROW -> "LARROW"
    | LEFTBRC -> "LEFTBRC"
    | LEFTPAR -> "LEFTPAR"
    | LEFTSQ -> "LEFTSQ"
    | LEFTSQBAR -> "LEFTSQBAR"
    | LEMMA -> "LEMMA"
    | LET -> "LET"
    | LIDENT _ -> "LIDENT"
    | LRARROW -> "LRARROW"
    | LT -> "LT"
    | LTGT -> "LTGT"
    | MATCH -> "MATCH"
    | META -> "META"
    | MINUS -> "MINUS"
    | MODULE -> "MODULE"
    | MUTABLE -> "MUTABLE"
    | NOT -> "NOT"
    | OLD -> "OLD"
    | OP1 _ -> "OP1"
    | OP2 _ -> "OP2"
    | OP3 _ -> "OP3"
    | OP4 _ -> "OP4"
    | OPPREF _ -> "OPPREF"
    | OR -> "OR"
    | PARTIAL -> "PARTIAL"
    | POSITION _ -> "POSITION"
    | PREDICATE -> "PREDICATE"
    | PRIVATE -> "PRIVATE"
    | PURE -> "PURE"
    | QUOTE_LIDENT _ -> "QUOTE_LIDENT"
    | RAISE -> "RAISE"
    | RAISES -> "RAISES"
    | RANGE -> "RANGE"
    | READS -> "READS"
    | REAL _ -> "REAL"
    | REC -> "REC"
    | REF -> "REF"
    | REQUIRES -> "REQUIRES"
    | RETURN -> "RETURN"
    | RETURNS -> "RETURNS"
    | RIGHTBRC -> "RIGHTBRC"
    | RIGHTPAR -> "RIGHTPAR"
    | RIGHTPAR_QUOTE _ -> "RIGHTPAR_QUOTE"
    | RIGHTPAR_USCORE _ -> "RIGHTPAR_USCORE"
    | RIGHTSQ -> "RIGHTSQ"
    | RIGHTSQ_QUOTE _ -> "RIGHTSQ_QUOTE"
    | SCOPE -> "SCOPE"
    | SEMICOLON -> "SEMICOLON"
    | SO -> "SO"
    | STRING _ -> "STRING"
    | THEN -> "THEN"
    | THEORY -> "THEORY"
    | TO -> "TO"
    | TRUE -> "TRUE"
    | TRY -> "TRY"
    | TYPE -> "TYPE"
    | UIDENT _ -> "UIDENT"
    | UNDERSCORE -> "UNDERSCORE"
    | USE -> "USE"
    | VAL -> "VAL"
    | VARIANT -> "VARIANT"
    | WHILE -> "WHILE"
    | WITH -> "WITH"
    | WRITES -> "WRITES"
    | PyAND -> "PyAND"
    | PyARROW -> "PyARROW"
    | PyASSERT -> "PyASSERT"
    | PyASSUME -> "PyASSUME"
    | PyAXIOM -> "PyAXIOM"
    | PyBEGIN -> "PyBEGIN"
    | PyBREAK -> "PyBREAK"
    | PyCALL -> "PyCALL"
    | PyCHECK -> "PyCHECK"
    | PyCMP _ -> "PyCMP"
    | PyCOLON -> "PyCOLON"
    | PyCOMMA -> "PyCOMMA"
    | PyCONSTANT -> "PyCONSTANT"
    | PyCONTINUE -> "PyCONTINUE"
    | PyDEF -> "PyDEF"
    | PyDIV -> "PyDIV"
    | PyDIVEQUAL -> "PyDIVEQUAL"
    | PyDIVR -> "PyDIVR"
    | PyDOT -> "PyDOT"
    | PyELIF -> "PyELIF"
    | PyELSE -> "PyELSE"
    | PyEND -> "PyEND"
    | PyENSURES -> "PyENSURES"
    | PyEOF -> "PyEOF"
    | PyEQUAL -> "PyEQUAL"
    | PyFALSE -> "PyFALSE"
    | PyFOR -> "PyFOR"
    | PyFROM -> "PyFROM"
    | PyFUNCTION -> "PyFUNCTION"
    | PyIDENT _ -> "PyIDENT"
    | PyIF -> "PyIF"
    | PyIMPORT -> "PyIMPORT"
    | PyIN -> "PyIN"
    | PyINTEGER _ -> "PyINTEGER"
    | PyINVARIANT -> "PyINVARIANT"
    | PyLABEL -> "PyLABEL"
    | PyLEFTBR -> "PyLEFTBR"
    | PyLEFTPAR -> "PyLEFTPAR"
    | PyLEFTSQ -> "PyLEFTSQ"
    | PyLEMMA -> "PyLEMMA"
    | PyMINUS -> "PyMINUS"
    | PyMINUSEQUAL -> "PyMINUSEQUAL"
    | PyMINUSR -> "PyMINUSR"
    | PyMOD -> "PyMOD"
    | PyMODEQUAL -> "PyMODEQUAL"
    | PyNEWLINE -> "PyNEWLINE"
    | PyNONE -> "PyNONE"
    | PyNOT -> "PyNOT"
    | PyOR -> "PyOR"
    | PyPASS -> "PyPASS"
    | PyPLUS -> "PyPLUS"
    | PyPLUSEQUAL -> "PyPLUSEQUAL"
    | PyPLUSR -> "PyPLUSR"
    | PyPREDICATE -> "PyPREDICATE"
    | PyREAL _ -> "PyREAL"
    | PyREQUIRES -> "PyREQUIRES"
    | PyRETURN -> "PyRETURN"
    | PyRIGHTBR -> "PyRIGHTBR"
    | PyRIGHTPAR -> "PyRIGHTPAR"
    | PyRIGHTSQ -> "PyRIGHTSQ"
    | PySTRING _ -> "PySTRING"
    | PyTIMES -> "PyTIMES"
    | PyTIMESEQUAL -> "PyTIMESEQUAL"
    | PyTIMESR -> "PyTIMESR"
    | PyTRUE -> "PyTRUE"
    | PyTVAR _ -> "PyTVAR"
    | PyVARIANT -> "PyVARIANT"
    | PyWHILE -> "PyWHILE"

  let print_token (prefix : string) (tok : Py_parser.token) (lb : Lexing.lexbuf) (pos1 : Lexing.position) (pos2 : Lexing.position) : unit =
    print_endline (prefix ^
                   "(" ^
                   string_of_int pos1.pos_lnum ^
                   ":" ^
                   string_of_int (pos1.pos_cnum - pos1.pos_bol) ^
                   "-" ^
                   string_of_int pos2.pos_lnum ^
                   ":" ^
                   string_of_int (pos2.pos_cnum - pos2.pos_bol) ^
                   " " ^
                   string_of_token tok ^
                   " " ^
                   quote_bytes (Bytes.sub lb.lex_buffer pos1.pos_cnum (pos2.pos_cnum-pos1.pos_cnum)) ^
                   ")" )

  let _ = ignore print_token
  let print_token (prefix : string) (tok : Py_parser.token) (lb : Lexing.lexbuf) (pos1 : Lexing.position) (pos2 : Lexing.position) : unit = ignore (prefix, tok, lb, pos1, pos2)

  let loop lb =
    let module I = Py_parser.MenhirInterpreter in
    let rec loop lb checkpoint =
      match checkpoint with
      | I.InputNeeded _ ->
        if not (Queue.is_empty py_tokens) then
          let pos1 = lb.lex_curr_p in
          let tok = py_next_token lb in
          let pos2 = lb.lex_curr_p in
          print_token "python-token" tok lb pos1 pos2;
          let checkpoint = I.offer checkpoint (tok, pos1, pos2) in
          loop lb checkpoint
        else
          let lb' = { lb with lex_mem = [||] } in
          let pos1 = lb.lex_curr_p in
          let tok_or_err =
            try
              Either.Left (py_next_token lb)
            with Lexing_error _ as exc ->
              Either.Right exc
          in
          let pos2 = lb.lex_curr_p in
          (match tok_or_err with
          | Either.Left tok when I.acceptable checkpoint tok pos1 ->
              (print_token "python-token" tok lb pos1 pos2;
              let checkpoint = I.offer checkpoint (tok, pos1, pos2) in
              loop lb checkpoint)
          | _ ->
              (let pos1 = lb'.lex_curr_p in
              let tok = Py_whylexer.token lb' in
              let pos2 = lb'.lex_curr_p in
              let triple = (tok, pos1, pos2) in
              print_token "whyml-token" tok lb pos1 pos2;
              let checkpoint = I.offer checkpoint triple in
              loop lb' checkpoint))
      | I.Shifting _
      | I.AboutToReduce _
      | I.HandlingError _ ->
          let checkpoint = I.resume ~strategy:`Legacy checkpoint in
          loop lb checkpoint
      | I.Accepted v ->
          v
      | I.Rejected ->
          raise Error
    in
    loop lb

  let parse_file lb =
    let checkpoint = Py_parser.Incremental.py_file lb.lex_curr_p in
    loop lb checkpoint

  let input_all c =
    let len = in_channel_length c in
    really_input_string c len

  let parse file c =
    let content = input_all c in
    let lb = Lexing.from_string content in
    Why3.Loc.set_file file lb;
    stack := [0];  (* reinitialise indentation stack *)
    Why3.Loc.with_location parse_file lb

}

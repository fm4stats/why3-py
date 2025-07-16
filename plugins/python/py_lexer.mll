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
       "forall", PyFORALL; "exists", PyEXISTS; "then", PyTHEN; "let", PyLET;
       "old", PyOLD; "at", PyAT; "variant", PyVARIANT; "call", PyCALL;
       "by", PyBY; "so", PySO;
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
  | (ident ("'" ident)+) as id
            { [PyQIDENT id] }
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
  | "<-"    { [PyLARROW] }
  | "<->"   { [PyLRARROW] }
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

  let next_token =
    let tokens = Queue.create () in
    fun lb ->
      if Queue.is_empty tokens then begin
	let l = next_tokens lb in
	List.iter (fun t -> Queue.add t tokens) l
      end;
      Queue.pop tokens

  let parse_file lb =
    let module I = Py_parser.MenhirInterpreter in
    let checkpoint = Py_parser.Incremental.py_file lb.lex_curr_p in
    let supplier () =
      let pos1 = lb.lex_curr_p in
      let tok = next_token lb in
      let pos2 = lb.lex_curr_p in
      (tok, pos1, pos2)
    in
    I.loop supplier checkpoint

  let input_all c =
    let len = in_channel_length c in
    really_input_string c len

  let parse file c =
    let content = input_all c in
    let lb = Lexing.from_string content in
    Why3.Loc.set_file file lb;
    stack := [0];  (* reinitialise indentation stack *)
    Why3.Loc.with_location parse_file lb

  (* Entries for transformations: similar to lexer.mll *)
  let build_parsing_function entry lb = Why3.Loc.with_location (entry next_token) lb

  let parse_term = build_parsing_function Py_parser.py_term_eof

  let parse_term_list = build_parsing_function Py_parser.py_term_comma_list_eof

  let parse_list_ident = build_parsing_function Py_parser.py_ident_comma_list_eof


}

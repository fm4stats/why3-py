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

(* This is a copy of [src/core/keywords.mli], with the following minor changes:

* use Py_parser.token instead of Parser.token.

*)

val keyword_tokens: (string * Py_parser.token) list

(* does not include contextual tokens *)
val keywords: string list

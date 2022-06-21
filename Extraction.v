(* *********************************************************************)
(*                                                                     *)
(*                 Coqlex verified lexer generator                     *)
(*                                                                     *)
(*  Copyright 2021 Siemens Mobility SAS and Institut National de       *)
(*  Recherche en Informatique et en Automatique.                       *)
(*  All rights reserved. This file is distributed under                *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

Require Coq.extraction.Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt SimpleLexerGenerator SimpleLexerGeneratorSpeedUp SimpleLexerGeneratorSpeedUp2 RValues.
Require Import RegExp.Char.
Require Import Parser Lexer.
Extraction Language OCaml.
Extraction Blacklist Char String List.
Separate Extraction Parser.prog SimpleLexerGenerator.make_lexer SimpleLexerGeneratorSpeedUp.make_lexer SimpleLexerGenerator.make_if_true_err_else_no_token_lexer SimpleLexerGeneratorSpeedUp2.make_lexer Lexer.thelexer newline identifier string_regex char_regex string_to_re charList_to_re regex_any ocamlStrInterp removeFirstAndLast removeFirst to_Char OPos flush_whole_history keep_matched_str ignore_matched_str_history simplyReturnToken.
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

Require Import SimpleLexerGenerator SimpleLexerGeneratorSpeedUp2 RValues.
Require Import Parser.
Require Import RegExp.Definitions RegExp.Char.
Import ListNotations.


Definition action_lexer := (SimpleLexerGeneratorSpeedUp2.make_lexer [
			(string_to_re "{", [keep_matched_str; SelfRec; keep_matched_str; SelfRec]);
			(string_to_re "}", [TokenReturn (fun str _ _ _ _ whole => (ResultOk (BRACECONTENT whole), whole))]) ;
      (Char "010", [newline; keep_matched_str; SelfRec]);
			(regex_any, [keep_matched_str; SelfRec])
		] 
			(simplyRaiseError "Un-finished Action"%string)).

Definition action_lexer_user := (SimpleLexerGeneratorSpeedUp2.make_lexer [
			(string_to_re "%{", [keep_matched_str; SelfRec; keep_matched_str; SelfRec]);
			(string_to_re "}%", [TokenReturn (fun str _ _ _ _ whole => (ResultOk (BRACECONTENT whole), whole))]);
      (Char "010", [newline; keep_matched_str; SelfRec]);
			(regex_any, [keep_matched_str; SelfRec])
		] 
			(simplyRaiseError "Un-finished Action"%string)).

Definition comment := (SimpleLexerGeneratorSpeedUp2.make_lexer (Token := token) (Hist := string)
		[
			(string_to_re "(*", [SelfRec; SelfRec] );
			(string_to_re "*)", []);
      (Char "010", [newline; SelfRec]);
			(regex_any, [SelfRec])
		] 
			(simplyRaiseError "Un-finished Action"%string)).

Definition history_type_setting := (SimpleLexerGeneratorSpeedUp2.make_lexer (Token := token) (Hist := string)
		[
			(string_to_re ".", [TokenReturn (fun str _ _ _ _ whole => (ResultOk (HISTORY_TYPE whole), whole))] );
      (Char "010", [newline; keep_matched_str; SelfRec]);
			(regex_any, [keep_matched_str; SelfRec])
		] 
			(simplyRaiseError "Un-finished history_type_setting"%string)).

Definition history_default_value_setting := (SimpleLexerGeneratorSpeedUp2.make_lexer (Token := token) (Hist := string)
		[
			(string_to_re ".", [TokenReturn (fun str _ _ _ _ whole => (ResultOk (HISTORY_DEFAULT whole), whole))] );
      (Char "010", [newline; keep_matched_str; SelfRec]);
			(regex_any, [keep_matched_str; SelfRec])
		] 
			(simplyRaiseError "Un-finished history_default_value_setting"%string)).

Definition token_type_setting := (SimpleLexerGeneratorSpeedUp2.make_lexer (Token := token) (Hist := string)
		[
			(string_to_re ".", [TokenReturn (fun str _ _ _ _ whole => (ResultOk (TOKEN_TYPE whole), whole))] );
      (Char "010", [newline; keep_matched_str; SelfRec]);
			(regex_any, [keep_matched_str; SelfRec])
		] 
			(simplyRaiseError "Un-finished token_type_setting"%string)).

Definition thelexer := 
	(SimpleLexerGeneratorSpeedUp2.make_lexer 
		[
			(charList_to_re [" "%char; "009"%char; "013"%char], [SelfRec]); 
      (string_to_re "%set_history_type", [flush_whole_history; (AnotherLexer history_type_setting)]); 
      (string_to_re "%set_default_history_value", [flush_whole_history; (AnotherLexer history_default_value_setting)]); 
      (string_to_re "%set_token_type", [flush_whole_history; (AnotherLexer token_type_setting)]); 
      (Char "010", [newline; SelfRec]);
			(Char "(", simplyReturnToken (LPARENT tt)); 
			(Char ")", simplyReturnToken (RPARENT tt)); 
			(Char "[", simplyReturnToken (LBRACKET tt)); 
			(Char "]", simplyReturnToken (RBRACKET tt)); 
			(Char "*", simplyReturnToken (STAR tt)); 
			(Char "_", simplyReturnToken (UNDERSCORE tt)); 
			(Char "+", simplyReturnToken (PLUS tt)); 
			(Char "|", simplyReturnToken (VBAR tt)); 
			(Char "?", simplyReturnToken (QMARK tt)); 
			(Char "-", simplyReturnToken (MINUS tt)); 
			(Char "^", simplyReturnToken (CIRCUMFLEX tt)); 
			(Char "$", simplyReturnToken (DOLLARD tt)); 
  		(Char "@", simplyReturnToken (ATSYMB tt)); 
  		(Char "=", simplyReturnToken (EQ tt)); 
      (string_to_re "let", simplyReturnToken (LET tt)); 
			(string_to_re "rule", simplyReturnToken (RULE tt)); 
			(string_to_re "and", simplyReturnToken (AND tt)); 
			(string_to_re "parse", simplyReturnToken (PARSE tt)); 
  		(identifier, [TokenReturn (fun id _ _ _ _ h => (ResultOk (IDENT id), h))]); 
  		(string_regex, [TokenReturn (fun str _ _ _ _ h => (ResultOk (STR_LIT (ocamlStrInterp (removeFirstAndLast str))), h))]); 
  		(char_regex, [TokenReturn (fun str _ _ _ _ h => (match to_Char (ocamlStrInterp (removeFirstAndLast str)) with | Some v => ResultOk ( CH_LIT v) | None => ResultError ("Impossible"%string) end, h))]); 
  		(string_to_re "(*", [flush_whole_history; (AnotherLexer comment); SelfRec]); 
      (string_to_re "{",  [flush_whole_history; (AnotherLexer action_lexer)]);
  		(string_to_re "%{", [flush_whole_history; (AnotherLexer action_lexer_user)])
		] 
			(simplyReturnToken (EOF tt))).



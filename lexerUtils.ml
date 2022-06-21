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

open Format
open Lexing
open Stream
open SimpleLexerGenerator
open Char0

exception UserErr of string
exception SpecDefinitionError of string 
exception CantProcessError of coq_Position 

let getPositionHelper lexbuf = {l_number = lexbuf.lex_curr_p.pos_lnum; c_number = lexbuf.lex_curr_p.pos_bol; abs_pos = lexbuf.lex_curr_p.pos_cnum }

let setPositionHelper lexbuf pos = match pos with
| { l_number = l; c_number = c; abs_pos = abs } -> 
        lexbuf.lex_start_pos <- lexbuf.lex_curr_pos;
        lexbuf.lex_curr_pos <- abs;
		lexbuf.lex_start_p <- lexbuf.lex_curr_p;
		lexbuf.lex_curr_p <- {{pos_fname = ""; pos_lnum  = l; pos_bol = c; pos_cnum = abs} with pos_fname = lexbuf.lex_curr_p.pos_fname}; 
		lexbuf.lex_abs_pos <- abs

let getStringHelper lexbuf = Bytes.sub_string lexbuf.lex_buffer lexbuf.lex_abs_pos (lexbuf.lex_buffer_len - lexbuf.lex_abs_pos)

let string_of_char_list cl = String.concat "" (List.map (String.make 1) cl)

let char_list_of_string s = List.init (String.length s) (String.get s)

let string_Adapter coq_lexer str pos = 
	match coq_lexer (char_list_of_string str) pos [] with 
	| (OneLexUserDefinitionErrorResult(err_mess, _, p), _) -> Format.printf "Error at position %d:%d@." p.l_number p.c_number; raise (UserErr(string_of_char_list err_mess))
	| (OneLexNoMatchErrorResult (rem, p), _) -> Format.printf "Error at position %d:%d@." p.l_number p.c_number; raise (CantProcessError p)
	| (OneLexSResult ({ token = {s_pos = _; 
                               	tok = t; 
                               	str_val = s };
                       cur_pos = p; 
                       remaining_str = rstr }), _) -> (t, (string_of_char_list rstr), p)
	| (OneLexSpecError (msg, _, p), _) -> Format.printf "Error at position %d:%d@." p.l_number p.c_number; raise (SpecDefinitionError (string_of_char_list msg))
	| (OneLexImplementationError _, p) -> failwith "Proven that it can never append"
	| (OneLexSpecNoToken (str_val, _, _, p), _) -> Format.printf "Error at position %d:%d (%s)@." p.l_number p.c_number (string_of_char_list str_val); raise (SpecDefinitionError "No token specified")
	| (OneLexLoop (_, p), _) -> Format.printf "Error at position %d:%d@." p.l_number p.c_number; raise (SpecDefinitionError "Infinite loop")

let lexbuf_Adapter coq_lexer lexbuf = 
	match coq_lexer (char_list_of_string (getStringHelper lexbuf)) (getPositionHelper lexbuf) [] with 
	| (OneLexUserDefinitionErrorResult(err_mess, _, p), _) -> Format.printf "Error at position %d:%d@."p.l_number p.c_number ; setPositionHelper lexbuf p ; setPositionHelper lexbuf p ; raise (UserErr(string_of_char_list err_mess))
	| (OneLexNoMatchErrorResult (rem, p), _) -> Format.printf "Error at position %d:%d (%s)@." p.l_number p.c_number (string_of_char_list rem) ; setPositionHelper lexbuf p ; raise (CantProcessError p)
	| (OneLexSResult ({ token = {s_pos = tspos; 
                               	tok = t; 
                               	str_val = s };
                       cur_pos = p; 
                       remaining_str = rstr }), _) -> setPositionHelper lexbuf tspos ; setPositionHelper lexbuf p ; t
	| (OneLexSpecError (msg, _, p), _) -> Format.printf "Error at position %d:%d@."p.l_number p.c_number ; setPositionHelper lexbuf p ; setPositionHelper lexbuf p ; raise (SpecDefinitionError (string_of_char_list msg))
	| (OneLexImplementationError (_, _, p), _) -> Format.printf "Error at position %d:%d@."p.l_number p.c_number ; setPositionHelper lexbuf p ; setPositionHelper lexbuf p ; failwith "Proven that it can never append"
	| (OneLexSpecNoToken (str_val, _, _, p), _) -> Format.printf "Error at position %d:%d (%s)@."p.l_number p.c_number (string_of_char_list str_val); setPositionHelper lexbuf p ; setPositionHelper lexbuf p ; raise (SpecDefinitionError "No token specified")
	| (OneLexLoop ( _, p), _) -> Format.printf "Error at position %d:%d@."p.l_number p.c_number ; setPositionHelper lexbuf p ; setPositionHelper lexbuf p ; raise (SpecDefinitionError "Infinite loop")

let string_to_re str = Char0.string_to_re (char_list_of_string str)

let default_starting_pos = {l_number = 1; c_number = 0; abs_pos = 0};;

let in_channel_to_string in_channel = 
	let rec in_channel_to_string_rec in_channel acc = 
		(
			try 
				in_channel_to_string_rec in_channel ((Stdlib.input_line in_channel)::acc)
			with End_of_file ->
				(List.rev acc) 
		) in
	String.concat "\n" (in_channel_to_string_rec in_channel [])

let filepath_to_string path = let in_channel = Stdlib.open_in path in in_channel_to_string in_channel

module LexerMaker (M : sig type t type h val coq_lexer : (t, (h list)) SimpleLexerGenerator.coq_RecLexer end) = struct
	let lex_from_lexbuf = lexbuf_Adapter M.coq_lexer ;;
	let lex_from_string_and_pos = string_Adapter M.coq_lexer ;;
end ;;
                    
                    
                    
                    

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

open Lexing
open LexerUtils
open Parser
open SimpleLexerGenerator

let report (lexb) =
  let b = lexeme_start_p lexb in
  let e = lexeme_end_p lexb in
  let l = b.pos_lnum in
  let fc = b.pos_bol in
  let lc = e.pos_bol in
  Format.eprintf "File \"%s\", line %d, characters %d-%d : Error near %s ()@." e.pos_fname l fc lc (lexeme lexb) (*String.sub (Bytes.sub_string lexb.lex_buffer lexb.lex_abs_pos (lexb.lex_buffer_len - lexb.lex_abs_pos)) 0 10*)


module GParser (M : sig type t val coq_lexer : (Parser.Aut.Gram.token, (char list)) SimpleLexerGenerator.coq_RecLexer val menhirParser : int -> MenhirLibParser.Inter.buffer -> t MenhirLibParser.Inter.parse_result end) = struct
	let ocamllexer = LexerUtils.lexbuf_Adapter M.coq_lexer ;;
	
	let coqlexer = LexerUtils.string_Adapter M.coq_lexer ;;
	
	let default_starting_pos = {l_number = 1; c_number = 0; abs_pos = 0};;
	
	let tokens_stream_from_lexbuf lexbuf : MenhirLibParser.Inter.buffer =
		let rec compute_token_stream () =
			let loop token =
				MenhirLibParser.Inter.Buf_cons (token, Lazy.from_fun compute_token_stream)
			in loop (ocamllexer lexbuf)
		in
		Lazy.from_fun compute_token_stream
	
	let tokens_stream_from_string str_to_lex starting_pos : MenhirLibParser.Inter.buffer =
		let rec compute_token_stream str pos () =
			let loop tokenXremaining_strXposition =
				let token, remaining_str, position = tokenXremaining_strXposition in
				MenhirLibParser.Inter.Buf_cons (token, Lazy.from_fun (compute_token_stream remaining_str position))
			in loop (coqlexer str pos)
		in
		Lazy.from_fun (compute_token_stream str_to_lex starting_pos)
	
	let ocamlparser_from_lexbuf lexbuf = 
		(match M.menhirParser 50 (tokens_stream_from_lexbuf lexbuf) with
		| Fail_pr_full (_, _) ->
		        report (lexbuf); failwith "failed!"
		| Timeout_pr ->
		        report (lexbuf); failwith "timed out!"
		| Parsed_pr (output, _) ->
		        output) ;;
	
	let coqparser_from_string ?starting_pos:(p=default_starting_pos) str = 
		(match M.menhirParser 50 (tokens_stream_from_string str p) with
		| Fail_pr_full (_, _) ->
		        failwith "failed!"
		| Timeout_pr ->
		        failwith "timed out!"
		| Parsed_pr (output, _) ->
		        output) ;;

	let parse_from_lexbuf = ocamlparser_from_lexbuf ;;
	let parse_from_string = coqparser_from_string ;;
	let rec lex_from_string ?starting_pos:(p=default_starting_pos) str = let token, remaining_str, position = coqlexer str p in if str <> "" then (lex_from_string ~starting_pos:position remaining_str) else ();;
end;;

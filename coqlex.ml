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

open ParserUtils
open LexerUtils
open Parser
open Lexer
open Definitions
open RValues
open Unix
open Sys

let buffer_size = 8192;;
let buffer = Bytes.create buffer_size;;

let file_copy input_name output_name =
  let fd_in = openfile input_name [O_RDONLY] 0 in
  let fd_out = openfile output_name [O_WRONLY; O_CREAT; O_TRUNC] 0o777 in
  let rec copy_loop () = match read fd_in buffer 0 buffer_size with
    |  0 -> ()
    | r -> ignore (write fd_out buffer 0 r); copy_loop ()
  in
  copy_loop ();
  close fd_in;
  close fd_out;;

let set_filename (fname:string) (lexbuf: Lexing.lexbuf)  =
    lexbuf.lex_curr_p <-  
        { lexbuf.lex_curr_p with pos_fname = fname }
    ; lexbuf
    

let create_directory ?perm:(perm = 0o777) dirname = 
	if (file_exists dirname) then 
			if not (is_directory dirname) then
				failwith ("Please remove your file named " ^ dirname)
			else
				()
		else
			Unix.mkdir dirname perm

module VlParser = 
struct 
	module M = ParserUtils.GParser(struct type t = Parser.coq_DataForLexer let coq_lexer = Lexer.thelexer let menhirParser = Parser.prog end);;
	let parse_from_lexbuf = M.parse_from_lexbuf;;
	let parse_from_string = M.parse_from_string;;
	let parse_from_file path = let lexbuf = set_filename path (Lexing.from_string (filepath_to_string path)) in parse_from_lexbuf lexbuf;;
	let lex_from_file path = M.lex_from_string (filepath_to_string path) ;;
end;;


let rec alist_print f alist = match alist with
| [] -> Format.fprintf f "" 
| h::[] -> Format.fprintf f "\"%03i\"%%char" (Char.code h)
| h::t -> Format.fprintf f "\"%03i\"%%char; %a" (Char.code h) alist_print t

let rec rlist_print f rlist = match rlist with
| [] -> Format.fprintf f "" 
| MCR(s, e)::[] -> Format.fprintf f "(RValues.rangeAscii2 \"%03i\"%%char \"%03i\"%%char)" (Char.code s) (Char.code e)
| MCR(s, e)::t -> Format.fprintf f "(List.app (RValues.rangeAscii2 \"%03i\"%%char \"%03i\"%%char) %a)" (Char.code s) (Char.code e) rlist_print t

let mclass_print f mclass = match mclass with
| MCC ([], []) ->  Format.fprintf f "" 
| MCC ([], rlist) ->  Format.fprintf f "%a" rlist_print rlist
| MCC (alist, []) ->  Format.fprintf f "[%a]" alist_print alist
| MCC (alist, rlist) ->  Format.fprintf f "(List.app [%a] %a)" alist_print alist rlist_print rlist

let rec print_coq_string f clist = match clist with
| [] -> Format.fprintf f "EmptyString"
| h::t -> Format.fprintf f "(String \"%03i\"%%char %a)" (Char.code h) print_coq_string t

let rec mregex_print f regex = match regex with
| MChar c -> Format.fprintf f "Char \"%03i\"%%char" (Char.code c)
| MEps -> Format.fprintf f "Eps"
| MCat (r1, r2) -> Format.fprintf f "Cat (%a) (%a)" mregex_print r1 mregex_print r2
| MOr (r1, r2) -> Format.fprintf f "Or (%a) (%a)" mregex_print r1 mregex_print r2
| MStar (r1) -> Format.fprintf f "Star (%a)" mregex_print r1 
| MNot (r1) -> Format.fprintf f "Not (%a)" mregex_print r1 
| MAnd (r1, r2) -> Format.fprintf f "And (%a) (%a)" mregex_print r1 mregex_print r2 
| MMinus (r1, r2) -> Format.fprintf f "RValues.minus (%a) (%a)" mregex_print r1 mregex_print r2
| MIdent s ->  Format.fprintf f "%s" (string_of_char_list s)
| MFromStr s ->  Format.fprintf f "RegExp.Char.string_to_re %a" print_coq_string s
| MAcceptClass c -> Format.fprintf f "RValues.charList_to_re %a" mclass_print c
| MNotAcceptClass c -> Format.fprintf f "RValues.class_char_except %a" mclass_print c
;;

let rec process_regexXaction f rXa = match rXa with
| [] -> Format.fprintf f ""
| (regex, action)::[] -> Format.fprintf f "(%a, %s)@." mregex_print regex (string_of_char_list (action))
| (regex, action)::t -> Format.fprintf f "(%a, %s);@.%a" mregex_print regex (string_of_char_list (action)) process_regexXaction t ;;

let process_explicit_tok_type f explicit_tok_type = if explicit_tok_type then Format.fprintf f "(Token := token_type) "

let process_explicit_hist_type f explicit_hist_type = if explicit_hist_type then Format.fprintf f "(Hist := history_type) "

let rec process_lexer_list explicit_tok_type explicit_hist_type f lexer_list = match lexer_list with
| [] -> Format.fprintf f ""
| ((lexer_name, rXa), eof_def)::t -> Format.fprintf f "Definition %s := (make_lexer %a%a[%a] (%s)).@.%a" (string_of_char_list lexer_name) process_explicit_tok_type explicit_tok_type process_explicit_hist_type explicit_hist_type process_regexXaction rXa (string_of_char_list (eof_def)) (process_lexer_list explicit_tok_type explicit_hist_type) t ;;

let rec lexer_names_bis f lexer_list = match lexer_list with
| [] -> Format.fprintf f ""
| ((lexer_name, rXa), eof_def)::t -> Format.fprintf f "%s %a" (string_of_char_list lexer_name) lexer_names_bis t ;;

let lexer_names f ld = match ld with
| LData (pre, token_type, history_type, history_default_value, bind_list, lexer_list, pos) -> lexer_names_bis f lexer_list ;;

let rec process_bind_list f bind_list = match bind_list with
| [] -> Format.fprintf f ""
| (id, value)::t -> Format.fprintf f "Definition %s := %a.@.%a" (string_of_char_list id) mregex_print value process_bind_list t ;;

let process_token_type_decl f stropt = match stropt with 
| None -> Format.fprintf f ""
| Some str -> Format.fprintf f "Definition token_type := %s." (string_of_char_list str)

let process_history_type_decl f stropt = match stropt with 
| None -> Format.fprintf f ""
| Some str -> Format.fprintf f "Definition history_type := %s." (string_of_char_list str)

let process_history_default_value_decl has_explicit_history_type f stropt = match stropt with 
| None -> Format.fprintf f ""
| Some str -> Format.fprintf f "Definition history_default_value %s:= %s." (if has_explicit_history_type then ": history_type" else "") (string_of_char_list str)

let processLD f ld = match ld with
| LData (pre, token_type, history_type, history_default_value, bind_list, lexer_list, pos) -> Format.fprintf f "%s@.%a@.%a@.%a@.%a@.%a@.%s" (string_of_char_list (pre)) process_token_type_decl token_type process_history_type_decl history_type (process_history_default_value_decl (history_type<>None)) history_default_value process_bind_list bind_list (process_lexer_list (token_type <> None) (history_type <> None)) lexer_list (string_of_char_list (pos));;

let codeGenerate f ld = Format.fprintf f "Require Import SimpleLexerGenerator RValues RegExp.Definitions RegExp.Char List.@.Import ListNotations.@.%a@.Require Coq.extraction.Extraction ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt.@.Extraction Blacklist Char String List.@.Extraction \"lexer.ml\" %a string_to_re OPos %s.@." processLD ld lexer_names ld (match ld with | LData (pre, token_type, history_type, Some _, bind_list, lexer_list, pos) -> "history_default_value" | _ -> "");;

let codeGenerate2 f ld = Format.fprintf f "Require Import SimpleLexerGenerator SimpleLexerGeneratorSpeedUp RValues RegExp.Definitions RegExp.Char List.@.Import ListNotations.@.%a@.Require Coq.extraction.Extraction ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt.@.Extraction Blacklist Char String List.@.Extraction \"lexer.ml\" %a string_to_re OPos %s.@." processLD ld lexer_names ld (match ld with | LData (pre, token_type, history_type, Some _, bind_list, lexer_list, pos) -> "history_default_value" | _ -> "");;

let codeGenerate3 f ld = Format.fprintf f "Require Import SimpleLexerGenerator SimpleLexerGeneratorSpeedUp2 RValues RegExp.Definitions RegExp.Char List.@.Import ListNotations.@.%a@.Require Coq.extraction.Extraction ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt.@.Extraction Blacklist Char String List.@.Extraction \"lexer.ml\" %a string_to_re OPos %s.@." processLD ld lexer_names ld (match ld with | LData (pre, token_type, history_type, Some _, bind_list, lexer_list, pos) -> "history_default_value" | _ -> "");;

let rec generateLexerModule_bis f lexer_list = match lexer_list with
| [] -> Format.fprintf f ""
| ((lexer_name, rXa), eof_def)::t -> Format.fprintf f "let %s_ocamllexer = lexbuf_Adapter Lexer.%s ;;@.let %s_coqlexer = charList_Adapter Lexer.%s ;;@.%a" (string_of_char_list lexer_name) (string_of_char_list lexer_name) (string_of_char_list lexer_name) (string_of_char_list lexer_name) generateLexerModule_bis t ;;

let generateLexerModule f ld = match ld with
| LData (pre, token_type, history_type, history_default_value, bind_list, lexer_list, pos) -> Format.fprintf f "%a"  generateLexerModule_bis lexer_list ;;

let process_hist_arg f ld = match ld with
| LData (pre, token_type, history_type, None, bind_list, lexer_list, pos) -> Format.fprintf f "hist"
| LData (pre, token_type, history_type, Some _, bind_list, lexer_list, pos) -> Format.fprintf f "?(hist=history_default_value)"

let utilCode f ld = Format.fprintf f "
exception UserErr of string
exception SpecDefinitionError of string 
exception CantProcessError of Lexer.position 

let getPositionHelper lexbuf = {l_number = lexbuf.lex_curr_p.pos_lnum; c_number = lexbuf.lex_curr_p.pos_bol; abs_pos = lexbuf.lex_curr_p.pos_cnum }

let setPositionHelper lexbuf pos = match pos with
| { l_number = l; c_number = c; abs_pos = abs } -> 
        lexbuf.lex_start_pos <- lexbuf.lex_curr_pos;
        lexbuf.lex_curr_pos <- abs;
		lexbuf.lex_start_p <- lexbuf.lex_curr_p;
		lexbuf.lex_curr_p <- {{pos_fname = \"\"; pos_lnum  = l; pos_bol = c; pos_cnum = abs} with pos_fname = lexbuf.lex_curr_p.pos_fname}; 
		lexbuf.lex_abs_pos <- abs

let getStringHelper lexbuf = Bytes.sub_string lexbuf.lex_buffer lexbuf.lex_abs_pos (lexbuf.lex_buffer_len - lexbuf.lex_abs_pos)

let string_of_char_list cl = String.concat \"\" (List.map (String.make 1) cl)

let char_list_of_string s = List.init (String.length s) (String.get s)

let default_starting_pos = oPos;;

let string_Adapter coq_lexer ?(pos=default_starting_pos) %a str = 
	match coq_lexer (char_list_of_string str) pos hist with 
	| (OneLexUserDefinitionErrorResult(err_mess, _, p), _) -> Format.printf \"Error at position %%d:%%d@.\"p.l_number p.c_number; raise (UserErr(string_of_char_list err_mess))
	| (OneLexNoMatchErrorResult (rem, p), _) -> Format.printf \"Error at position %%d:%%d@.\"p.l_number p.c_number; raise (CantProcessError p)
	| (OneLexSResult ({ token = {s_pos = _; 
                               	tok = t; 
                               	str_val = s };
                       cur_pos = p; 
                       remaining_str = rstr }), _) -> (t, (string_of_char_list rstr), p)
	| (OneLexSpecError (msg, _, p), _) -> Format.printf \"Error at position %%d:%%d@.\"p.l_number p.c_number; raise (SpecDefinitionError (string_of_char_list msg))
	| (OneLexImplementationError _, _) -> failwith \"Proven that it can never append\"
	| (OneLexSpecNoToken (_, _, _, p), _) -> Format.printf \"Error at position %%d:%%d@.\"p.l_number p.c_number; raise (SpecDefinitionError \"No token specified\")
	| (OneLexLoop (_, p), _) -> Format.printf \"Error at position %%d:%%d@.\"p.l_number p.c_number; raise (SpecDefinitionError \"Infinite loop\")
	
let charList_Adapter coq_lexer ?(pos=default_starting_pos) %a str = 
	match coq_lexer str pos hist with 
	| (OneLexUserDefinitionErrorResult(err_mess, _, p), _) -> Format.printf \"Error at position %%d:%%d@.\"p.l_number p.c_number; raise (UserErr(string_of_char_list err_mess))
	| (OneLexNoMatchErrorResult (rem, p), _) -> Format.printf \"Error at position %%d:%%d@.\"p.l_number p.c_number; raise (CantProcessError p)
	| (OneLexSResult ({ token = {s_pos = _; 
                               	tok = t; 
                               	str_val = s };
                       cur_pos = p; 
                       remaining_str = rstr }), h) -> (t, rstr, p, h)
	| (OneLexSpecError (msg, _, p), _) -> Format.printf \"Error at position %%d:%%d@.\"p.l_number p.c_number; raise (SpecDefinitionError (string_of_char_list msg))
	| (OneLexImplementationError _, _) -> failwith \"Proven that it can never append\"
	| (OneLexSpecNoToken (_, _, _, p), _) -> Format.printf \"Error at position %%d:%%d@.\"p.l_number p.c_number; raise (SpecDefinitionError \"No token specified\")
	| (OneLexLoop (_, p), _) -> Format.printf \"Error at position %%d:%%d@.\"p.l_number p.c_number; raise (SpecDefinitionError \"Infinite loop\")

let lexbuf_Adapter coq_lexer %a lexbuf = 
	match coq_lexer (char_list_of_string (getStringHelper lexbuf)) (getPositionHelper lexbuf) hist with 
	| (OneLexUserDefinitionErrorResult(err_mess, _, p), _) -> Format.printf \"Error at position %%d:%%d@.\"p.l_number p.c_number; setPositionHelper lexbuf p ; raise (UserErr(string_of_char_list err_mess))
	| (OneLexNoMatchErrorResult (rem, p), _) -> Format.printf \"Error at position %%d:%%d@.\"p.l_number p.c_number; setPositionHelper lexbuf p ; raise (CantProcessError p)
	| (OneLexSResult ({ token = {s_pos = tspos; 
                               	tok = t; 
                               	str_val = s };
                       cur_pos = p; 
                       remaining_str = rstr }), _) -> setPositionHelper lexbuf tspos ; setPositionHelper lexbuf p ; t
	| (OneLexSpecError (msg, _, p), _) -> Format.printf \"Error at position %%d:%%d@.\"p.l_number p.c_number; setPositionHelper lexbuf p ; raise (SpecDefinitionError (string_of_char_list msg))
	| (OneLexImplementationError (_, _, p), _) -> Format.printf \"Error at position %%d:%%d@.\"p.l_number p.c_number; setPositionHelper lexbuf p ; failwith \"Proven that it can never append\"
	| (OneLexSpecNoToken (_, _, _, p), _) -> Format.printf \"Error at position %%d:%%d@.\"p.l_number p.c_number; setPositionHelper lexbuf p ; raise (SpecDefinitionError \"No token specified\")
	| (OneLexLoop ( _, p), _) -> Format.printf \"Error at position %%d:%%d@.\"p.l_number p.c_number; setPositionHelper lexbuf p ; raise (SpecDefinitionError \"Infinite loop\")

let string_to_re str = Lexer.string_to_re (char_list_of_string str)

let in_channel_to_string in_channel = 
	let rec in_channel_to_string_rec in_channel acc = 
		(
			try 
				in_channel_to_string_rec in_channel ((Stdlib.input_line in_channel)::acc)
			with End_of_file ->
				(List.rev acc) 
		) in
	String.concat \"\n\" (in_channel_to_string_rec in_channel [])

let filepath_to_string path = let in_channel = Stdlib.open_in path in in_channel_to_string in_channel" process_hist_arg ld process_hist_arg ld process_hist_arg ld
;;

let mainMLGenerate f ld = Format.fprintf f "open Format@.open Lexer@.open Lexing@.%a@.%a@." utilCode ld generateLexerModule ld ;;

let compileSHGenerate f = Format.fprintf f "
#!/bin/bash
coqc CoqLexer.v
ocamlc -c lexer.mli
ocamlc -c lexer.ml
ocamlc -c main.ml
" ;;

let () =
	begin
		let usage_msg = Format.sprintf "A program to generate a Coq-lexer .@;Usage : %s filename" Sys.argv.(0) in
		let inputPath = ref None in
		let speclist = [] in
		Arg.parse speclist (fun anon -> inputPath := Some anon) usage_msg;
		match !inputPath with
		| None -> failwith "No input file"
		| Some path -> Format.printf "Parsing@."; let parsed = VlParser.parse_from_file path in
				Format.printf "Parsed@.";
				let inputfile_dirname = Filename.concat (Filename.dirname path) "TheCoqLexerGenerated" in
				create_directory inputfile_dirname;
				let coqlexer_dir = Filename.concat inputfile_dirname "v0" in
				Format.printf "generating v0@.";
				create_directory coqlexer_dir; 
				file_copy "SimpleLexerGenerator.vo" (Filename.concat coqlexer_dir "SimpleLexerGenerator.vo");
				file_copy "RValues.vo" (Filename.concat coqlexer_dir "RValues.vo");
				file_copy "UsefullProofs.vo" (Filename.concat coqlexer_dir "UsefullProofs.vo");
				file_copy "MatchLen.vo" (Filename.concat coqlexer_dir "MatchLen.vo");
				file_copy "MatchLenSpeedUp2.vo" (Filename.concat coqlexer_dir "MatchLenSpeedUp2.vo");
				(*file_copy "lexerUtils.ml" (Filename.concat coqlexer_dir "lexerUtils.ml");*)
				let out_channel = open_out (Filename.concat coqlexer_dir "CoqLexer.v") in
				codeGenerate (Format.formatter_of_out_channel out_channel) parsed ; 
				close_out out_channel (*;VlParser.lex_from_file path*);
				let out_channel = open_out (Filename.concat coqlexer_dir "main.ml") in
				mainMLGenerate (Format.formatter_of_out_channel out_channel) parsed ; close_out out_channel;
				let out_channel = open_out (Filename.concat coqlexer_dir "compile.sh") in
				compileSHGenerate (Format.formatter_of_out_channel out_channel) ; close_out out_channel;
				
				let coqlexer_dir = Filename.concat inputfile_dirname "v0.1" in
				Format.printf "generating v0.1@.";
				create_directory coqlexer_dir; 
				file_copy "SimpleLexerGenerator.vo" (Filename.concat coqlexer_dir "SimpleLexerGenerator.vo");
				file_copy "SimpleLexerGeneratorSpeedUp.vo" (Filename.concat coqlexer_dir "SimpleLexerGeneratorSpeedUp.vo");
				file_copy "RValues.vo" (Filename.concat coqlexer_dir "RValues.vo");
				file_copy "UsefullProofs.vo" (Filename.concat coqlexer_dir "UsefullProofs.vo");
				file_copy "MatchLen.vo" (Filename.concat coqlexer_dir "MatchLen.vo");
				file_copy "MatchLenSpeedUp2.vo" (Filename.concat coqlexer_dir "MatchLenSpeedUp2.vo");
				file_copy "MatchLenSpeedUp.vo" (Filename.concat coqlexer_dir "MatchLenSpeedUp.vo");
				(*file_copy "lexerUtils.ml" (Filename.concat coqlexer_dir "lexerUtils.ml");*)
				let out_channel = open_out (Filename.concat coqlexer_dir "CoqLexer.v") in
				codeGenerate2 (Format.formatter_of_out_channel out_channel) parsed ; 
				close_out out_channel (*;VlParser.lex_from_file path*);
				let out_channel = open_out (Filename.concat coqlexer_dir "main.ml") in
				mainMLGenerate (Format.formatter_of_out_channel out_channel) parsed ; close_out out_channel;
				let out_channel = open_out (Filename.concat coqlexer_dir "compile.sh") in
				compileSHGenerate (Format.formatter_of_out_channel out_channel) ; close_out out_channel;
				
				let coqlexer_dir = Filename.concat inputfile_dirname "v0.2" in
				Format.printf "generating v0.2@.";
				create_directory coqlexer_dir; 
				file_copy "SimpleLexerGenerator.vo" (Filename.concat coqlexer_dir "SimpleLexerGenerator.vo");
				file_copy "SimpleLexerGeneratorSpeedUp2.vo" (Filename.concat coqlexer_dir "SimpleLexerGeneratorSpeedUp2.vo");
				file_copy "RValues.vo" (Filename.concat coqlexer_dir "RValues.vo");
				file_copy "UsefullProofs.vo" (Filename.concat coqlexer_dir "UsefullProofs.vo");
				file_copy "MatchLen.vo" (Filename.concat coqlexer_dir "MatchLen.vo");
				file_copy "MatchLenSpeedUp2.vo" (Filename.concat coqlexer_dir "MatchLenSpeedUp2.vo");
				(*file_copy "lexerUtils.ml" (Filename.concat coqlexer_dir "lexerUtils.ml");*)
				let out_channel = open_out (Filename.concat coqlexer_dir "CoqLexer.v") in
				codeGenerate3 (Format.formatter_of_out_channel out_channel) parsed ; 
				close_out out_channel (*;VlParser.lex_from_file path*);
				let out_channel = open_out (Filename.concat coqlexer_dir "main.ml") in
				mainMLGenerate (Format.formatter_of_out_channel out_channel) parsed ; close_out out_channel;
				let out_channel = open_out (Filename.concat coqlexer_dir "compile.sh") in
				compileSHGenerate (Format.formatter_of_out_channel out_channel) ; close_out out_channel
				
	end

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

%{
Require Import List.
Require Import Coq.Strings.Ascii Coq.Strings.String.
Import ListNotations.

Inductive MCharRange :=
| MCR : ascii -> ascii -> MCharRange.

Inductive MCharClass :=
| MCC : (list ascii) -> (list MCharRange) -> MCharClass.

Definition MCC_from_ascii_list ascii_list := MCC ascii_list [].

Definition MCC_from_MCharRange mcharrange := MCC [] [mcharrange].

Definition MCC_add_ascii_list mcc ascii_list := 
match mcc with
| MCC al mr => MCC (List.app al ascii_list) mr
end.

Definition MCC_add_MCharRange mcc mcharrange := 
match mcc with
| MCC al mr => MCC al (List.app mr mcharrange)
end.

Definition MCC_add mcc mcc2 :=
match mcc, mcc2 with
| MCC al mr, MCC al2 mr2 => MCC (List.app al al2) (List.app mr mr2)
end.

Inductive MRegExp := 
| MChar : ascii -> MRegExp
| MAcceptClass : MCharClass -> MRegExp
| MNotAcceptClass : MCharClass -> MRegExp
| MIdent : string -> MRegExp
| MCat : MRegExp -> MRegExp -> MRegExp
| MStar : MRegExp -> MRegExp
| MNot : MRegExp -> MRegExp
| MOr : MRegExp -> MRegExp -> MRegExp
| MAnd : MRegExp -> MRegExp -> MRegExp
| MMinus : MRegExp -> MRegExp -> MRegExp
| MFromStr : string -> MRegExp
| MEps : MRegExp.

Inductive DataForLexer :=
| LData : string -> option string -> option string -> option string -> (list (string * MRegExp)) -> (list ( string * (list (MRegExp * string)) * string) ) -> string -> DataForLexer.
  
%}

%token LPARENT RPARENT LBRACKET RBRACKET CIRCUMFLEX STAR UNDERSCORE PLUS VBAR QMARK ATSYMB EOF MINUS RULE AND EQ PARSE DOLLARD LET
%token <ascii> CH_LIT
%token <string> BRACECONTENT IDENT STR_LIT HISTORY_TYPE HISTORY_DEFAULT TOKEN_TYPE

%start<DataForLexer> prog
%type <MRegExp> regex term factor expression atom
%type <string> header bracecontent bracecontent_opt trailler eof_part
%type <list (MRegExp * string)> lexer_definition
%type <string * (list (MRegExp * string)) * string> lexer
%type <list (string * (list (MRegExp * string)) * string)> lexer_list lexers
%type <MCharClass> characterrange characterclass 
%type <string * MRegExp> regex_bind_one
%type <list (string * MRegExp)> regex_bind_list regex_bind
%type <option string> token_type history_type history_default_value
%%

prog : | h = header tot = token_type ht = history_type hv = history_default_value b = regex_bind l = lexers t = trailler EOF { LData h tot ht hv b l t }

history_type : | { None }
               | ht = HISTORY_TYPE { Some ht }

token_type : | { None }
               | tot = TOKEN_TYPE { Some tot }

history_default_value : | { None }
               | hv = HISTORY_DEFAULT { Some hv }

regex_bind :  |  { [] }
              | l = regex_bind_list { l }

regex_bind_list : | b = regex_bind_one { [b] }
                  | l = regex_bind_list b = regex_bind_one { List.app l [b] }

regex_bind_one : LET i = IDENT EQ r = regex { (i, r) }

bracecontent : | c = BRACECONTENT { c }

bracecontent_opt : | { ""%string }
                   | c = bracecontent  { c }

header : | c = bracecontent_opt { c }

trailler : | c = bracecontent_opt { c }

lexers : | RULE l = lexer_list { l }

lexer_list :  | l = lexer { [l] }
              | ls = lexer_list AND l = lexer { List.app ls [l] }

lexer : id = IDENT EQ PARSE l = lexer_definition eof_def = eof_part { (id, l, eof_def) }

eof_part : DOLLARD eof_def = bracecontent { eof_def }
           |                              { ""%string }

lexer_definition : r = regex c = bracecontent { [(r, c)] }
                   | VBAR r = regex c = bracecontent { [(r, c)] }
                   | l = lexer_definition VBAR r = regex c = bracecontent { List.app l [(r, c)] }

regex :       | e = expression { e }

expression :  | t = term { t }
              | e = expression VBAR t = term {MOr e t}


term :        | f = factor { f }
              | t = term ATSYMB f = factor {MCat t f}
              | t = term MINUS f = factor {MMinus t f}

factor :      | a = atom  { a }
              | t = atom STAR {MStar t} 
              | t = atom PLUS {MCat t (MStar t)} 
              | t = atom QMARK {MOr MEps t} 

atom : | c = CH_LIT {MChar c}
       | UNDERSCORE { MIdent "RValues.regex_any"%string }
       | LPARENT e = expression RPARENT { e }
       | LBRACKET c = characterclass RBRACKET { MAcceptClass c }
       | LBRACKET CIRCUMFLEX c = characterclass RBRACKET { MNotAcceptClass c }
       | s = STR_LIT {MFromStr s}
       | id = IDENT { MIdent id }


characterclass :  
       | c = characterrange { c }
       | c1 = characterclass c = characterrange {MCC_add c1 c}

characterrange : 
       | c = CH_LIT { MCC_from_ascii_list [c] }
       | b = CH_LIT MINUS e = CH_LIT {MCC_from_MCharRange (MCR b e)}

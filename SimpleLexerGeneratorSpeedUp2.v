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

Require Import SimpleLexerGenerator.
Require Import MatchLenSpeedUp2.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import UsefullProofs.
Require Import micromega.Lia.
Import ListNotations.


Fixpoint electCandidateSpeedUp2 {Action : Set} RegexpXAction_list str := match RegexpXAction_list with
| [] => None
| (re, ac)::t => (match match_len_opt re str with 
            | None => electCandidateSpeedUp2 t str
            | Some n => (match electCandidateSpeedUp2(Action:=Action) t str with
                        | Some c => Some (if Nat.ltb n (resultNat c) then c else (mkElectionResult Action re ac n) )
                        | None => Some (mkElectionResult Action re ac n)
                        end)
          end)
end.

Definition electionSpeedUp2 {Action : Set} regexp_to_action str := electCandidateSpeedUp2 (Action := Action) regexp_to_action str.

Lemma electionSpeedUp_correct {Action : Set} : forall regexp_to_action str, election regexp_to_action str = electionSpeedUp2 (Action:=Action) regexp_to_action str.
Proof.
unfold electionSpeedUp2.
unfold election.
induction regexp_to_action; simpl; auto.
induction a.
intros.
rewrite IHregexp_to_action.
rewrite match_len_equiv_opt; auto.
Qed.

Lemma electionSpeedUp2_inf_strLen {Action : Set} : forall str regexp_to_action e, electionSpeedUp2 (Action := Action) regexp_to_action str = Some e -> resultNat e <= String.length str.
Proof.
intros.
rewrite <- electionSpeedUp_correct in H.
eapply election_inf_strLen; eauto.
Qed.

Definition parseElectorSpeedup2 {Action : Set}:= mkElector Action electionSpeedUp2 electionSpeedUp2_inf_strLen.

Definition make_lexer {Token Hist : Set} regexp_x_action (eof_action : Action (Token := Token) (Hist := Hist)) := 
  mkRecLexer 
    Token 
    Hist
    (lexergenerator parseElectorSpeedup2 regexp_x_action eof_action) 
    (lexergenerator_start_end_position parseElectorSpeedup2 regexp_x_action eof_action)
    (lexergenerator_tok_position parseElectorSpeedup2 regexp_x_action eof_action)
    (lexergenerator_start_tok_position parseElectorSpeedup2 regexp_x_action eof_action)
    (lexergenerator_start_cur_position_abs parseElectorSpeedup2 regexp_x_action eof_action)
    (lexergenerator_correct_consum parseElectorSpeedup2 regexp_x_action eof_action)
    (lexergenerator_no_implementation_error parseElectorSpeedup2 regexp_x_action eof_action)
    (lexergenerator_start_interruption_position parseElectorSpeedup2 regexp_x_action eof_action)
    (lexergenerator_start_interruption_position2 parseElectorSpeedup2 regexp_x_action eof_action)
.

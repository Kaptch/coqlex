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
Require Import MatchLenSpeedUp.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import UsefullProofs.
Require Import micromega.Lia.
Import ListNotations.


Fixpoint electCandidateSpeedUp {Action : Set} RegexpXAction_list str := match RegexpXAction_list with
| [] => None
| (re, ac)::t => (match match_len_speed_up_v2 re str with 
            | None => electCandidateSpeedUp t str
            | Some n => (match electCandidateSpeedUp(Action:=Action) t str with
                        | Some c => Some (if Nat.ltb n (resultNat c) then c else (mkElectionResult Action re ac n) )
                        | None => Some (mkElectionResult Action re ac n)
                        end)
          end)
end.

Lemma electCandidateSpeedUp_correct {Action : Set} : forall RegexpXAction_list str, electCandidate (Action:=Action) RegexpXAction_list str = electCandidateSpeedUp RegexpXAction_list str.
Proof.
induction RegexpXAction_list; simpl; auto.
induction a.
intros.
rewrite IHRegexpXAction_list.
rewrite match_len_speed_up_v2_correct; auto.
Qed.

Definition electionSpeedUp {Action : Set} regexp_to_action str := electCandidateSpeedUp (Action := Action) regexp_to_action str.

Lemma electionSpeedUp_correct {Action : Set} : forall regexp_to_action str, election regexp_to_action str = electionSpeedUp (Action:=Action) regexp_to_action str.
Proof.
unfold electionSpeedUp.
unfold election.
intros.
rewrite electCandidateSpeedUp_correct; auto.
Qed.

Lemma electionSpeedUp_inf_strLen {Action : Set} : forall str regexp_to_action e, electionSpeedUp (Action := Action) regexp_to_action str = Some e -> resultNat e <= String.length str.
Proof.
intros.
rewrite <- electionSpeedUp_correct in H.
eapply election_inf_strLen; eauto.
Qed.

Definition parseElectorSpeedup {Action : Set}:= mkElector Action electionSpeedUp electionSpeedUp_inf_strLen.

Definition make_lexer {Token Hist : Set} regexp_x_action (eof_action : Action (Token := Token) (Hist := Hist)) := 
  mkRecLexer 
    Token 
    Hist
    (lexergenerator parseElectorSpeedup regexp_x_action eof_action) 
    (lexergenerator_start_end_position parseElectorSpeedup regexp_x_action eof_action)
    (lexergenerator_tok_position parseElectorSpeedup regexp_x_action eof_action)
    (lexergenerator_start_tok_position parseElectorSpeedup regexp_x_action eof_action)
    (lexergenerator_start_cur_position_abs parseElectorSpeedup regexp_x_action eof_action)
    (lexergenerator_correct_consum parseElectorSpeedup regexp_x_action eof_action)
    (lexergenerator_no_implementation_error parseElectorSpeedup regexp_x_action eof_action)
    (lexergenerator_start_interruption_position parseElectorSpeedup regexp_x_action eof_action)
    (lexergenerator_start_interruption_position2 parseElectorSpeedup regexp_x_action eof_action) 
.








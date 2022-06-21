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

Require Import RegExp.Definitions.
Require Import RegExp.Boolean.
Require Import RegExp.Char.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Compare.
Require Import Coq.Arith.PeanoNat.
Require Import micromega.Lia.
Require Import UsefullProofs.
Require Import MatchLen.
Require Import RValues.
Require Import Coq.Lists.List.
Import ListNotations.

Inductive Result {Token : Set} : Set :=
| ResultOk : Token -> Result
| ResultError : string -> Result.

Record Position : Set := mkPosition
{
  l_number : nat;
  c_number : nat;
  abs_pos : nat
}.

Record LexingOkItemv2 {Token : Set} : Set := mkLexingOkItemv2
{
  s_pos : Position ;
  tok : Token ;
  str_val : string
}.

Record OneLexSuccesResult {Token : Set} : Set := mkOneLexSuccesResult
{
   token : LexingOkItemv2 (Token := Token)
  ;cur_pos : Position
  ;remaining_str : string
}.

Inductive OneLexResult {Token : Set} : Type :=
| OneLexSResult : OneLexSuccesResult (Token := Token)  -> OneLexResult
| OneLexUserDefinitionErrorResult : string -> string -> Position -> OneLexResult
| OneLexSpecNoToken :  string -> Position -> string -> Position -> OneLexResult
| OneLexSpecError :  string -> string -> Position -> OneLexResult
| OneLexImplementationError : nat -> string -> Position -> OneLexResult
| OneLexNoMatchErrorResult : string -> Position -> OneLexResult
(* | OneLexNoConsumeWT : Token -> string -> Position -> OneLexResult
| OneLexNoConsumeEmpty : string -> Position -> OneLexResult *)
| OneLexLoop : string -> Position -> OneLexResult.

Definition extractCurrentPosition {Token : Set} (o : OneLexResult(Token:=Token)) := match o with
| OneLexSResult
               {|
               token := tok;
               cur_pos := cur_pos;
               remaining_str := remaining_str; |} => cur_pos
| OneLexUserDefinitionErrorResult _ _ p => p
| OneLexSpecNoToken _ _ _ p => p
| OneLexSpecError _ _ p => p
| OneLexImplementationError _ _ p => p
| OneLexNoMatchErrorResult _ p => p
| OneLexLoop _ p => p
(* | OneLexNoConsumeWT _ _ p => p
| OneLexNoConsumeEmpty _ p => p *)
end.

Definition extractRemainingString {Token : Set} (o : OneLexResult(Token:=Token)) := match o with
| OneLexSResult
               {|
               token := tok;
               cur_pos := cur_pos;
               remaining_str := remaining_str; |} => remaining_str
| OneLexUserDefinitionErrorResult _ remaining_str _ => remaining_str
| OneLexSpecNoToken _ _ remaining_str _ => remaining_str
| OneLexSpecError _ remaining_str _ => remaining_str
| OneLexImplementationError _ remaining_str p => remaining_str
| OneLexNoMatchErrorResult remaining_str p => remaining_str
| OneLexLoop remaining_str p => remaining_str
(* | OneLexNoConsumeWT _ remaining_str p => remaining_str
| OneLexNoConsumeEmpty remaining_str p => remaining_str *)
end.

(* Definition hasConsumed {Token : Set} (o : OneLexResult(Token:=Token)) := match o with
| OneLexNoMatchErrorResult remaining_str p => false
| OneLexNoConsumeWT _ _ _ => false
| OneLexNoConsumeEmpty _ _ => false
| _ => true
end. *)

Definition positionLE sp ep :=
  ( (abs_pos sp) <= (abs_pos ep)) /\ ((l_number sp) < (l_number ep) \/ ((l_number sp) = (l_number ep) /\ (c_number sp) <= (c_number ep))).

Lemma positionLE_trans : forall a b c, positionLE a b -> positionLE b c -> positionLE a c.
Proof.
unfold positionLE.
induction a, b, c.
simpl.
lia.
Qed.

Lemma positionLE_ident : forall a, positionLE a a.
Proof.
induction a.
unfold positionLE.
lia.
Qed.

Record RecLexer {Token Hist : Set} : Set := mkRecLexer
 {  lexer : (string -> Position -> Hist -> OneLexResult (Token := Token) * Hist);
    
    lexer_start_cur_position : forall str_to_lex param_pos history nhistory r
      ,
      (lexer str_to_lex param_pos history = (r, nhistory)) -> positionLE param_pos (extractCurrentPosition r)
    
    ;lexer_tok_position : forall str_to_lex param_pos history nhistory ts_pos tok cur_pos tok_str_val
      remaining_str,
      (lexer str_to_lex param_pos history = (OneLexSResult
               {|
               token := {|
                        s_pos := ts_pos;
                        tok := tok;
                        str_val := tok_str_val |};
               cur_pos := cur_pos;
               remaining_str := remaining_str; |}, nhistory)) -> positionLE ts_pos cur_pos

    ;lexer_start_tok_position : forall str_to_lex param_pos history nhistory ts_pos tok cur_pos tok_str_val
      remaining_str,
      (lexer str_to_lex param_pos history = (OneLexSResult
               {|
               token := {|
                        s_pos := ts_pos;
                        tok := tok;
                        str_val := tok_str_val |};
               cur_pos := cur_pos;
               remaining_str := remaining_str; |}, nhistory)) -> positionLE param_pos ts_pos

    ;lexer_start_cur_position_abs : forall str_to_lex param_pos history nhistory r
      ,
      (lexer str_to_lex param_pos history = (r, nhistory)) -> abs_pos (extractCurrentPosition r) = abs_pos param_pos + ((String.length str_to_lex) - (String.length (extractRemainingString r)))


    ;lexer_correct_consum : forall str_to_lex param_pos history nhistory r
      ,
      (lexer str_to_lex param_pos history = (r, nhistory)) -> extractRemainingString r = ignore_nfirst_char ((abs_pos (extractCurrentPosition r)) - (abs_pos param_pos)) str_to_lex

    ;lexer_no_implementation_error : forall str ncur_pos nhist n history' ncur_pos' rem, lexer str ncur_pos nhist = (OneLexImplementationError n rem ncur_pos', history') -> False

    ; lexer_start_interruption_position : forall str_to_lex param_pos history nhistory ts_pos cur_pos tok_str_val
      remaining_str,
      lexer str_to_lex param_pos history = (OneLexSpecNoToken tok_str_val ts_pos remaining_str cur_pos, nhistory) -> positionLE param_pos ts_pos

    ; lexer_start_interruption_position2 : forall str_to_lex param_pos history nhistory ts_pos cur_pos tok_str_val
      remaining_str,
      lexer str_to_lex param_pos history = (OneLexSpecNoToken tok_str_val ts_pos remaining_str cur_pos, nhistory) -> positionLE ts_pos cur_pos

    (* ;lexer_dec_str : forall a str_to_lex param_pos history nhistory
      r,
      (lexer (String a str_to_lex) param_pos history = (r, nhistory)) -> hasConsumed r = true -> String.length (extractRemainingString r) < String.length (String a str_to_lex)
    ;will_consume : string -> Position -> Hist -> bool

    ;will_consume_true : forall str_to_lex param_pos history nhistory
      r, will_consume str_to_lex param_pos history = true -> lexer str_to_lex param_pos history = (r, nhistory) -> String.length (extractRemainingString r) < String.length str_to_lex

    ;will_consume_false_rem_str : forall str_to_lex param_pos history nhistory
      r,
      will_consume str_to_lex param_pos history = false -> (lexer str_to_lex param_pos history = (r, nhistory)) -> (extractRemainingString r) = str_to_lex*)
}.

Record PosChanger : Set := mkPosChanger
{  
  changer : Position -> Position;
  changer_correct_le : forall a, positionLE a (changer a);
  changer_correct_abs : forall a, abs_pos a = abs_pos (changer a)
}.

Inductive AtomicAction {Token Hist : Set} : Set :=
| HistoryHandler : (string -> Position -> option Token -> string -> Position -> Hist -> Hist) -> AtomicAction
| AnotherLexer : RecLexer (Token := Token) (Hist := Hist) -> AtomicAction
| PosHandler : PosChanger -> AtomicAction
| TokenReturn : (string -> Position -> option Token -> string -> Position -> Hist -> (Result (Token := Token) * Hist)) -> AtomicAction
| SelfRec : AtomicAction.

Definition Action {Token Hist : Set} : Set := list (AtomicAction (Token := Token) (Hist := Hist)).

(*Fixpoint recomputePositionAndHistory {Token Hist : Set} (l : Action) matched_str cur_pos hist : Position * Hist * Action (Token := Token) (Hist := Hist) := match l with
| [] => (cur_pos, hist, [])
| (HistoryHandler hf)::t => recomputePositionAndHistory t matched_str cur_pos (hf matched_str cur_pos hist)
| (PosHandler pf)::t => recomputePositionAndHistory t matched_str ((changer pf) cur_pos) hist
| h::t => (cur_pos, hist, l)
end.

Lemma recomputePositionAndHistoryPosLE {Token Hist : Set} : forall l mstr cpos hist, positionLE cpos (fst (fst (recomputePositionAndHistory (Token := Token) (Hist := Hist) l mstr cpos hist))).
Proof.
induction l; simpl; intros.
apply positionLE_ident.
induction a.
apply IHl.
simpl; apply positionLE_ident.
eapply (positionLE_trans cpos (changer p cpos)).
apply changer_correct_le.
apply IHl.
simpl; apply positionLE_ident.
simpl; apply positionLE_ident.
Qed.

Lemma recomputePositionAndHistoryLDec {Token Hist : Set} : forall l mstr cpos hist npos nhist nh nt, recomputePositionAndHistory (Token := Token) (Hist := Hist) l mstr cpos hist = (npos, nhist, nh::nt) -> List.length nt < List.length l.
Proof.
induction l; simpl.
intros.
inversion H.
intros.
case_eq a.
intros.
rewrite H0 in H.
apply IHl in H; lia.
intros.
rewrite H0 in H.
inversion H; lia.
intros.
rewrite H0 in H.
apply IHl in H; lia.
intros.
rewrite H0 in H.
inversion H; lia.
intros.
rewrite H0 in H.
inversion H; lia.
Qed.*)

Record ElectionResult {Action : Set} : Set := mkElectionResult
{
   resultRegex : RegExp
  ;resultAction : Action
  ;resultNat : nat
}.

(* Definition computeScores {Action : Set} RegexpXAction_list str : list (ElectionResult (Action := Action)) := List.map (fun (re_ac : RegExp * Action ) => let (re, ac) := re_ac in mkElectionResult Action re ac (match match_len re str with | None => 0 | Some n => n end) ) RegexpXAction_list. *)

(* Fixpoint electCandidate {Action : Set} (electionResultList: list (ElectionResult (Action := Action))) := match electionResultList with
| [] => None
| h::t => (match electCandidate t with
            | None => Some h
            | Some c => Some (if Nat.ltb (resultNat h) (resultNat c) then c else h)
          end)
end. *)

Fixpoint electCandidate {Action : Set} RegexpXAction_list str := match RegexpXAction_list with
| [] => None
| (re, ac)::t => (match match_len re str with 
            | None => electCandidate t str
            | Some n => (match electCandidate(Action:=Action) t str with
                        | Some c => Some (if Nat.ltb n (resultNat c) then c else (mkElectionResult Action re ac n) )
                        | None => Some (mkElectionResult Action re ac n)
                        end)
          end)
end.

(* Lemma computeScores_resultNat_inf_strlen {Action : Set}: forall regexp_to_action str, forall (e : (ElectionResult (Action := Action)) ), In e (computeScores regexp_to_action str) -> resultNat e <= String.length str.
Proof.
intro.
induction regexp_to_action.
simpl.
intros.
destruct H.
intros.
apply in_inv in H.
destruct H.
induction a.
rewrite <- H.
case_eq (match_len a str).
intros.
rewrite H0 in H.
simpl.
eapply matchlen_inf; eauto.
intros.
rewrite H0 in H.
simpl.
lia.
auto.
Qed. *)

Lemma electCandidate_isMember {Action : Set}: forall l str (e : (ElectionResult (Action := Action)) ), electCandidate l str = Some e -> In (resultRegex e, resultAction e) l.
Proof.
induction l.
discriminate.
simpl.
induction a.
intro.
case_eq (match_len a str); intro.
case_eq (electCandidate l str).
intro.
case_eq (n <? resultNat e).
intros.
inversion H2.
rewrite H4 in *.
apply IHl in H0.
auto.
intros.
inversion H2.
auto.
intros.
inversion H1.
auto.
intros.
apply IHl in H0; auto.
Qed.

Lemma electCandidate_resultNat_inf_strlen {Action : Set} : forall regexp_to_action str (e : (ElectionResult (Action := Action)) ), electCandidate regexp_to_action str = Some e -> resultNat e <= String.length str.
Proof.
induction regexp_to_action; simpl; try discriminate.
induction a.
intro.
case_eq (match_len a str).
case_eq (electCandidate regexp_to_action str).
intros e H n.
case_eq (n <? resultNat e).
intros.
inversion H2.
rewrite H4 in *.
apply IHregexp_to_action in H; auto.
intros.
apply matchlen_inf in H1.
inversion H2; simpl; auto.
intros.
apply matchlen_inf in H0.
inversion H1; simpl; auto.
intros.
apply IHregexp_to_action in H0; auto.
Qed.

Lemma electCandidateSome {Action : Set}: forall l str c, electCandidate (Action:=Action) l str = Some c -> match_len (resultRegex c) str = Some (resultNat c).
Proof.
induction l.
simpl.
discriminate.
simpl.
induction a.
intro.
case_eq (match_len a str).
intros n H c.
case_eq (electCandidate l str).
intro.
induction (n <? resultNat e).
intros.
inversion H1.
rewrite H3 in H0.
apply IHl; auto.
intros.
inversion H1; simpl; auto.
intros.
inversion H1; simpl; auto.
intros.
apply IHl; auto.
Qed.

Lemma electCandidateNone {Action : Set}: forall l str, electCandidate (Action:=Action) l str = None <-> (forall re ac, In (re, ac) l -> match_len re str = None).
Proof.
split.
induction l.
simpl; intros.
inversion H0.
intros.
simpl in H.
induction a.
case_eq (match_len a str).
intros.
rewrite H1 in H.
induction (electCandidate l str); inversion H.
intros.
rewrite H1 in H.
inversion H0.
inversion H2.
rewrite H4 in *; auto.
eapply IHl; eauto.
intros.
induction l; simpl; auto.
induction a.
assert (match_len a str = None).
apply (H a b); simpl; auto.
rewrite H0.
apply IHl.
intros.
assert (In (re, ac) ((a, b) :: l)).
simpl; auto.
eapply H; eauto.
Qed.


Lemma electCandidate_max {Action : Set}: forall l str h, electCandidate (Action:=Action) l str = Some h -> (forall re ac n, In (re, ac) l -> match_len re str = Some n -> (resultNat h) >= n).
Proof.
induction l.
discriminate.
intros.
simpl in H.
induction a.
case_eq (match_len a str).
intros.
rewrite H2 in H.
case_eq (electCandidate l str).
intros.
apply in_inv in H0.
destruct H0.
rewrite H3 in H.
case_eq (n0 <? resultNat e).
intros.
rewrite H4 in H.
inversion H.
inversion H0.
rewrite H6 in *.
rewrite H7 in *.
rewrite H1 in H2.
inversion H2.
apply Nat.ltb_lt in H4; lia.
intros.
rewrite H4 in H.
inversion H.
simpl.
inversion H0.
rewrite H7 in *.
rewrite H1 in H2.
inversion H2.
auto.
rewrite H3 in H.
case_eq (n0 <? resultNat e).
intros.
rewrite H4 in H.
inversion H.
rewrite H6 in *.
eapply IHl; eauto.
intros.
rewrite H4 in H.
inversion H.
simpl.
apply Nat.ltb_ge in H4.
assert (resultNat e >= n).
eapply IHl; eauto.
lia.
intros.
apply in_inv in H0.
destruct H0.
inversion H0.
rewrite H5 in *.
rewrite H2 in *.
inversion H1.
rewrite H7 in *.
rewrite H3 in H.
inversion H.
simpl; auto.
assert (match_len re str = None).
eapply electCandidateNone; eauto.
rewrite H4 in *.
inversion H1.
intros.
induction H0.
inversion H0.
rewrite H4 in *.
rewrite H2 in *.
inversion H1.
rewrite H2 in H.
eapply IHl; eauto.
Qed.


Definition election {Action : Set} regexp_to_action str := electCandidate (Action := Action) regexp_to_action str.

Lemma election_inf_strLen {Action : Set} : forall str regexp_to_action e, election (Action := Action) regexp_to_action str = Some e -> resultNat e <= String.length str.
Proof.
unfold election.
intros.
apply electCandidate_resultNat_inf_strlen in H; auto.
Qed.

Definition regexp_separator r c := forall s s', match_len r s = match_len r (s ++ (String c s')).

Definition lexer_separator {Action : Set} regexp_to_action c := forall r (a : Action), In (r, a) regexp_to_action -> regexp_separator r c.

Lemma election_matchesNotNone {Action : Set} : forall s e regexp_to_action, election (Action := Action) regexp_to_action s = Some e -> (exists l, match_len (resultRegex e) s = Some l).
Proof.
intros.
unfold election in H.
apply electCandidateSome in H.
exists (resultNat e); auto.
Qed.

Lemma election_matches {Action : Set} : forall s e regexp_to_action, election (Action := Action) regexp_to_action s = Some e -> (exists r a, In (r, a) regexp_to_action /\ match_len r s = Some (resultNat e)).
Proof.
intros.
assert (H' := H).
exists (resultRegex e).
exists (resultAction e).
unfold election in H.
apply electCandidate_isMember in H.
apply electCandidateSome in H'.
auto.
Qed.


Lemma matchesNotNone_election {Action : Set} : forall s e l regexp_to_action, match_len (resultRegex e) s = Some l -> In (resultRegex e, resultAction e) regexp_to_action  -> (exists e', election (Action := Action) regexp_to_action s = Some e') .
Proof.
intros.
case_eq (election regexp_to_action s); intros.
exists e0; auto.
unfold election in H1.
assert (forall (re : RegExp) (ac : Action),
   In (re, ac) regexp_to_action -> match_len re s = None).
apply electCandidateNone; auto.
apply H2 in H0.
rewrite H0 in H.
inversion H.
Qed.

Lemma election_cons {Action : Set} : forall a regexp_to_action str, election (Action := Action) (a :: regexp_to_action) str = None -> election regexp_to_action str = None.
Proof.
intros.
unfold election in *.
simpl in H.
induction a.
induction (match_len a str).
induction (electCandidate regexp_to_action str); inversion H.
auto.
Qed.


Lemma election_None_equiv {Action : Set} : forall str regexp_to_action, (forall e a, In (e, a) regexp_to_action -> match_len e str = None) <-> election(Action := Action) regexp_to_action str = None.
Proof.
split.
intros.
unfold election.
eapply electCandidateNone; eauto.
unfold election.
intros.
eapply electCandidateNone; eauto.
Qed.

Lemma election_S {Action : Set} : forall str a regexp_to_action e e', election (Action := Action) (a :: regexp_to_action) str = Some e -> election regexp_to_action str = Some e' -> (resultNat e') <= (resultNat e).
Proof.
intros.
unfold election in H, H0.
induction a.
simpl in H.
case_eq (match_len a str); intros ; rewrite H1 in H.
rewrite H0 in H.
case_eq (n <? resultNat e'); intros; rewrite H2 in H.
inversion H; auto.
inversion H; auto; simpl.
apply Nat.ltb_ge in H2; auto.
rewrite H0 in H.
inversion H; auto.
Qed.

Lemma election_Some_max_equiv {Action : Set} : forall regexp_to_action str e, election(Action := Action) regexp_to_action str = Some e ->
(forall r a v, In (r, a) regexp_to_action -> match_len r str = Some v -> v <= (resultNat e)).
Proof.
induction regexp_to_action.
intros.
inversion H0.
simpl.
induction a.
intro.
case_eq (match_len a str).
intro.
case_eq (election regexp_to_action str).
intro.
case_eq (n <? resultNat e).
intros.
inversion H2.
rewrite H6 in *.
apply Nat.ltb_lt in H; auto.
destruct H3.
inversion H3.
rewrite H7 in *.
rewrite H4 in H1.
inversion H1; lia.
eapply IHregexp_to_action; eauto.
intros.
apply Nat.ltb_ge in H; auto.
inversion H3.
inversion H5.
rewrite H7 in *.
rewrite H4 in H1.
inversion H1.
inversion H2.
auto.
eapply IHregexp_to_action in H0; eauto.
inversion H2.
simpl.
lia.
intros.
destruct H2.
inversion H2.
rewrite H5 in *.
rewrite H3 in *.
inversion H1.
simpl.
inversion H0.
auto.
unfold election in *.
assert (forall (re : RegExp) (ac : Action), In (re, ac) regexp_to_action -> match_len re str = None).
apply electCandidateNone; auto.
assert (match_len r str = None).
eapply H4; eauto.
rewrite H5 in H3.
inversion H3.
intros.
inversion H1.
inversion H3.
rewrite H5 in *.
rewrite H2 in H.
inversion H.
eapply IHregexp_to_action; eauto.
Qed.


Lemma election_Some_Priority {Action : Set} : forall str r a regexp_to_action e l, election (Action := Action) regexp_to_action str = Some e -> match_len r str = Some l -> (resultNat e) <= l -> election ((r, a)::regexp_to_action) str = Some {|resultRegex := r; resultAction := a; resultNat := l|}.
Proof.
intros.
simpl.
rewrite H.
rewrite H0.
apply Nat.ltb_ge in H1; auto.
rewrite H1.
auto.
Qed.

Lemma election_Some_Priority2 {Action : Set} : forall str r a regexp_to_action e l, election (Action := Action) regexp_to_action str = Some e -> match_len r str = Some l -> (resultNat e) > l -> election ((r, a)::regexp_to_action) str = Some e.
Proof.
intros.
simpl.
rewrite H0.
rewrite H.
assert ( l < resultNat e) by lia.
apply Nat.ltb_lt in H2; auto.
rewrite H2; auto.
Qed.

Lemma election_concat {Action : Set} : forall regexp_to_action s s' e, election regexp_to_action s = Some e -> (exists e', election (Action := Action) regexp_to_action (s ++ s') = Some e').
Proof.
induction regexp_to_action; simpl.
discriminate.
induction a.
intros s s'.
case_eq (match_len a s).
intros n H.
case_eq (match_len a (s ++ s')).
intros n0 H0.
eapply (matchlen_concat_croiss s s' n n0) in H; auto.
case_eq (election regexp_to_action s); intros.
apply (IHregexp_to_action s s') in H1.
destruct H1.
rewrite H1.
induction (n0 <? resultNat x).
exists x; auto.
exists ({| resultRegex := a; resultAction := b; resultNat := n0 |}); auto.
induction (election regexp_to_action (s ++ s')).
induction (n0 <? resultNat a0).
exists a0; auto.
exists ({| resultRegex := a; resultAction := b; resultNat := n0 |}) ;auto.
exists ({| resultRegex := a; resultAction := b; resultNat := n0 |}) ;auto.
intros.
apply matchlen_concat2 in H0.
rewrite H0 in H.
inversion H.
intros.
apply (IHregexp_to_action s s') in H0.
destruct H0.
rewrite H0.
induction (match_len a (s ++ s')).
exists (if a0 <? resultNat x
     then x
     else {| resultRegex := a; resultAction := b; resultNat := a0 |}); auto.
exists x; auto.
Qed.

Lemma election_concat2 {Action : Set} : forall s s' regexp_to_action, election (Action := Action) regexp_to_action (s ++ s') = None -> election regexp_to_action s = None.
Proof.
intros.
case_eq (election regexp_to_action s); auto.
intros.
apply (election_concat regexp_to_action s s' e) in H0.
destruct H0.
rewrite H in H0.
inversion H0.
Qed.

Lemma election_separator {Action : Set} : forall regexp_to_action s s' c, lexer_separator regexp_to_action c -> election (Action := Action) regexp_to_action s = election regexp_to_action (s ++ (String c s')).
Proof.
induction regexp_to_action; simpl; auto.
induction a.
intros.
assert (H':=H).
unfold lexer_separator in H.
unfold regexp_separator in H.
assert (match_len a s = match_len a (s ++ String c s')).
apply (H a b); auto.
simpl; auto.
rewrite H0.
case_eq (match_len a (s ++ String c s')).
intros.
assert (lexer_separator regexp_to_action c).
unfold lexer_separator.
intros.
unfold regexp_separator.
eapply (H r a0).
simpl; auto.
apply (IHregexp_to_action s s') in H2.
rewrite H2.
auto.
intros.
assert (lexer_separator regexp_to_action c).
unfold lexer_separator.
intros.
unfold regexp_separator.
eapply (H r a0).
simpl; auto.
apply IHregexp_to_action; auto.
Qed.

Require Import Recdef Coq.Program.Wf.

(*Inductive recomputeResult {Token Hist : Set} :=
| Ok : Position -> Hist -> Action (Token := Token) (Hist := Hist) -> recomputeResult
| ErrUserDef : string -> Position -> Hist -> recomputeResult
(* | ErrNoTok : string -> Position -> string -> Position -> Hist -> recomputeResult *)
| ErrSpecErr : string -> Position -> Hist -> recomputeResult
| ErrImplError : nat -> Position -> Hist -> recomputeResult
| ErrNoMatchErr : Position -> Hist -> recomputeResult
| ErrLoop : Position -> Hist -> recomputeResult
(* | ErrLocaImplError : nat -> Position -> Hist -> recomputeResult *)
.*)

(* Definition isStopError {Token : Set} (o : OneLexResult(Token:=Token)) := match o with
| OneLexSResult _ => false
| OneLexUserDefinitionErrorResult _ _ p => true
| OneLexSpecNoToken _ _ _ p => false
| OneLexSpecError _ _ p => true
| OneLexImplementationError _ _ p => true
| OneLexNoMatchErrorResult _ p => true
| OneLexLoop _ p => true
| OneLexNoConsumeWT _ _ p => false
| OneLexNoConsumeEmpty _ p => false
end. *)

Fixpoint semiActionCompute {Token Hist : Set} (l : Action) matched_str cur_pos hist rem_str token_option start_pos : OneLexResult (Token := Token) * Hist * Action := match l with
| [] => (OneLexSpecNoToken matched_str start_pos rem_str cur_pos, hist, [])
| (HistoryHandler hf)::t => semiActionCompute t matched_str cur_pos (hf matched_str start_pos token_option rem_str cur_pos hist) rem_str token_option start_pos
| (PosHandler pf)::t => semiActionCompute t matched_str ((changer pf) cur_pos) hist rem_str token_option start_pos
| (TokenReturn f)::nil => (match f matched_str start_pos token_option rem_str cur_pos hist with
                          | (ResultOk t, nh) => (OneLexSResult {| 
                                      token := {|s_pos := start_pos; 
                                        tok := t; 
                                        str_val := matched_str |}; 
                                      cur_pos := cur_pos ; 
                                      remaining_str := rem_str |}, nh, [])
                          | (ResultError msg, nh) => (OneLexUserDefinitionErrorResult msg rem_str cur_pos, nh, (TokenReturn f)::[])
                          end)
| (TokenReturn f)::t => (match f matched_str start_pos token_option rem_str cur_pos hist with
                          | (ResultOk tok, nhist) => semiActionCompute t matched_str cur_pos nhist rem_str (Some tok) start_pos
                          | (ResultError msg, nhist) => (OneLexUserDefinitionErrorResult msg rem_str cur_pos, nhist, (TokenReturn f)::t)
                        end)
| (AnotherLexer lex)::nil => (match (lexer lex) rem_str cur_pos hist with
                                  | (OneLexSResult res, nh) => (OneLexSResult res, nh, [])
                                  | (OneLexSpecNoToken st p st0 p0, nh) => (OneLexSpecNoToken st p st0 p0, nh, [])
                                  | (res, nh) => (res, nh, (AnotherLexer lex)::nil)
                                end)
| (AnotherLexer lex)::t => (match (lexer lex) rem_str cur_pos hist with
                                  | (OneLexSResult {| 
                                    token := {|
                        s_pos := s_pos;
                        tok := tok;
                        str_val := mstr |}; 
                                    cur_pos := ncur_pos ; 
                                    remaining_str := rem_str' |}, nh) => semiActionCompute t mstr ncur_pos nh rem_str' (Some tok) s_pos
                                  | (OneLexSpecNoToken st p st0 p0, nh) => semiActionCompute t st p0 nh st0 None p
                                  | (res, nh) => (res, nh, (AnotherLexer lex)::t)
                            end)
| SelfRec::t => (OneLexSpecNoToken matched_str start_pos rem_str cur_pos, hist, SelfRec::t)
end.

Lemma semiActionCompute_start_cur_position {Token Hist : Set} : forall l mstr cpos hist lexr histr actr rem_str tok_op sp, semiActionCompute (Token := Token) (Hist := Hist) l mstr cpos hist rem_str tok_op sp = (lexr, histr, actr) ->  positionLE cpos (extractCurrentPosition lexr).
Proof.
unfold extractCurrentPosition.
induction l; simpl; intros.
inversion H.
apply positionLE_ident.
induction a.
eapply IHl; eauto.
case_eq (lexer r rem_str cpos hist); intros; rewrite H0 in *; apply lexer_start_cur_position in H0. 
case_eq l; intros; rewrite H1 in H.
induction o.
inversion H.
induction o; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
induction o.
induction o.
induction token0.
rewrite <- H1 in H.
simpl in *.
eapply IHl in H; eauto.
eapply positionLE_trans; eauto.
inversion H; simpl in *; auto.
rewrite <- H1 in H.
simpl in *.
eapply IHl in H; eauto.
eapply positionLE_trans; eauto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
eapply IHl in H; eauto.
eapply positionLE_trans; eauto.
apply changer_correct_le.
case_eq l; intros; rewrite H0 in H.
induction (p mstr sp tok_op rem_str cpos hist).
induction a; inversion H; apply positionLE_ident.
induction (p mstr sp tok_op rem_str cpos hist).
rewrite <- H0 in H.
induction a0.
eapply IHl in H; eauto.
inversion H; simpl in *; apply positionLE_ident.
inversion H; simpl in *; apply positionLE_ident.
Qed.

Lemma semiActionCompute_tok_position {Token Hist : Set} : forall l mstr cpos hist histr actr rem_str tok_op sp ts_pos tok cur_pos tok_str_val
      remaining_str, semiActionCompute (Token := Token) (Hist := Hist) l mstr cpos hist rem_str tok_op sp = (OneLexSResult
               {|
               token := {|
                        s_pos := ts_pos;
                        tok := tok;
                        str_val := tok_str_val |};
               cur_pos := cur_pos;
               remaining_str := remaining_str; |}, histr, actr) ->  positionLE sp cpos -> positionLE ts_pos cur_pos.
Proof.
induction l; simpl; intros; rename H0 into H'.
inversion H.
induction a.
eapply IHl; eauto.
case_eq (lexer r rem_str cpos hist); intros; rewrite H0 in *.
induction o.
induction o.
induction token0.
apply lexer_tok_position in H0. 
case_eq l; intros; rewrite H1 in H.
inversion H.
rewrite H3 in *.
rewrite H6 in *; auto.
rewrite <- H1 in *.
eapply IHl; eauto.
induction l; inversion H.
case_eq l; intros; rewrite H1 in H.
inversion H.
rewrite <- H1 in *.
eapply IHl in H; eauto.
apply lexer_start_interruption_position2 in H0; auto.
induction l; inversion H.
induction l; inversion H.
induction l; inversion H.
induction l; inversion H.
eapply IHl; eauto.
eapply positionLE_trans; eauto.
apply changer_correct_le.
case_eq l; intros; rewrite H0 in H.
induction (p mstr sp tok_op rem_str cpos hist).
induction a; inversion H.
rewrite H2 in *.
rewrite H5 in *; auto.
induction (p mstr sp tok_op rem_str cpos hist).
rewrite <- H0 in H.
induction a0.
eapply IHl in H; eauto.
inversion H. 
inversion H.
Qed.

Lemma semiActionCompute_start_tok_position {Token Hist : Set} : forall l mstr cpos hist histr actr rem_str tok_op sp ts_pos tok cur_pos tok_str_val
      remaining_str, semiActionCompute (Token := Token) (Hist := Hist) l mstr cpos hist rem_str tok_op sp = (OneLexSResult
               {|
               token := {|
                        s_pos := ts_pos;
                        tok := tok;
                        str_val := tok_str_val |};
               cur_pos := cur_pos;
               remaining_str := remaining_str; |}, histr, actr) -> positionLE sp cpos -> positionLE sp ts_pos.
Proof.
induction l; simpl; intros; rename H0 into H'.
inversion H.
induction a.
eapply IHl; eauto.
case_eq (lexer r rem_str cpos hist); intros; rewrite H0 in *.
induction o.
induction o.
induction token0. 
case_eq l; intros; rewrite H1 in H.
inversion H.
apply lexer_start_tok_position in H0.
rewrite H3 in *.
eapply positionLE_trans; eauto.
rewrite <- H1 in *.
eapply IHl in H; eauto.
apply lexer_start_tok_position in H0.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
apply lexer_tok_position in H0; auto.
induction l; inversion H.
case_eq l; intros; rewrite H1 in H.
inversion H.
rewrite <- H1 in *.
eapply IHl in H; eauto.
apply lexer_start_interruption_position in H0; auto.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
apply lexer_start_interruption_position2 in H0; auto.
induction l; inversion H.
induction l; inversion H.
induction l; inversion H.
induction l; inversion H.
eapply IHl in H; eauto.
eapply positionLE_trans; eauto.
apply changer_correct_le.
case_eq l; intros; rewrite H0 in H.
induction (p mstr sp tok_op rem_str cpos hist).
induction a; inversion H.
apply positionLE_ident.
induction (p mstr sp tok_op rem_str cpos hist).
rewrite <- H0 in H.
induction a0.
eapply IHl in H; eauto.
inversion H. 
inversion H.
Qed.

Lemma lexer_dec_str_eq {Token Hist: Set} : forall str_to_lex param_pos (history nhistory : Hist)
      (r0 : RecLexer(Token := Token) (Hist := Hist)) r ,
      (lexer r0) str_to_lex param_pos history = (r, nhistory) -> String.length (extractRemainingString r) <= String.length str_to_lex.
Proof.
intros.
apply lexer_correct_consum in H.
rewrite H.
apply ignore_dec_length.
Qed.

Lemma semiActionCompute_dec_str_eq {Token Hist : Set} : forall l mstr cpos hist lexr histr actr rem_str tok_op sp, semiActionCompute (Token := Token) (Hist := Hist) l mstr cpos hist rem_str tok_op sp = (lexr, histr, actr) ->  String.length (extractRemainingString lexr) <= String.length rem_str.
Proof.
induction l; simpl; intros.
inversion H.
simpl; auto.
induction a.
eapply IHl; eauto.
case_eq (lexer r rem_str cpos hist); intros; rewrite H0 in *; apply lexer_dec_str_eq in H0. 
case_eq l; intros; rewrite H1 in H.
induction o; inversion H; auto.
induction o.
induction o.
induction token0.
rewrite <- H1 in H.
eapply IHl in H; eauto.
simpl in H0.
lia.
inversion H; simpl in *; auto.
rewrite <- H1 in H.
simpl in *.
eapply IHl in H; eauto.
lia.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
eapply IHl in H; eauto.
case_eq l; intros; rewrite H0 in H.
induction (p mstr sp tok_op rem_str cpos hist).
induction a; inversion H; simpl in *; auto.
induction (p mstr sp tok_op rem_str cpos hist).
rewrite <- H0 in H.
induction a0.
eapply IHl in H; eauto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
Qed.

Lemma semiActionCompute_start_cur_position_abs {Token Hist : Set} : forall l mstr cpos hist lexr histr actr rem_str tok_op sp, semiActionCompute (Token := Token) (Hist := Hist) l mstr cpos hist rem_str tok_op sp = (lexr, histr, actr) ->  abs_pos (extractCurrentPosition lexr) = abs_pos cpos + ((String.length rem_str) - (String.length (extractRemainingString lexr))).
Proof.
unfold extractCurrentPosition.
induction l; simpl; intros.
inversion H; simpl; lia.
induction a.
eapply IHl; eauto.
case_eq (lexer r rem_str cpos hist); intros; rewrite H0 in *; assert (H0':=H0); apply lexer_start_cur_position_abs in H0. 
case_eq l; intros; rewrite H1 in H.
induction o.
inversion H.
induction o; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
induction o.
induction o.
induction token0.
rewrite <- H1 in H.
simpl in H0.
assert (H':=H).
apply lexer_dec_str_eq in H0'; simpl in H0'.
apply semiActionCompute_dec_str_eq in H'; simpl in H'.
eapply IHl in H; eauto.
induction lexr.
induction o.
simpl in *.
rewrite H0 in *.
rewrite H.
lia.
rewrite H.
rewrite H0.
simpl in *.
lia.
rewrite H; rewrite H0; simpl in *; lia.
rewrite H; rewrite H0; simpl in *; lia.
rewrite H; rewrite H0; simpl in *; lia.
rewrite H; rewrite H0; simpl in *; lia.
rewrite H; rewrite H0; simpl in *; lia.
inversion H.
auto.
rewrite <- H1 in H.
assert (H':=H).

apply lexer_dec_str_eq in H0'; simpl in H0'.
apply semiActionCompute_dec_str_eq in H'; simpl in H'.
eapply IHl in H; eauto.
induction lexr.
induction o.
simpl in *.
rewrite H0 in *.
rewrite H.
lia.
simpl in *.
rewrite H.
rewrite H0.
lia.
rewrite H; simpl in H0; rewrite H0; simpl in *; lia.
rewrite H; simpl in H0; rewrite H0; simpl in *; lia.
rewrite H; simpl in H0; rewrite H0; simpl in *; lia.
rewrite H; simpl in H0; rewrite H0; simpl in *; lia.
rewrite H; simpl in H0; rewrite H0; simpl in *; lia.
inversion H.
auto.
inversion H; auto.
inversion H; auto.
inversion H; auto.
eapply IHl in H; eauto.
rewrite H.
rewrite <- changer_correct_abs; auto.
case_eq l; intros; rewrite H0 in H.
induction (p mstr sp tok_op rem_str cpos hist).
induction a; inversion H. 
simpl; lia.
simpl; lia.
induction (p mstr sp tok_op rem_str cpos hist).
rewrite <- H0 in H.
induction a0.
eapply IHl in H; eauto.
inversion H; simpl in *; lia.
inversion H; simpl in *; lia.
Qed.

Lemma ignore_usefull : forall str n n', (ignore_nfirst_char n (ignore_nfirst_char n' str)) = (ignore_nfirst_char (n + n') str).
Proof.
unfold ignore_nfirst_char.
induction str, n, n'; simpl; auto.
f_equal.
rewrite <- substr_0_len_str; auto.
apply IHstr.
replace (n + 0) with n by lia.
f_equal.
rewrite substr_0_len_str; auto.
apply substr_0_len_str.
rewrite IHstr.
f_equal.
lia.
lia.
Qed.

Lemma semiActionCompute_correct_consum {Token Hist : Set} : forall l mstr cpos hist lexr histr actr rem_str tok_op sp, semiActionCompute (Token := Token) (Hist := Hist) l mstr cpos hist rem_str tok_op sp = (lexr, histr, actr) ->  extractRemainingString lexr = ignore_nfirst_char ((abs_pos (extractCurrentPosition lexr)) - (abs_pos cpos)) rem_str.
Proof.
induction l; simpl; intros.
inversion H; simpl.
replace (abs_pos cpos - abs_pos cpos) with 0 by lia.
unfold ignore_nfirst_char.
replace (String.length rem_str - 0) with (String.length rem_str) by lia.
rewrite substr_0_len_str; auto.
induction a.
eapply IHl; eauto.
case_eq (lexer r rem_str cpos hist); intros; rewrite H0 in *; assert (H0':=H0); apply lexer_correct_consum in H0. 
case_eq l; intros; rewrite H1 in H.
induction o.
inversion H.
induction o; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
induction o.
induction o.
induction token0.
rewrite <- H1 in H.
simpl in *.
assert (H':=H).
eapply IHl in H; eauto.
rewrite H.
rewrite H0.
rewrite ignore_usefull.
apply lexer_start_cur_position_abs in H0'; simpl in H0'.
apply semiActionCompute_start_cur_position_abs in H'; simpl in H'.
f_equal.
lia.
inversion H.
simpl in *; auto.
rewrite <- H1 in H.
assert (H':=H).
eapply IHl in H; eauto.
simpl in *.
rewrite H0 in H.
rewrite ignore_usefull in H.
apply lexer_start_cur_position_abs in H0'; simpl in H0'.
apply semiActionCompute_start_cur_position_abs in H'; simpl in H'.
rewrite H.
f_equal.
lia.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
apply IHl in H.
rewrite <- changer_correct_abs in H; auto.
case_eq l; intros; rewrite H0 in H.
induction (p mstr sp tok_op rem_str cpos hist).
induction a; inversion H; simpl in *. 
replace (abs_pos cpos - abs_pos cpos) with 0 by lia.
unfold ignore_nfirst_char.
replace (String.length rem_str - 0) with (String.length rem_str) by lia.
rewrite substr_0_len_str; auto.
replace (abs_pos cpos - abs_pos cpos) with 0 by lia.
unfold ignore_nfirst_char.
replace (String.length rem_str - 0) with (String.length rem_str) by lia.
rewrite substr_0_len_str; auto.
induction (p mstr sp tok_op rem_str cpos hist).
rewrite <- H0 in H.
induction a0.
eapply IHl in H; eauto.
inversion H; simpl in *.
replace (abs_pos cpos - abs_pos cpos) with 0 by lia.
unfold ignore_nfirst_char.
replace (String.length rem_str - 0) with (String.length rem_str) by lia.
rewrite substr_0_len_str; auto.
inversion H; simpl in *.
replace (abs_pos cpos - abs_pos cpos) with 0 by lia.
unfold ignore_nfirst_char.
replace (String.length rem_str - 0) with (String.length rem_str) by lia.
rewrite substr_0_len_str; auto.
Qed.

Lemma semiActionCompute_no_implementation_error {Token Hist : Set} : forall l mstr cpos hist histr actr rem_str tok_op sp n ncur_pos' rem, semiActionCompute (Token := Token) (Hist := Hist) l mstr cpos hist rem_str tok_op sp = (OneLexImplementationError n rem ncur_pos', histr, actr) -> False .
Proof.
induction l; simpl; intros.
inversion H.
induction a.
apply IHl in H.
auto.
case_eq l; intros; rewrite H0 in H.
case_eq (lexer r rem_str cpos hist); intros; rewrite H1 in H.
induction o; try inversion H.
apply lexer_no_implementation_error in H1; auto.
case_eq (lexer r rem_str cpos hist); intros; rewrite H1 in H.
rewrite <- H0 in H.
induction o.
induction o.
induction token0.
apply IHl in H; auto.
inversion H.
apply IHl in H; auto.
inversion H.
apply lexer_no_implementation_error in H1; auto.
inversion H.
inversion H.
apply IHl in H; auto.
case_eq l; intros; rewrite H0 in H.
induction (p mstr sp tok_op rem_str cpos hist); induction a; inversion H.
rewrite <- H0 in H.
induction (p mstr sp tok_op rem_str cpos hist).
induction a0.
apply IHl in H; auto.
inversion H.
inversion H.
Qed.

Lemma semiActionCompute_start_interruption_position {Token Hist : Set} : forall l mstr cpos hist histr actr rem_str tok_op sp ts_pos cur_pos tok_str_val
      remaining_str, semiActionCompute (Token := Token) (Hist := Hist) l mstr cpos hist rem_str tok_op sp = (OneLexSpecNoToken tok_str_val ts_pos remaining_str cur_pos, histr, actr) -> positionLE sp cpos -> positionLE sp ts_pos.
Proof.
induction l; simpl; intros; rename H0 into H'.
inversion H.
apply positionLE_ident.
induction a.
eapply IHl; eauto.
case_eq (lexer r rem_str cpos hist); intros; rewrite H0 in *.
case_eq l; intros; rewrite H1 in H.
induction o; inversion H.
apply lexer_start_interruption_position in H0.
rewrite H4 in *.
eapply positionLE_trans; eauto.
rewrite <- H1 in *.
induction o.
induction o.
induction token0.
eapply IHl in H; eauto.
apply lexer_start_tok_position in H0.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
eapply IHl in H; eauto.
apply lexer_tok_position in H0; auto.
apply lexer_tok_position in H0; auto.
inversion H.
eapply IHl in H; eauto.
apply lexer_start_interruption_position in H0.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
apply lexer_start_interruption_position2 in H0; auto.
inversion H.
inversion H.
inversion H.
inversion H.
eapply IHl in H; eauto.
eapply positionLE_trans; eauto.
apply changer_correct_le.
case_eq l; intros; rewrite H0 in H.
induction (p mstr sp tok_op rem_str cpos hist).
induction a; inversion H.
induction (p mstr sp tok_op rem_str cpos hist).
rewrite <- H0 in H.
induction a0.
eapply IHl in H; eauto.
inversion H. 
inversion H.
apply positionLE_ident.
Qed.

Lemma semiActionCompute_start_interruption_position2 {Token Hist : Set} : forall l mstr cpos hist histr actr rem_str tok_op sp ts_pos cur_pos tok_str_val
      remaining_str, semiActionCompute (Token := Token) (Hist := Hist) l mstr cpos hist rem_str tok_op sp = (OneLexSpecNoToken tok_str_val ts_pos remaining_str cur_pos, histr, actr) -> positionLE sp cpos -> positionLE ts_pos cur_pos.
Proof.
induction l; simpl; intros; rename H0 into H'.
inversion H.
rewrite H2 in *.
rewrite H4 in *.
auto.
induction a.
eapply IHl; eauto.
case_eq (lexer r rem_str cpos hist); intros; rewrite H0 in *.
case_eq l; intros; rewrite H1 in H.
induction o; inversion H.
rewrite H4 in *.
rewrite H6 in *.
apply lexer_start_interruption_position2 in H0; auto.
induction o.
induction o.
induction token0.
rewrite <- H1 in H.
eapply IHl in H; eauto.
apply lexer_tok_position in H0; auto.
inversion H.
rewrite <- H1 in H.
eapply IHl in H; eauto.
apply lexer_start_interruption_position2 in H0; auto.
inversion H.
inversion H.
inversion H.
inversion H.
eapply IHl in H; eauto.
eapply positionLE_trans; eauto.
apply changer_correct_le.
case_eq l; intros; rewrite H0 in H.
induction (p mstr sp tok_op rem_str cpos hist).
induction a; inversion H.
induction (p mstr sp tok_op rem_str cpos hist).
rewrite <- H0 in H.
induction a0.
eapply IHl in H; eauto.
inversion H. 
inversion H.
rewrite H2 in *.
rewrite H4 in *.
auto.
Qed.

Lemma semiActionCompute_LDec {Token Hist : Set} : forall l mstr cpos hist lexr histr actr rem_str tok_op sp, semiActionCompute (Token := Token) (Hist := Hist) l mstr cpos hist rem_str tok_op sp = (lexr, histr, actr) -> List.length actr <= List.length l .
Proof.
induction l; simpl; intros.
inversion H; auto.
induction a.
apply IHl in H; lia.
case_eq l; intros; rewrite H0 in H.
case_eq (lexer r rem_str cpos hist); intros; rewrite H1 in H.
induction o.
inversion H.
simpl; lia.
inversion H; simpl; lia.
inversion H; simpl; lia.
inversion H; simpl; lia.
inversion H; simpl; lia.
inversion H; simpl; lia.
inversion H; simpl; lia.
rewrite <- H0 in *.
case_eq (lexer r rem_str cpos hist); intros; rewrite H1 in H.
induction o.
induction o.
induction token0.
apply IHl in H; lia.
inversion H; simpl; lia.
apply IHl in H; lia.
inversion H; simpl; lia.
inversion H; simpl; lia.
inversion H; simpl; lia.
inversion H; simpl; lia.
apply IHl in H; lia.
case_eq l; intros; rewrite H0 in H.
induction (p mstr sp tok_op rem_str cpos hist).
induction a; inversion H.
lia.
simpl; lia.
rewrite <- H0 in *.
induction (p mstr sp tok_op rem_str cpos hist).
induction a0.
apply IHl in H; lia.
inversion H; simpl; lia.
inversion H; simpl; lia.
Qed.

Lemma semiActionCompute_SafeHH {Token Hist : Set} : forall l mstr cpos hist lexr histr actr rem_str tok_op sp h, semiActionCompute (Token := Token) (Hist := Hist) l mstr cpos hist rem_str tok_op sp = (lexr, histr, (HistoryHandler h)::actr) -> False .
Proof.
induction l; simpl; intros.
inversion H; auto.
case_eq a; intros; rewrite H0 in *; rename H0 into Ha.
apply IHl in H; auto.
case_eq l; intros; rewrite H0 in H.
case_eq (lexer r rem_str cpos hist); intros; rewrite H1 in H.
induction o.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
case_eq (lexer r rem_str cpos hist); intros; rewrite H1 in H.
induction o.
induction o.
induction token0.
rewrite <- H0 in *.
apply IHl in H; auto.
inversion H.
rewrite <- H0 in *.
apply IHl in H; auto.
inversion H.
inversion H.
inversion H.
inversion H.
apply IHl in H; auto.
case_eq l; intros; rewrite H0 in H.
induction (p mstr sp tok_op rem_str cpos hist).
induction a0; inversion H. 
rewrite <- H0 in *.
induction (p mstr sp tok_op rem_str cpos hist).
induction a1.
apply IHl in H; auto.
 inversion H.
inversion H.
Qed.

Lemma semiActionCompute_SafePH {Token Hist : Set} : forall l mstr cpos hist lexr histr actr rem_str tok_op sp h, semiActionCompute (Token := Token) (Hist := Hist) l mstr cpos hist rem_str tok_op sp = (lexr, histr, (PosHandler h)::actr) -> False .
Proof.
induction l; simpl; intros.
inversion H; auto.
case_eq a; intros; rewrite H0 in *; rename H0 into Ha.
apply IHl in H; auto.
case_eq l; intros; rewrite H0 in H.
case_eq (lexer r rem_str cpos hist); intros; rewrite H1 in H.
induction o.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
case_eq (lexer r rem_str cpos hist); intros; rewrite H1 in H.
induction o.
induction o.
induction token0.
rewrite <- H0 in *.
apply IHl in H; auto.
inversion H.
rewrite <- H0 in *.
apply IHl in H; auto.
inversion H.
inversion H.
inversion H.
inversion H.
apply IHl in H; auto.
case_eq l; intros; rewrite H0 in H.
induction (p mstr sp tok_op rem_str cpos hist).
induction a0; inversion H. 
rewrite <- H0 in *.
induction (p mstr sp tok_op rem_str cpos hist).
induction a1.
apply IHl in H; auto.
 inversion H.
inversion H.
Qed.

Definition isError {Token : Set} (o : OneLexResult(Token:=Token)) := match o with
| OneLexSResult _ => false
| OneLexUserDefinitionErrorResult _ _ p => true
| OneLexSpecNoToken _ _ _ p => false
| OneLexSpecError _ _ p => true
| OneLexImplementationError _ _ p => true
| OneLexNoMatchErrorResult _ p => true
| OneLexLoop _ p => true
end.

Lemma semiActionCompute_SafeTR {Token Hist : Set} : forall l mstr cpos hist lexr histr actr rem_str tok_op sp h, semiActionCompute (Token := Token) (Hist := Hist) l mstr cpos hist rem_str tok_op sp = (lexr, histr, (TokenReturn h)::actr) -> isError lexr = true .
Proof.
induction l; simpl; intros.
inversion H; auto.
case_eq a; intros; rewrite H0 in *; rename H0 into Ha.
apply IHl in H; auto.
case_eq l; intros; rewrite H0 in H.
case_eq (lexer r rem_str cpos hist); intros; rewrite H1 in H.
induction o.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
case_eq (lexer r rem_str cpos hist); intros; rewrite H1 in H.
induction o.
induction o.
induction token0.
rewrite <- H0 in *.
apply IHl in H; auto.
inversion H.
rewrite <- H0 in *.
apply IHl in H; auto.
inversion H.
inversion H.
inversion H.
inversion H.
apply IHl in H; auto.
case_eq l; intros; rewrite H0 in H.
induction (p mstr sp tok_op rem_str cpos hist).
induction a0; inversion H.
simpl; auto. 
rewrite <- H0 in *.
induction (p mstr sp tok_op rem_str cpos hist).
induction a1.
apply IHl in H; auto.
 inversion H; simpl; auto.
inversion H; simpl; auto.
Qed.

Lemma semiActionCompute_SafeLex {Token Hist : Set} : forall l mstr cpos hist lexr histr actr rem_str tok_op sp h, semiActionCompute (Token := Token) (Hist := Hist) l mstr cpos hist rem_str tok_op sp = (lexr, histr, (AnotherLexer h)::actr) -> isError lexr = true .
Proof.
induction l; simpl; intros.
inversion H; auto.
case_eq a; intros; rewrite H0 in *; rename H0 into Ha.
apply IHl in H; auto.
case_eq l; intros; rewrite H0 in H.
case_eq (lexer r rem_str cpos hist); intros; rewrite H1 in H.
induction o.
inversion H.
inversion H; auto.
inversion H.
inversion H; auto.
inversion H; auto.
inversion H; auto.
inversion H; auto.
case_eq (lexer r rem_str cpos hist); intros; rewrite H1 in H.
induction o.
induction o.
induction token0.
rewrite <- H0 in *.
apply IHl in H; auto.
inversion H; auto.
rewrite <- H0 in *.
apply IHl in H; auto.
inversion H; auto.
inversion H; auto.
inversion H; auto.
inversion H; auto.
apply IHl in H; auto.
case_eq l; intros; rewrite H0 in H.
induction (p mstr sp tok_op rem_str cpos hist).
induction a0; inversion H.
rewrite <- H0 in *.
induction (p mstr sp tok_op rem_str cpos hist).
induction a1.
apply IHl in H; auto.
 inversion H; simpl; auto.
inversion H; simpl; auto.
Qed.

Lemma semiActionCompute_SafeSelf {Token Hist : Set} : forall l mstr cpos hist lexr histr actr rem_str tok_op sp, semiActionCompute (Token := Token) (Hist := Hist) l mstr cpos hist rem_str tok_op sp = (lexr, histr, (SelfRec::actr)) -> (match lexr with | OneLexSpecNoToken _ _ _ _ => true | _ => false end) = true .
Proof.
induction l; simpl; intros.
inversion H; auto.
case_eq a; intros; rewrite H0 in *; rename H0 into Ha.
apply IHl in H; auto.
case_eq l; intros; rewrite H0 in H.
case_eq (lexer r rem_str cpos hist); intros; rewrite H1 in H.
induction o.
inversion H.
inversion H; auto.
inversion H.
inversion H; auto.
inversion H; auto.
inversion H; auto.
inversion H; auto.
case_eq (lexer r rem_str cpos hist); intros; rewrite H1 in H.
induction o.
induction o.
induction token0.
rewrite <- H0 in *.
apply IHl in H; auto.
inversion H; auto.
rewrite <- H0 in *.
apply IHl in H; auto.
inversion H; auto.
inversion H; auto.
inversion H; auto.
inversion H; auto.
apply IHl in H; auto.
case_eq l; intros; rewrite H0 in H.
induction (p mstr sp tok_op rem_str cpos hist).
induction a0; inversion H.
rewrite <- H0 in *.
induction (p mstr sp tok_op rem_str cpos hist).
induction a1.
apply IHl in H; auto.
 inversion H; simpl; auto.
inversion H; simpl; auto.
Qed.

(*Definition oef_one_step {Token Hist: Set} (action : AtomicAction (Token := Token) (Hist := Hist)) (start_pos : Position) cur_position (history : Hist) (last_matched_str : string) tok_opt : OneLexResult * Hist := match action with
| HistoryHandler f => (OneLexImplementationError 0 EmptyString cur_position, history)
| AnotherLexer f => (lexer f) ""%string cur_position history
| PosHandler f => (OneLexImplementationError 1 EmptyString cur_position, history)
| TokenReturn f => (match f last_matched_str start_pos tok_opt EmptyString cur_position history with 
                    | (ResultOk t, nh) => (OneLexSResult {| 
                        token := {|s_pos := start_pos; 
                          tok := t; 
                          str_val := last_matched_str |}; 
                        cur_pos := cur_position ; 
                        remaining_str := ""%string |}, nh)
                    | (ResultError msg, nh) => (OneLexUserDefinitionErrorResult msg EmptyString cur_position, nh)
                    end)
| SelfRec => (OneLexLoop EmptyString cur_position, history)
end.*)

Definition eof_process {Token Hist: Set} (eof_action : Action (Token := Token) (Hist := Hist)) start_pos cur_position history last_matched_str tok_opt:=
match semiActionCompute eof_action last_matched_str cur_position history EmptyString tok_opt start_pos with
 | (OneLexSpecNoToken matched_str spos rem_str cur_pos, hist, SelfRec::t) => (OneLexLoop EmptyString cur_pos, hist)
 | (res, hist, _) => (res, hist)
end.

(*Lemma eof_process_start_end_position {Token Hist: Set} : forall eof_action start_pos cur_position history
      last_matched_str nhistory r tok_opt,
 eof_process Token Hist eof_action start_pos cur_position history
      last_matched_str tok_opt =
    (r, nhistory) -> positionLE cur_position (extractCurrentPosition r).
Proof.
intros.
functional induction eof_process Token Hist eof_action start_pos cur_position history
      last_matched_str tok_opt.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnPosLE in e.
inversion H; simpl in *; auto.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnPosLE in e.
inversion H; simpl in *; auto.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnPosLE in e.
inversion H; simpl in *; auto.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnPosLE in e.
inversion H; simpl in *; auto.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnPosLE in e.
inversion H; simpl in *; auto.

apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnPosLE in e.
inversion H; simpl in *; auto.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnPosLE in e; simpl in e; auto.
induction h; simpl in H.
inversion H; simpl in *; auto.
apply lexer_start_cur_position in H.
eapply (positionLE_trans cur_position ncur_pos); auto.
inversion H; simpl in *; auto.
induction (p last_matched_str start_pos tok0 ""%string ncur_pos nhist), a; try inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnPosLE in e; simpl in e.
case_eq h; intros; rewrite H0 in e0; simpl in e0; try discriminate e0.
apply lexer_start_cur_position in e0; simpl in *.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
induction (p last_matched_str start_pos tok0 ""%string ncur_pos nhist), a; try inversion e0; simpl in *; auto.
rewrite <- H5 in *.
eapply positionLE_trans; eauto.
apply IHp in H; auto.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnPosLE in e.
case_eq h; intros; rewrite H0 in e0; simpl in e0; try discriminate e0; simpl in *; auto.
apply lexer_start_cur_position in e0; simpl in *.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
induction (p last_matched_str start_pos tok0 ""%string ncur_pos nhist), a; try inversion e0.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnPosLE in e; simpl in e.
case_eq h; intros; rewrite H in e0; simpl in e0; try inversion e0; simpl in *; auto.
apply lexer_start_cur_position in e0; simpl in *.
eapply positionLE_trans; eauto.
induction (p last_matched_str start_pos tok0 ""%string ncur_pos nhist), a; try inversion e0; simpl in *; auto.
Qed.

Lemma eof_process_tok_position {Token Hist: Set} : forall eof_action start_pos cur_position history
      last_matched_str ts_pos tok tok_str_val cur_pos0 remaining_str0 nhistory tok_opt,
 eof_process Token Hist eof_action start_pos cur_position history
      last_matched_str tok_opt =
    (OneLexSResult
       {|
       token := {|
                  s_pos := ts_pos;
                  tok := tok;
                  str_val := tok_str_val |};
       cur_pos := cur_pos0;
       remaining_str := remaining_str0 |}, nhistory) -> positionLE start_pos cur_position -> positionLE ts_pos cur_pos0.
Proof.
intros.
functional induction eof_process Token Hist eof_action start_pos cur_position history
      last_matched_str tok_opt.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
induction h; simpl in H.
inversion H.
apply lexer_tok_position in H; auto.
inversion H.
induction (p last_matched_str start_pos tok1 ""%string ncur_pos nhist), a; try inversion H.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnPosLE in e.
rewrite <- H2.
rewrite <- H5 in *.
eapply positionLE_trans; eauto.
inversion H.
apply IHp in H; auto.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnPosLE in e.
case_eq h; intros; rewrite H1 in *; simpl in e0; try inversion e0.
apply lexer_tok_position in e0; auto.
induction (p last_matched_str start_pos tok1 ""%string ncur_pos nhist), a; try inversion e0.
rewrite H7 in *.
rewrite H4 in *.
eapply positionLE_trans; eauto.
apply IHp in H; auto.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnPosLE in e.
case_eq h; intros; rewrite H1 in *; simpl in e0; try inversion e0.
apply lexer_start_interruption_position2 in e0.
auto.
induction (p last_matched_str start_pos tok1 ""%string ncur_pos nhist), a; try inversion e0.
inversion y0.
Qed.

Lemma eof_process_start_tok_position {Token Hist: Set} : forall eof_action start_pos cur_position history
      last_matched_str ts_pos tok tok_str_val cur_pos0 remaining_str0 nhistory tok_opt,
 eof_process Token Hist eof_action start_pos cur_position history
      last_matched_str tok_opt =
    (OneLexSResult
       {|
       token := {|
                  s_pos := ts_pos;
                  tok := tok;
                  str_val := tok_str_val |};
       cur_pos := cur_pos0;
       remaining_str := remaining_str0 |}, nhistory) -> positionLE start_pos cur_position -> positionLE start_pos ts_pos.
Proof.
intros.
functional induction eof_process Token Hist eof_action start_pos cur_position history
      last_matched_str tok_opt.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnPosLE in e.
induction h; simpl in H.
inversion H.
apply lexer_start_tok_position in H; auto.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
inversion H.
induction (p last_matched_str start_pos tok1 ""%string ncur_pos nhist), a; try inversion H.
apply positionLE_ident.
inversion H.
apply IHp in H; auto.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnPosLE in e.
case_eq h; intros; rewrite H1 in *; simpl in e0; try inversion e0.
apply lexer_start_tok_position in e0; auto.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
induction (p last_matched_str start_pos tok1 ""%string ncur_pos nhist), a; try inversion e0.
auto.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnPosLE in e.
case_eq h; intros; rewrite H1 in *; simpl in e0; try inversion e0.
apply lexer_tok_position in e0; auto.
induction (p last_matched_str start_pos tok1 ""%string ncur_pos nhist), a; try inversion e0.
rewrite H4 in *.
rewrite H7 in *.
eapply positionLE_trans; eauto.
apply IHp in H; auto.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnPosLE in e.
case_eq h; intros; rewrite H1 in *; simpl in e0; try inversion e0.
apply lexer_start_cur_position in e0; simpl in *.
apply lexer_start_interruption_position in H3.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
induction (p last_matched_str start_pos tok1 ""%string ncur_pos nhist), a; try inversion e0.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnPosLE in e; simpl in *.
case_eq h; intros; rewrite H1 in *; simpl in e0; try inversion e0.
apply lexer_start_interruption_position2 in H3; auto.
induction (p last_matched_str start_pos tok1 ""%string ncur_pos nhist), a; try inversion e0.
inversion y0.
Qed. 

Lemma lexer_remaining_eof {Token Hist: Set} : forall r (r0 : RecLexer(Token:=Token)(Hist:=Hist)) ncur_pos nhist nhistory, (lexer r0) ""%string ncur_pos nhist = (r, nhistory) -> 
  extractRemainingString r = ""%string.
Proof.
intros.
assert (H':=H).
assert (H'':=H).
apply lexer_start_cur_position_abs in H.
simpl in H.
apply lexer_correct_consum in H'.
unfold ignore_nfirst_char in *.
simpl in H'.
induction (abs_pos (extractCurrentPosition r) - abs_pos ncur_pos); auto.
Qed.

Lemma lexer_abs_mov_eof {Token Hist: Set} : forall r (r0 : RecLexer(Token:=Token)(Hist:=Hist)) ncur_pos nhist nhistory, (lexer r0) ""%string ncur_pos nhist = (r, nhistory) -> 
  abs_pos (extractCurrentPosition r) = abs_pos ncur_pos.
Proof.
intros.
assert (H':=H).
assert (H'':=H).
apply lexer_start_cur_position_abs in H.
simpl in H.
lia.
Qed.

Lemma eof_process_remaining_string {Token Hist: Set} : forall eof_action start_pos cur_position history
      last_matched_str r nhistory tok_opt ,
 eof_process Token Hist eof_action start_pos cur_position history
      last_matched_str tok_opt =
    (r, nhistory) -> extractRemainingString r = EmptyString.
Proof.
intros.
functional induction eof_process Token Hist eof_action start_pos cur_position history
      last_matched_str tok_opt.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
inversion H; simpl in *; auto.
induction h; simpl in *; auto.
inversion H; simpl in *; auto.
apply lexer_remaining_eof in H; auto. 
inversion H; auto.
induction (p last_matched_str start_pos tok0 ""%string ncur_pos nhist), a; try inversion H.
auto.
auto.
inversion H; simpl in *; auto.
apply IHp in H; auto.
apply IHp in H; auto.
induction h; simpl in *; auto.
inversion e0; simpl in *; auto.
apply lexer_remaining_eof in e0; auto. 
inversion e0; simpl in *; auto.
induction (p last_matched_str start_pos tok0 ""%string ncur_pos nhist), a; try inversion e0; auto.
inversion e0; simpl in *; auto.
Qed.

Lemma eof_process_abs_mov {Token Hist: Set} : forall eof_action start_pos cur_position history
      last_matched_str r nhistory tok_opt,
 eof_process Token Hist eof_action start_pos cur_position history
      last_matched_str tok_opt =
    (r, nhistory) -> abs_pos (extractCurrentPosition r) = abs_pos cur_position.
Proof.
intros.
functional induction eof_process Token Hist eof_action start_pos cur_position history
      last_matched_str tok_opt.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnAbs in e; simpl in e.
inversion H; simpl in *; auto.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnAbs in e; simpl in e.
inversion H; simpl in *; auto.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnAbs in e; simpl in e.
inversion H; simpl in *; auto.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnAbs in e; simpl in e.
inversion H; simpl in *; auto.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnAbs in e; simpl in e.
inversion H; simpl in *; auto.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnAbs in e; simpl in e.
inversion H; simpl in *; auto.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnAbs in e; simpl in e.
induction h; simpl in *; auto.
inversion H; simpl in *; auto.
apply lexer_abs_mov_eof in H; lia.
inversion H; simpl in *; auto.
induction (p last_matched_str start_pos tok0 ""%string ncur_pos nhist), a; try inversion H; simpl; lia.
inversion H; simpl in *; auto.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnAbs in e; simpl in e.
apply IHp in H; auto.
induction h; simpl in *; auto; inversion e0.
apply lexer_start_cur_position_abs in e0; simpl in *; lia.
induction (p last_matched_str start_pos tok0 ""%string ncur_pos nhist), a; try inversion e0; simpl.
rewrite H5 in *; lia.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnAbs in e; simpl in e.
apply IHp in H.
induction h; simpl in *; auto; inversion e0.
apply lexer_start_cur_position_abs in e0; simpl in *; lia.
induction (p last_matched_str start_pos tok0 ""%string ncur_pos nhist), a; try inversion e0; simpl.
apply recomputePositionAndHistoryIgnoreIntermediaryTokenReturnAbs in e; simpl in e.
induction h; simpl in *; auto; inversion e0; simpl; try lia.
apply lexer_start_cur_position_abs in e0; simpl in *; lia.
induction (p last_matched_str start_pos tok0 ""%string ncur_pos nhist), a; try inversion e0; simpl; lia.
Qed.

Definition oef_on_action_one_step {Token Hist: Set} (action : AtomicAction (Token := Token) (Hist := Hist)) eof_action start_pos cur_position history last_matched_str tok_opt := match action with
| HistoryHandler f => (OneLexImplementationError 2 EmptyString cur_position, history)
| AnotherLexer f => (lexer f) ""%string cur_position history
| PosHandler f => (OneLexImplementationError 3 EmptyString cur_position, history)
| TokenReturn f => (match f last_matched_str start_pos tok_opt ""%string cur_position history with 
                    | (ResultOk t, nh) => (OneLexSResult {| 
                        token := {|s_pos := start_pos; 
                          tok := t; 
                          str_val := last_matched_str |}; 
                        cur_pos := cur_position ; 
                        remaining_str := ""%string |}, nh)
                    | (ResultError msg, nh) => (OneLexUserDefinitionErrorResult msg EmptyString cur_position, nh)
                    end)
| SelfRec => eof_process Token Hist eof_action start_pos cur_position history last_matched_str tok_opt
end.*)

Function eof_on_action {Token Hist: Set} action (eof_action : Action (Token := Token) (Hist := Hist)) start_pos cur_position history last_matched_str tok_opt {measure List.length action}:=
match semiActionCompute action last_matched_str cur_position history EmptyString tok_opt start_pos with
 | (OneLexSpecNoToken matched_str spos rem_str cur_pos, hist, SelfRec::nil) => eof_process eof_action spos cur_pos hist matched_str None
 | (OneLexSpecNoToken matched_str spos rem_str cur_pos, hist, SelfRec::t) => 
      (match eof_process eof_action spos cur_pos hist matched_str None with
        | (OneLexSResult {| 
              token := {|s_pos := tspos; 
                tok := to; 
                str_val := str_val' |}; 
              cur_pos := ncur_pos' ; 
              remaining_str := remaining_str' |}, nhist') => eof_on_action t eof_action tspos ncur_pos' nhist' str_val' (Some to)
         | (OneLexSpecNoToken last_m last_sp
              str ncur_pos'
            , nhist') => eof_on_action t eof_action last_sp ncur_pos' nhist' last_m None
         | r => r
        end)
 | (res, hist, _) => (res, hist)
end.
Proof.
intros.
apply semiActionCompute_LDec in teq; auto.
intros.
apply semiActionCompute_LDec in teq; auto.
Qed.

Lemma eof_on_action_safe {Token Hist: Set} : forall (eof_action : Action (Token := Token) (Hist := Hist)) curAction start_pos cur_position history history' last_matched_str n str cur_position' tok_opt, eof_on_action Token Hist curAction eof_action start_pos cur_position history last_matched_str tok_opt = (OneLexImplementationError n str cur_position', history') -> False.
Proof.
intros.
functional induction eof_on_action Token Hist curAction eof_action start_pos cur_position history
      last_matched_str tok_opt.
unfold eof_process in *.
case_eq (semiActionCompute eof_action matched_str cur_pos0 hist "" None spos); intros; rewrite H0 in H.
induction p.
induction a0; try inversion H.
case_eq a; intros; rewrite H1 in H; try inversion H; clear H2.
induction a0; inversion H.
apply semiActionCompute_no_implementation_error in H0; auto.
apply IHp in H; auto.
apply IHp in H; auto.
unfold eof_process in *.
case_eq (semiActionCompute eof_action matched_str cur_pos0 hist "" None spos); intros; rewrite H in e0.
induction p.
induction a0; try inversion e0; clear H1.
case_eq a; intros; rewrite H0 in e0; try inversion e0; clear H2.
induction a0; inversion e0.
apply semiActionCompute_no_implementation_error in H; auto.
inversion H.
rewrite H1 in *.
apply semiActionCompute_no_implementation_error in e; auto.
Qed.

Lemma eof_on_action_start_end_position {Token Hist: Set} : forall curAction eof_action start_pos cur_position history
      last_matched_str r nhistory tok_opt,
 eof_on_action Token Hist curAction eof_action start_pos cur_position history
      last_matched_str tok_opt =
    (r, nhistory) -> positionLE cur_position (extractCurrentPosition r).
Proof.
intros.
functional induction eof_on_action Token Hist curAction eof_action start_pos cur_position history
      last_matched_str tok_opt.

unfold eof_process in H; simpl in H.
case_eq (semiActionCompute eof_action matched_str cur_pos0 hist "" None spos); intros; rewrite H0 in *.
induction p.
induction a0; inversion H.
rewrite H2 in *.
apply semiActionCompute_start_cur_position in H0; simpl in H0.
apply semiActionCompute_start_cur_position in e; simpl in e.
eapply positionLE_trans; eauto.
rewrite H2 in *.
apply semiActionCompute_start_cur_position in H0; simpl in H0.
apply semiActionCompute_start_cur_position in e; simpl in e.
eapply positionLE_trans; eauto.
clear H2.
case_eq a; intros; rewrite H1 in *.
inversion H.
apply semiActionCompute_start_cur_position in H0; simpl in H0.
apply semiActionCompute_start_cur_position in e; simpl in e.
eapply positionLE_trans; eauto.
induction a0; inversion H; apply semiActionCompute_start_cur_position in H0; simpl in H0; apply semiActionCompute_start_cur_position in e; simpl in e; eapply positionLE_trans; eauto.
inversion H; apply semiActionCompute_start_cur_position in H0; simpl in H0; apply semiActionCompute_start_cur_position in e; simpl in e; eapply positionLE_trans; eauto.
inversion H; apply semiActionCompute_start_cur_position in H0; simpl in H0; apply semiActionCompute_start_cur_position in e; simpl in e; eapply positionLE_trans; eauto.
inversion H; apply semiActionCompute_start_cur_position in H0; simpl in H0; apply semiActionCompute_start_cur_position in e; simpl in e; eapply positionLE_trans; eauto.
inversion H; apply semiActionCompute_start_cur_position in H0; simpl in H0; apply semiActionCompute_start_cur_position in e; simpl in e; eapply positionLE_trans; eauto.
apply IHp in H; auto.
apply semiActionCompute_start_cur_position in e; simpl in e.
unfold eof_process in e0; simpl in e0.
case_eq (semiActionCompute eof_action matched_str cur_pos0 hist "" None spos); intros; rewrite H0 in *.
induction p.
induction a0; inversion e0.
rewrite H2 in *.
apply semiActionCompute_start_cur_position in H0; simpl in H0.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
clear H2.
case_eq a; intros; rewrite H1 in *.
inversion e0.
induction a0; inversion e0.
apply IHp in H; auto.
unfold eof_process in e0; simpl in e0.
case_eq (semiActionCompute eof_action matched_str cur_pos0 hist "" None spos); intros; rewrite H0 in *.
induction p.
induction a0; inversion e0.
clear H2.
case_eq a; intros; rewrite H1 in e0; try inversion e0.
apply semiActionCompute_start_cur_position in e; simpl in e.
rewrite H6 in *.
apply semiActionCompute_start_cur_position in H0; simpl in H0.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
clear H3.
induction a0; inversion e0.
rewrite H6 in *.
apply semiActionCompute_start_cur_position in e; simpl in e.
apply semiActionCompute_start_cur_position in H0; simpl in H0.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
rewrite H6 in *.
apply semiActionCompute_start_cur_position in e; simpl in e.
apply semiActionCompute_start_cur_position in H0; simpl in H0.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
rewrite H6 in *.
apply semiActionCompute_start_cur_position in e; simpl in e.
apply semiActionCompute_start_cur_position in H0; simpl in H0.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
rewrite H6 in *.
apply semiActionCompute_start_cur_position in e; simpl in e.
apply semiActionCompute_start_cur_position in H0; simpl in H0.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
apply semiActionCompute_start_cur_position in e; simpl in e.
unfold eof_process in e0; simpl in e0.
case_eq (semiActionCompute eof_action matched_str cur_pos0 hist "" None spos); intros; rewrite H in *.
induction p.
apply semiActionCompute_start_cur_position in H; simpl in H.
eapply positionLE_trans; eauto.
induction a0; inversion e0; auto.
clear H1.
induction a; inversion e0; auto.
induction a; inversion e0; auto.
apply semiActionCompute_start_cur_position in e; simpl in e.
inversion H.
rewrite H1 in *; auto.
Qed.


Lemma eof_on_action_tok_position {Token Hist: Set} : forall curAction eof_action start_pos cur_position history ts_pos tok tok_str_val
      last_matched_str cur_pos0 remaining_str0 nhistory tok_opt,
 eof_on_action Token Hist curAction eof_action start_pos cur_position history
      last_matched_str tok_opt =
    (OneLexSResult
       {|
       token := {|
                        s_pos := ts_pos;
                        tok := tok;
                        str_val := tok_str_val |};
       cur_pos := cur_pos0;
       remaining_str := remaining_str0 |}, nhistory) -> positionLE start_pos cur_position -> positionLE ts_pos cur_pos0.
Proof.
intros.
functional induction eof_on_action Token Hist curAction eof_action start_pos cur_position history
      last_matched_str tok_opt.
unfold eof_process in *.
case_eq (semiActionCompute eof_action matched_str cur_pos1 hist "" None spos); intros; rewrite H1 in *.
induction p.
induction a0; inversion H.
rewrite H3 in *; simpl in *.
apply semiActionCompute_tok_position in H1; simpl in H1; auto.
apply semiActionCompute_start_interruption_position2 in e; simpl in e; auto.
induction a; inversion H3.
induction a; inversion H4.
unfold eof_process in *.
case_eq (semiActionCompute eof_action matched_str cur_pos1 hist "" None spos); intros; rewrite H1 in *.
induction p.
induction a0; inversion e0.
rewrite H3 in *; simpl in *.
apply IHp in H; auto.
apply semiActionCompute_tok_position in H1; simpl in H1; auto.
apply semiActionCompute_start_interruption_position2 in e; simpl in e; auto.
clear H3.
case_eq a; intros; rewrite H2 in *; inversion e0.
clear H4.
induction a0; inversion e0.
unfold eof_process in *.
case_eq (semiActionCompute eof_action matched_str cur_pos1 hist "" None spos); intros; rewrite H1 in *.
induction p.
induction a0; inversion e0.
clear H3.
case_eq a; intros; rewrite H2 in *; inversion e0.
apply IHp in H; auto.
rewrite H5 in *.
rewrite H7 in *.
apply semiActionCompute_start_interruption_position2 in H1; simpl in H1; auto.
apply semiActionCompute_start_interruption_position2 in e; simpl in e; auto.
clear H4.
apply IHp in H; auto.
induction a0; inversion e0; auto.
rewrite H7 in *.
rewrite H5 in *.
apply semiActionCompute_start_interruption_position2 in H1; simpl in H1; auto.
apply semiActionCompute_start_interruption_position2 in e; simpl in e; auto.
rewrite H7 in *.
rewrite H5 in *.
apply semiActionCompute_start_interruption_position2 in H1; simpl in H1; auto.
apply semiActionCompute_start_interruption_position2 in e; simpl in e; auto.
rewrite H7 in *.
rewrite H5 in *.
apply semiActionCompute_start_interruption_position2 in H1; simpl in H1; auto.
apply semiActionCompute_start_interruption_position2 in e; simpl in e; auto.
rewrite H7 in *.
rewrite H5 in *.
apply semiActionCompute_start_interruption_position2 in H1; simpl in H1; auto.
apply semiActionCompute_start_interruption_position2 in e; simpl in e; auto.
inversion y0.
inversion H.
rewrite H2 in *.
apply semiActionCompute_tok_position in e; simpl in e; auto.
Qed.

Lemma eof_on_action_start_tok_position {Token Hist: Set} : forall curAction eof_action start_pos cur_position history ts_pos tok tok_str_val
      last_matched_str cur_pos0 remaining_str0 nhistory tok_opt,
 eof_on_action Token Hist curAction eof_action start_pos cur_position history
      last_matched_str tok_opt =
    (OneLexSResult
       {|
       token := {|
                        s_pos := ts_pos;
                        tok := tok;
                        str_val := tok_str_val |};
       cur_pos := cur_pos0;
       remaining_str := remaining_str0 |}, nhistory) -> positionLE start_pos cur_position -> positionLE start_pos ts_pos.
Proof.
intros.
functional induction eof_on_action Token Hist curAction eof_action start_pos cur_position history
      last_matched_str tok_opt.
unfold eof_process in *.
case_eq (semiActionCompute eof_action matched_str cur_pos1 hist "" None spos); intros; rewrite H1 in *.
induction p.
induction a0; inversion H.
rewrite H3 in *; simpl in *.
apply semiActionCompute_start_tok_position in H1; simpl in H1; auto.
apply semiActionCompute_start_interruption_position in e; simpl in e; auto.
eapply positionLE_trans; eauto.
apply semiActionCompute_start_interruption_position2 in e; simpl in e; auto.
induction a; inversion H3.
induction a; inversion H4.
unfold eof_process in *.
case_eq (semiActionCompute eof_action matched_str cur_pos1 hist "" None spos); intros; rewrite H1 in *.
induction p.
induction a0; inversion e0.
rewrite H3 in *; simpl in *.
apply IHp in H; auto.
apply semiActionCompute_start_tok_position in H1; simpl in H1; auto.
apply semiActionCompute_start_interruption_position in e; simpl in e; auto.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
apply semiActionCompute_start_interruption_position2 in e; simpl in e; auto.
apply semiActionCompute_tok_position in H1; simpl in H1; auto.
apply semiActionCompute_start_interruption_position2 in e; simpl in e; auto.
clear H3.
case_eq a; intros; rewrite H2 in *; inversion e0.
induction a0; inversion e0.
unfold eof_process in *.
case_eq (semiActionCompute eof_action matched_str cur_pos1 hist "" None spos); intros; rewrite H1 in *.
induction p.
induction a0; inversion e0.
clear H3.
apply IHp in H; auto.
case_eq a; intros; rewrite H2 in *; inversion e0.
rewrite H5 in *.
apply semiActionCompute_start_interruption_position in H1; simpl in H1; auto.
apply semiActionCompute_start_interruption_position in e; simpl in e; auto.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
apply semiActionCompute_start_interruption_position2 in e; simpl in e; auto.
clear H4.
induction a0; inversion e0; auto.
apply semiActionCompute_SafeHH in H1; inversion H1.
apply semiActionCompute_SafeLex in H1; inversion H1.
apply semiActionCompute_SafePH in H1; inversion H1.
apply semiActionCompute_SafeTR in H1; inversion H1.
induction a; inversion e0.
rewrite H4 in *.
rewrite H6 in *.
apply semiActionCompute_start_interruption_position2 in H1; simpl in H1; auto.
apply semiActionCompute_start_interruption_position2 in e; simpl in e; auto.
clear H3.
induction a; inversion e0.
apply semiActionCompute_SafeHH in H1; inversion H1.
apply semiActionCompute_SafeLex in H1; inversion H1.
apply semiActionCompute_SafePH in H1; inversion H1.
apply semiActionCompute_SafeTR in H1; inversion H1.
inversion y0.
inversion H.
rewrite H2 in *.
apply semiActionCompute_start_tok_position in e; auto.
Qed.

Lemma eof_on_action_remaining_str {Token Hist: Set} : forall curAction eof_action start_pos cur_position history
      last_matched_str r nhistory tok_opt,
 eof_on_action Token Hist curAction eof_action start_pos cur_position history
      last_matched_str tok_opt =
    (r, nhistory) -> extractRemainingString r = EmptyString.
Proof.
intros.
functional induction eof_on_action Token Hist curAction eof_action start_pos cur_position history
      last_matched_str tok_opt.

unfold eof_process in *.
case_eq (semiActionCompute eof_action matched_str cur_pos0 hist "" None spos); intros; rewrite H0 in *.
induction p.
apply semiActionCompute_dec_str_eq in e.
apply semiActionCompute_dec_str_eq in H0.
simpl in *.
assert (rem_str = ""%string).
induction rem_str; simpl in e; auto; lia.
assert ((extractRemainingString a0) = ""%string).
induction (extractRemainingString a0); simpl in H0; auto; lia.
induction a0; inversion H; auto.
induction a; inversion H; auto.
induction a; inversion H5; auto.
unfold eof_process in *.
case_eq (semiActionCompute eof_action matched_str cur_pos0 hist "" None spos); intros; rewrite H0 in *.
induction p.
apply semiActionCompute_dec_str_eq in e.
apply semiActionCompute_dec_str_eq in H0.
simpl in *.
assert (rem_str = ""%string).
induction rem_str; simpl in e; auto; lia.
assert ((extractRemainingString a0) = ""%string).
induction (extractRemainingString a0); simpl in H0; auto; lia.
induction a0; inversion e0; auto.

unfold eof_process in *.
case_eq (semiActionCompute eof_action matched_str cur_pos0 hist "" None spos); intros; rewrite H0 in *.
induction p.
apply semiActionCompute_dec_str_eq in e.
apply semiActionCompute_dec_str_eq in H0.
simpl in *.
assert (rem_str = ""%string).
induction rem_str; simpl in e; auto; lia.
assert ((extractRemainingString a0) = ""%string).
induction (extractRemainingString a0); simpl in H0; auto; lia.
induction a0; inversion e0; auto.

unfold eof_process in *.
case_eq (semiActionCompute eof_action matched_str cur_pos0 hist "" None spos); intros; rewrite H in *.
induction p.
apply semiActionCompute_dec_str_eq in e.
apply semiActionCompute_dec_str_eq in H.
simpl in *.
assert (rem_str = ""%string).
induction rem_str; simpl in e; auto; lia.
assert ((extractRemainingString a0) = ""%string).
induction (extractRemainingString a0); simpl in H; auto; lia.
induction a; induction a0; inversion e0; auto.
simpl in *.
assert (s0 = ""%string).
induction s0; simpl in H; auto; lia.
induction a; inversion e0; auto.
inversion H.
rewrite H1 in *.
apply semiActionCompute_dec_str_eq in e.
induction (extractRemainingString r); simpl in e; auto; lia.
Qed.

Lemma eof_on_action_abs_mov {Token Hist: Set} : forall curAction eof_action start_pos cur_position history
      last_matched_str r nhistory tok_opt,
 eof_on_action Token Hist curAction eof_action start_pos cur_position history
      last_matched_str tok_opt =
    (r, nhistory) -> abs_pos (extractCurrentPosition r) = abs_pos cur_position.
Proof.
intros.
functional induction eof_on_action Token Hist curAction eof_action start_pos cur_position history
      last_matched_str tok_opt .
unfold eof_process in *.
case_eq (semiActionCompute eof_action matched_str cur_pos0 hist "" None spos); intros; rewrite H0 in *.
induction p.
apply semiActionCompute_start_cur_position_abs in H0; simpl in *.
apply semiActionCompute_start_cur_position_abs in e; simpl in *.
induction a0; inversion H; simpl in *; auto.
induction o.
lia.
lia.
clear H2.
induction a; inversion H; auto; simpl in *; try lia.
induction a; inversion H; auto; simpl in *; try lia.
lia.
lia.
lia.
lia.
unfold eof_process in *.
case_eq (semiActionCompute eof_action matched_str cur_pos0 hist "" None spos); intros; rewrite H0 in *.
induction p.
apply semiActionCompute_start_cur_position_abs in H0; simpl in *.
apply semiActionCompute_start_cur_position_abs in e; simpl in *.
apply IHp in H.
induction a0; inversion e0; simpl in *; auto.
induction o; inversion e0.
rewrite H5 in *.
lia.
clear H2.
induction a; inversion e0.
clear H2.
induction a; inversion e0.
apply IHp in H.
unfold eof_process in *.
case_eq (semiActionCompute eof_action matched_str cur_pos0 hist "" None spos); intros; rewrite H0 in *.
induction p.
apply semiActionCompute_start_cur_position_abs in H0; simpl in *.
apply semiActionCompute_start_cur_position_abs in e; simpl in *.
induction a0; inversion e0; simpl in *; auto.
clear H2.
induction a; inversion e0.
rewrite H5 in *.
lia.
clear H2.
clear IHa.
induction a; inversion e0; auto; rewrite H5 in *; lia.
unfold eof_process in *.
case_eq (semiActionCompute eof_action matched_str cur_pos0 hist "" None spos); intros; rewrite H in *.
induction p.
apply semiActionCompute_start_cur_position_abs in H; simpl in *.
apply semiActionCompute_start_cur_position_abs in e; simpl in *.
induction a0; inversion e0; simpl in *; try lia.
induction a; inversion e0; simpl in *; try lia.
clear H2.
clear IHa.
clear H1.
induction a; inversion e0; simpl in *; try lia.
inversion H.
rewrite H1 in *.
apply semiActionCompute_start_cur_position_abs in e; simpl in *.
lia.
Qed.

Lemma eof_on_action_start_interruption {Token Hist: Set} : forall curAction eof_action start_pos ncur_pos history
      last_matched_str last_m last_sp str ncur_pos' nhist' tok_opt,
 eof_on_action Token Hist curAction eof_action start_pos ncur_pos history
      last_matched_str tok_opt = (OneLexSpecNoToken last_m last_sp str ncur_pos', nhist')-> positionLE start_pos ncur_pos -> positionLE start_pos last_sp.
Proof.
intros.
functional induction eof_on_action Token Hist curAction eof_action start_pos
      ncur_pos history last_matched_str tok_opt.
unfold eof_process in *.
case_eq (semiActionCompute eof_action matched_str cur_pos0 hist "" None spos); intros; rewrite H1 in *.
induction p.
induction a0; inversion H; auto.
apply semiActionCompute_start_interruption_position in H1; auto.
apply semiActionCompute_start_interruption_position in e; auto.
induction a; auto; inversion H3.
rewrite H5 in *.
eapply positionLE_trans; eauto.
induction a; auto; inversion H3; rewrite H6 in *.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
apply semiActionCompute_start_interruption_position2 in e; auto.

unfold eof_process in *.
case_eq (semiActionCompute eof_action matched_str cur_pos0 hist "" None spos); intros; rewrite H1 in *.
induction p.
induction a0; inversion e0; auto.
rewrite H3 in *.
apply IHp in H; auto.
apply semiActionCompute_start_tok_position in H1; auto.
apply semiActionCompute_start_interruption_position in e; auto.
simpl in *.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
apply semiActionCompute_start_interruption_position2 in e; auto.
apply semiActionCompute_tok_position in H1; auto.
apply semiActionCompute_start_interruption_position2 in e; auto.
clear H3.
induction a; inversion e0; auto.
clear H3.
clear IHa.
induction a; inversion e0; auto.

unfold eof_process in *.
case_eq (semiActionCompute eof_action matched_str cur_pos0 hist "" None spos); intros; rewrite H1 in *.
induction p.
induction a0; inversion e0; auto.
clear H3.
induction a; inversion e0; auto.
apply IHp in H; auto.
rewrite H4 in *.
apply semiActionCompute_start_interruption_position in H1; auto.
apply semiActionCompute_start_interruption_position in e; auto.
simpl in *.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
apply semiActionCompute_start_interruption_position2 in e; auto.
rewrite H4 in *.
rewrite H6 in *.
apply semiActionCompute_start_interruption_position2 in H1; auto.
apply semiActionCompute_start_interruption_position2 in e; auto.
clear H3.
clear IHa.

induction a; inversion e0; auto.
apply semiActionCompute_SafeHH in H1; inversion H1.
apply semiActionCompute_SafeLex in H1; inversion H1.
apply semiActionCompute_SafePH in H1; inversion H1.
apply semiActionCompute_SafeTR in H1; inversion H1.
inversion y0.
inversion H.
rewrite H2 in *.
apply semiActionCompute_start_interruption_position in e; auto.
Qed.

Lemma eof_on_action_start_interruption2 {Token Hist: Set} : forall curAction eof_action start_pos ncur_pos history
      last_matched_str last_m last_sp str ncur_pos' nhist' tok_opt,
 eof_on_action Token Hist curAction eof_action start_pos ncur_pos history
      last_matched_str tok_opt = (OneLexSpecNoToken last_m last_sp str ncur_pos', nhist')-> positionLE start_pos ncur_pos -> positionLE last_sp ncur_pos'.
Proof.
intros.
functional induction eof_on_action Token Hist curAction eof_action start_pos
      ncur_pos history last_matched_str tok_opt.

unfold eof_process in *.
case_eq (semiActionCompute eof_action matched_str cur_pos0 hist "" None spos); intros; rewrite H1 in *.
induction p.
induction a0; inversion H; auto.
apply semiActionCompute_start_interruption_position2 in e; auto.
apply semiActionCompute_start_interruption_position2 in H1; auto.
clear H3.
induction a; inversion H; auto.
rewrite H4 in *.
rewrite H6 in *; auto.
induction a; inversion H; auto.
rewrite H5 in *.
rewrite H7 in *; auto.
rewrite H5 in *.
rewrite H7 in *; auto.
rewrite H5 in *.
rewrite H7 in *; auto.
rewrite H5 in *.
rewrite H7 in *; auto.

unfold eof_process in *.
case_eq (semiActionCompute eof_action matched_str cur_pos0 hist "" None spos); intros; rewrite H1 in *.
induction p.
induction a0; inversion e0; auto.
rewrite H3 in *.
apply IHp in H; auto.
apply semiActionCompute_tok_position in H1; auto.
apply semiActionCompute_start_interruption_position2 in e; auto.
clear H3.
induction a; inversion e0; auto.
clear H3.
clear IHa.
induction a; inversion e0; auto.

unfold eof_process in *.
case_eq (semiActionCompute eof_action matched_str cur_pos0 hist "" None spos); intros; rewrite H1 in *.
induction p.
induction a0; inversion e0; auto.
clear H3.
induction a; inversion e0; auto.
apply IHp in H; auto.
rewrite H4 in *.
rewrite H6 in *.
apply semiActionCompute_start_interruption_position2 in H1; auto.
apply semiActionCompute_start_interruption_position2 in e; auto.
clear H3.
clear IHa.
induction a; inversion e0; auto.
apply semiActionCompute_SafeHH in H1; inversion H1.
apply semiActionCompute_SafeLex in H1; inversion H1.
apply semiActionCompute_SafePH in H1; inversion H1.
apply semiActionCompute_SafeTR in H1; inversion H1.
inversion y0.
inversion H.
rewrite H2 in *.
apply semiActionCompute_start_interruption_position2 in e; auto.
Qed.


Record elector {Action : Set} : Set := mkElector
 {  elector_func : list (Definitions.RegExp * Action) -> string -> option (ElectionResult(Action := Action)) ;

    elector_inf_strLen : forall str (regexp_to_action : list (Definitions.RegExp * Action)) e, elector_func regexp_to_action str = Some e -> resultNat e <= String.length str
}.


Function computeAction {Token Hist: Set} regexp_x_action (eof_action : Action (Token := Token) (Hist := Hist)) str_to_lex start_pos cur_position history curAction last_matched_str tok_opt (elect : elector(Action := Action)) {measure String.length str_to_lex}:=
match str_to_lex with
| EmptyString => eof_on_action Token Hist curAction eof_action start_pos cur_position history last_matched_str tok_opt
| _ => (match semiActionCompute curAction last_matched_str cur_position history str_to_lex tok_opt start_pos with
       | (OneLexSpecNoToken matched_str spos rem_str cur_pos, hist, SelfRec::t) => 
           (match rem_str with
            | EmptyString => eof_on_action Token Hist (List.app eof_action t) eof_action spos cur_pos hist matched_str None
            | _ => (match (elector_func elect) regexp_x_action rem_str with 
                    | None => (OneLexNoMatchErrorResult rem_str cur_pos, hist)
                    | Some elected => (
                      match resultNat elected with
                      | S _ => computeAction regexp_x_action eof_action (ignore_nfirst_char (resultNat elected) rem_str) cur_pos {| l_number := (l_number cur_pos) ; c_number := (c_number cur_pos) + (resultNat elected); 
                        abs_pos := (abs_pos cur_pos) + (resultNat elected) |} hist (List.app (resultAction elected) t) (substring 0 (resultNat elected) rem_str) None elect
                      | 0 =>
                        (
                        match semiActionCompute (List.app (resultAction elected) t) EmptyString cur_pos hist rem_str None spos with
                          | (OneLexSpecNoToken matched_str' spos' rem_str' cur_pos', hist', SelfRec::t') =>
                                (match Nat.eqb (String.length rem_str') (String.length rem_str) with
                                  | true => (OneLexLoop rem_str' cur_pos', hist')
                                  | false => computeAction regexp_x_action eof_action rem_str' spos' cur_pos' hist' (SelfRec::t') matched_str' None elect
                                end)
                          | (res', hist', _) => (res', hist')
                        end)
                      end)
                end)
            end)
    | (res, hist, _) => (res, hist)
    end)
end.
Proof.
intros.
apply semiActionCompute_dec_str_eq in teq0.
apply semiActionCompute_dec_str_eq in teq8.
simpl in *.
apply EqNat.beq_nat_false in teq13.
lia.
intros.
apply semiActionCompute_dec_str_eq in teq0.
simpl in *.
assert (String.length
  (ignore_nfirst_char (S n) (String a2 s0)) < String.length (String a2 s0)).
apply ignore_decroiss_length; lia.
simpl in *.
lia.
Qed.

Lemma computeAction_safe {Token Hist: Set} : forall n history' regexp_x_action (eof_action : Action (Token := Token) (Hist := Hist)) str_to_lex start_pos cur_position history curAction last_matched_str cur_position' str tok_opt elect, computeAction Token Hist regexp_x_action eof_action str_to_lex start_pos cur_position  history curAction last_matched_str tok_opt elect = (OneLexImplementationError n str cur_position', history') -> False.
Proof.
intros.
functional induction computeAction Token Hist regexp_x_action eof_action str_to_lex start_pos
      cur_position history curAction
      last_matched_str tok_opt elect.
apply eof_on_action_safe in H; inversion H.
apply eof_on_action_safe in H; inversion H.
inversion H.
apply IHp in H; inversion H.
inversion H.
apply IHp in H; inversion H.
inversion H.
rewrite H1 in *.
apply semiActionCompute_no_implementation_error in e4.
inversion e4.
inversion H.
rewrite H1 in *.
apply semiActionCompute_no_implementation_error in e0.
inversion e0.
Qed.

Lemma computeAction_start_end_position {Token Hist: Set} : forall regexp_x_action r (eof_action : Action (Token := Token) (Hist := Hist)) curAction last_matched_str str_to_lex start_pos param_pos history nhistory 
      tok_opt elect,
      (computeAction Token Hist regexp_x_action eof_action str_to_lex start_pos param_pos history curAction last_matched_str tok_opt elect = (r, nhistory)) -> positionLE param_pos (extractCurrentPosition r).
Proof.
intros.
functional induction computeAction Token Hist regexp_x_action eof_action str_to_lex
      start_pos param_pos history curAction
      last_matched_str tok_opt elect.
apply eof_on_action_start_end_position in H; auto.
apply eof_on_action_start_end_position in H.
apply semiActionCompute_start_cur_position in e0.
simpl in e0.
eapply positionLE_trans; eauto.
inversion H; simpl.
apply semiActionCompute_start_cur_position in e0; simpl in e0; auto.
apply IHp in H.
apply semiActionCompute_start_cur_position in e0; simpl in e0; auto.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
unfold positionLE; simpl; lia.
apply semiActionCompute_start_cur_position in e0; simpl in e0; auto.
apply semiActionCompute_start_cur_position in e4; simpl in e4; auto.
inversion H; simpl.
eapply positionLE_trans; eauto.
apply IHp in H.
apply semiActionCompute_start_cur_position in e0; simpl in e0; auto.
apply semiActionCompute_start_cur_position in e4; simpl in e4; auto.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
inversion H; simpl.
apply semiActionCompute_start_cur_position in e0; simpl in e0; auto.
apply semiActionCompute_start_cur_position in e4; simpl in e4; auto.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
rewrite H1.
apply positionLE_ident.
inversion H.
rewrite H1 in *.
apply semiActionCompute_start_cur_position in e0; simpl in e0; auto.
Qed.

Lemma computeAction_tok_position {Token Hist: Set} : forall regexp_x_action (eof_action : Action (Token := Token) (Hist := Hist)) curAction last_matched_str str_to_lex start_pos param_pos history nhistory ts_pos tok tok_str_val cur_pos
      remaining_str tok_opt elect,
      (computeAction Token Hist regexp_x_action eof_action str_to_lex start_pos param_pos history curAction last_matched_str tok_opt elect = (OneLexSResult
               {|
               token := {|
                        s_pos := ts_pos;
                        tok := tok;
                        str_val := tok_str_val |};
               cur_pos := cur_pos;
               remaining_str := remaining_str; |}, nhistory)) -> positionLE start_pos param_pos -> positionLE ts_pos cur_pos.
Proof.
intros.
functional induction computeAction Token Hist regexp_x_action eof_action str_to_lex
      start_pos param_pos history curAction
      last_matched_str tok_opt elect.
apply eof_on_action_tok_position in H; auto.
apply eof_on_action_tok_position in H; auto.
apply semiActionCompute_start_interruption_position2 in e0; auto.
inversion H.
apply IHp in H; auto.
unfold positionLE; simpl; lia.
inversion H.
apply IHp in H; auto.
apply semiActionCompute_start_interruption_position2 in e4; auto.
apply semiActionCompute_start_interruption_position2 in e0; auto.
inversion H.
rewrite H2 in *.
apply semiActionCompute_tok_position in e4; auto.
apply semiActionCompute_start_interruption_position2 in e0; auto.
inversion H.
rewrite H2 in *.
apply semiActionCompute_tok_position in e0; auto.
Qed.

Lemma computeAction_start_tok_position {Token Hist: Set} : forall regexp_x_action (eof_action : Action (Token := Token) (Hist := Hist)) curAction last_matched_str str_to_lex start_pos param_pos history nhistory ts_pos tok tok_str_val cur_pos
      remaining_str tok_opt elect,
      (computeAction Token Hist regexp_x_action eof_action str_to_lex start_pos param_pos history curAction last_matched_str tok_opt elect = (OneLexSResult
               {|
               token := {|
                        s_pos := ts_pos;
                        tok := tok;
                        str_val := tok_str_val |};
               cur_pos := cur_pos;
               remaining_str := remaining_str; |}, nhistory)) -> positionLE start_pos param_pos -> positionLE start_pos ts_pos.
Proof.
intros.
functional induction computeAction Token Hist regexp_x_action eof_action str_to_lex
      start_pos param_pos history curAction
      last_matched_str tok_opt elect.
apply eof_on_action_start_tok_position in H; auto.
apply eof_on_action_start_tok_position in H; auto.
apply semiActionCompute_start_interruption_position in e0; auto.
eapply positionLE_trans; eauto.
apply semiActionCompute_start_interruption_position2 in e0; auto.
inversion H.
apply IHp in H; auto.
assert (e0':=e0).
apply semiActionCompute_start_interruption_position2 in e0; auto.
apply semiActionCompute_start_interruption_position in e0'; auto.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
unfold positionLE; simpl; lia.
inversion H.
apply IHp in H; auto.
apply semiActionCompute_start_interruption_position in e4; auto.
apply semiActionCompute_start_interruption_position in e0; auto.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
apply semiActionCompute_start_interruption_position2 in e0; auto.
apply semiActionCompute_start_interruption_position2 in e4; auto.
apply semiActionCompute_start_interruption_position2 in e0; auto.
inversion H.
rewrite H2 in *.
apply semiActionCompute_start_tok_position in e4; auto.
apply semiActionCompute_start_interruption_position in e0; auto.
eapply positionLE_trans; eauto.
apply semiActionCompute_start_interruption_position2 in e0; auto.
inversion H.
rewrite H2 in *.
apply semiActionCompute_start_tok_position in e0; auto.
Qed.

Lemma usefullLia : forall a b c, c <= b -> b <= a -> (a - b) + (b - c) = a - c.
Proof.
induction a, b, c; simpl; lia.
Qed.

Lemma usefullLia2 : forall a b c, b + c <= a -> a - (b + c) + c = a - b.
Proof.
induction a, b, c; simpl; lia.
Qed.

Lemma usefullSubstr : forall str, str = substring 0 (String.length str) str.
Proof.
induction str; auto; simpl.
f_equal; apply IHstr.
Qed.

Lemma computeAction_correct_consum {Token Hist: Set} : forall regexp_x_action r (eof_action : Action (Token := Token) (Hist := Hist)) curAction last_matched_str str_to_lex start_pos param_pos history nhistory 
      tok_opt elect,
      (computeAction Token Hist regexp_x_action eof_action str_to_lex start_pos param_pos history curAction last_matched_str tok_opt elect = (r, nhistory)) -> extractRemainingString r = ignore_nfirst_char ((abs_pos (extractCurrentPosition r)) - (abs_pos param_pos)) str_to_lex.
Proof.
intros.
functional induction computeAction Token Hist regexp_x_action eof_action str_to_lex start_pos param_pos history
      curAction last_matched_str tok_opt elect.
apply eof_on_action_remaining_str in H.
unfold ignore_nfirst_char; simpl.
induction (abs_pos (extractCurrentPosition r) - abs_pos cur_position); auto.
assert (H':=H).
apply eof_on_action_abs_mov in H.
apply eof_on_action_remaining_str in H'.
apply semiActionCompute_correct_consum in e0.
simpl in e0.
rewrite H in *.
rewrite <- e0 in *; auto.
inversion H; simpl.
apply semiActionCompute_correct_consum in e0; simpl in *; auto.
assert (H':= H).
apply IHp in H.
apply computeAction_start_end_position in H'.
unfold positionLE in H'.
simpl in *.
rewrite ignore_usefull in H.
replace (abs_pos (extractCurrentPosition r) - (abs_pos cur_pos0 + resultNat elected) + resultNat elected)
with (abs_pos (extractCurrentPosition r) - abs_pos cur_pos0) in H by lia.
assert (e0':=e0).
apply semiActionCompute_start_cur_position_abs in e0; simpl in *; auto.
apply semiActionCompute_correct_consum in e0'; simpl in *; auto.
rewrite e0' in *.
rewrite ignore_usefull in H.
replace (abs_pos (extractCurrentPosition r) - abs_pos cur_pos0 + (abs_pos cur_pos0 - abs_pos cur_position))
with (abs_pos (extractCurrentPosition r) - abs_pos cur_position)
in H by lia.
auto.
inversion H.
simpl in *.
assert (e0':=e0).
assert (e4':=e4).
apply semiActionCompute_correct_consum in e0; simpl in *; auto.
apply semiActionCompute_correct_consum in e4; simpl in *; auto.
rewrite e0 in e4.
rewrite ignore_usefull in e4.
apply semiActionCompute_start_cur_position in e0'.
simpl in *.
unfold positionLE in e0'.
apply semiActionCompute_start_cur_position in e4'; simpl in *; auto.
unfold positionLE in e4'.
replace (abs_pos cur_pos' - abs_pos cur_pos0 + (abs_pos cur_pos0 - abs_pos cur_position))
with (abs_pos cur_pos' - abs_pos cur_position) in e4 by lia.
auto.
assert (H':=H).
apply IHp in H.
assert (e0':=e0).
assert (e4':=e4).
apply semiActionCompute_correct_consum in e0; simpl in *; auto.
apply semiActionCompute_correct_consum in e4; simpl in *; auto.
rewrite e0 in e4.
rewrite e4 in H.
rewrite ignore_usefull in H.
apply semiActionCompute_start_cur_position in e4'; simpl in *; auto.
apply semiActionCompute_start_cur_position in e0'; simpl in *; auto.
apply computeAction_start_end_position in H'.
unfold positionLE in *.
replace (abs_pos (extractCurrentPosition r) - abs_pos cur_pos' + (abs_pos cur_pos' - abs_pos cur_pos0))
with (abs_pos (extractCurrentPosition r) - abs_pos cur_pos0) in * by lia.
rewrite ignore_usefull in H.
replace (abs_pos (extractCurrentPosition r) - abs_pos cur_pos0 + (abs_pos cur_pos0 - abs_pos cur_position))
with (abs_pos (extractCurrentPosition r) - abs_pos cur_position) in * by lia.
auto.
inversion H.
rewrite H1 in *.
assert (e0':=e0).
assert (e4':=e4).
apply semiActionCompute_correct_consum in e4.
apply semiActionCompute_correct_consum in e0.
simpl in *.
rewrite e0 in e4.
rewrite ignore_usefull in e4.
apply semiActionCompute_start_cur_position in e4'; simpl in *; auto.
apply semiActionCompute_start_cur_position in e0'; simpl in *; auto.
unfold positionLE in *.
replace (abs_pos (extractCurrentPosition r) - abs_pos cur_pos0 + (abs_pos cur_pos0 - abs_pos cur_position))
with (abs_pos (extractCurrentPosition r) - abs_pos cur_position) in * by lia.
auto.
inversion H.
rewrite H1 in *.
apply semiActionCompute_correct_consum in e0.
auto.
Qed.

Lemma usefullSubstr2 : forall str n, String.length (ignore_nfirst_char n str) = String.length str - n.
Proof.
unfold ignore_nfirst_char.
induction str; simpl; auto.
induction n; auto; simpl.
induction n; auto; simpl.
f_equal.
replace (String.length str) with (String.length str - 0) by lia.
rewrite IHstr.
lia.
Qed.

Lemma usefullLia3 : forall a b c, a<= b -> a + (b - a) - c = b - c.
Proof.
induction a, b, c; simpl; lia.
Qed.

Lemma ignore_usefull2 : forall str n, String.length (ignore_nfirst_char n str) +
     String.length (substring 0 n str) = String.length str.
Proof.
induction str, n; simpl; auto.
f_equal.
rewrite substr_0_len_str.
lia.
unfold ignore_nfirst_char.
simpl.
replace (String.length (substring n (String.length str - n) str) +
S (String.length (substring 0 n str))) with ( S(String.length (substring n (String.length str - n) str) + (String.length (substring 0 n str)))) by lia.
f_equal.
unfold ignore_nfirst_char in *.
apply IHstr.
Qed.

Lemma computeAction_dec_eq {Token Hist: Set} : forall regexp_x_action r (eof_action : Action (Token := Token) (Hist := Hist)) curAction last_matched_str str_to_lex start_pos param_pos history nhistory 
      tok_opt elect,
 computeAction Token Hist regexp_x_action eof_action str_to_lex start_pos param_pos history curAction last_matched_str tok_opt elect= (r, nhistory) -> String.length (extractRemainingString r) <= (String.length str_to_lex).
Proof.
intros.
functional induction computeAction Token Hist regexp_x_action eof_action str_to_lex start_pos
      param_pos history curAction last_matched_str tok_opt elect.
apply eof_on_action_remaining_str in H.
rewrite H; simpl; auto.
apply eof_on_action_remaining_str in H.
rewrite H; simpl; lia.
inversion H.
simpl.
apply semiActionCompute_dec_str_eq in e0.
simpl in e0.
auto.
apply IHp in H.
apply semiActionCompute_dec_str_eq in e0.
simpl in *.
assert (String.length
      (ignore_nfirst_char (resultNat elected) rem_str) <= String.length rem_str).
apply ignore_dec_length; lia.
lia.
apply semiActionCompute_dec_str_eq in e0.
apply semiActionCompute_dec_str_eq in e4.
inversion H.
simpl in *.
lia.
apply IHp in H.
apply semiActionCompute_dec_str_eq in e0.
apply semiActionCompute_dec_str_eq in e4.
simpl in *.
lia.
inversion H.
rewrite H1 in *.
apply semiActionCompute_dec_str_eq in e0.
apply semiActionCompute_dec_str_eq in e4.
simpl in *.
lia.
inversion H.
rewrite H1 in *.
apply semiActionCompute_dec_str_eq in e0.
auto.
Qed.

Lemma computeAction_start_cur_position_abs {Token Hist: Set} : forall regexp_x_action r (eof_action : Action (Token := Token) (Hist := Hist)) curAction last_matched_str str_to_lex start_pos param_pos history nhistory 
      tok_opt elect,
  computeAction Token Hist regexp_x_action eof_action str_to_lex start_pos param_pos history curAction last_matched_str tok_opt elect = (r, nhistory) -> abs_pos (extractCurrentPosition r) = abs_pos param_pos + ((String.length str_to_lex) - (String.length (extractRemainingString r))).
Proof.
intros.
functional induction computeAction Token Hist regexp_x_action eof_action str_to_lex start_pos param_pos history
      curAction last_matched_str tok_opt elect.
apply eof_on_action_abs_mov in H.
simpl.
lia.
assert (H':=H).
apply eof_on_action_abs_mov in H.
apply semiActionCompute_start_cur_position_abs in e0.
simpl in*.
apply eof_on_action_remaining_str in H'.
rewrite H' in *.
simpl in *; lia.
apply semiActionCompute_start_cur_position_abs in e0; simpl in e0.
inversion H.
simpl.
auto.
assert (H':=H).
assert (H'':=H).
apply IHp in H.
simpl in H.
assert (e0':=e0).
apply semiActionCompute_start_cur_position_abs in e0; simpl in e0.
rewrite e0 in H.
rewrite usefullSubstr2 in H.
apply computeAction_dec_eq in H'.
rewrite usefullSubstr2 in H'.
apply semiActionCompute_dec_str_eq in e0'.
simpl in *.
apply elector_inf_strLen in e2.
lia.
inversion H.
simpl in *.
apply semiActionCompute_start_cur_position_abs in e0; simpl in e0.
apply semiActionCompute_start_cur_position_abs in e4; simpl in e4.
apply EqNat.beq_nat_true in e5.
lia.
assert (e0':=e0).
assert (e4':=e4).
apply semiActionCompute_start_cur_position_abs in e0; simpl in e0.
apply semiActionCompute_start_cur_position_abs in e4; simpl in e4.
assert (H':=H).
apply IHp in H.
apply elector_inf_strLen in e2.
rewrite e0 in *.
rewrite e4 in *.
apply computeAction_dec_eq in H'.
apply semiActionCompute_dec_str_eq in e0'.
apply semiActionCompute_dec_str_eq in e4'.
simpl in *.
lia.
inversion H.
rewrite H1 in *.
assert (e0':=e0).
assert (e4':=e4).
apply semiActionCompute_start_cur_position_abs in e0; simpl in e0.
apply semiActionCompute_start_cur_position_abs in e4; simpl in e4.
rewrite e0 in *.
apply semiActionCompute_dec_str_eq in e0'.
apply semiActionCompute_dec_str_eq in e4'.
simpl in *.
lia.
inversion H.
rewrite H1 in *.
apply semiActionCompute_start_cur_position_abs in e0; simpl in e0.
auto.
Qed.

Lemma computeAction_interruption {Token Hist: Set} : forall regexp_x_action (eof_action : Action (Token := Token) (Hist := Hist)) curAction last_matched_str str_to_lex start_pos param_pos history nhistory last_m last_sp str ncur_pos' tok_opt elect, 
      computeAction Token Hist regexp_x_action eof_action str_to_lex start_pos param_pos history curAction last_matched_str tok_opt elect = (OneLexSpecNoToken last_m last_sp str ncur_pos', nhistory) -> positionLE start_pos param_pos -> positionLE start_pos last_sp.
Proof.
intros.
functional induction computeAction Token Hist regexp_x_action eof_action
       str_to_lex start_pos param_pos history curAction
       last_matched_str tok_opt elect; try inversion H.
apply eof_on_action_start_interruption in H; auto.
apply eof_on_action_start_interruption in H; auto.
apply semiActionCompute_start_interruption_position in e0; auto.
eapply positionLE_trans; eauto.
apply semiActionCompute_start_interruption_position2 in e0; auto.
apply IHp in H; auto.
apply semiActionCompute_start_cur_position in e0; simpl in e0.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
unfold positionLE; simpl; lia.
apply IHp in H; auto.
apply semiActionCompute_start_interruption_position in e4; auto.
apply semiActionCompute_start_interruption_position in e0; auto.
eapply positionLE_trans; eauto.
eapply positionLE_trans; eauto.
apply semiActionCompute_start_interruption_position2 in e0; auto.
apply semiActionCompute_start_interruption_position2 in e4; auto.
apply semiActionCompute_start_interruption_position2 in e0; auto.
rewrite H2 in *.
apply semiActionCompute_start_interruption_position in e4; auto.
apply semiActionCompute_start_interruption_position in e0; auto.
eapply positionLE_trans; eauto.
apply semiActionCompute_start_interruption_position2 in e0; auto.
rewrite H2 in *.
apply semiActionCompute_start_interruption_position in e0; auto.
Qed.

Lemma computeAction_interruption2 {Token Hist: Set} : forall regexp_x_action (eof_action : Action (Token := Token) (Hist := Hist)) curAction last_matched_str str_to_lex start_pos param_pos history nhistory last_m last_sp str ncur_pos' tok_opt elect, 
      computeAction Token Hist regexp_x_action eof_action str_to_lex start_pos param_pos history curAction last_matched_str tok_opt elect = (OneLexSpecNoToken last_m last_sp str ncur_pos', nhistory) -> positionLE start_pos param_pos -> positionLE last_sp ncur_pos'.
Proof.
intros.
functional induction computeAction Token Hist regexp_x_action eof_action
       str_to_lex start_pos param_pos history curAction
       last_matched_str tok_opt elect; try inversion H.
apply eof_on_action_start_interruption2 in H2; auto.
apply eof_on_action_start_interruption2 in H2; auto.
apply semiActionCompute_start_interruption_position2 in e0; auto.
apply IHp in H; auto.
unfold positionLE; simpl; lia.
apply IHp in H; auto.
apply semiActionCompute_start_interruption_position2 in e4; auto.
apply semiActionCompute_start_interruption_position2 in e0; auto.
rewrite H2 in *.
apply semiActionCompute_start_interruption_position2 in e4; auto.
apply semiActionCompute_start_interruption_position2 in e0; auto.
rewrite H2 in *.
apply semiActionCompute_start_interruption_position2 in e0; auto.
Qed.

Definition lexergenerator {Token Hist: Set} (elect : elector(Action := Action)) regexp_x_action (eof_action : Action (Token := Token) (Hist := Hist)) str_to_lex cur_position history := match str_to_lex with
| EmptyString => eof_process eof_action cur_position cur_position history EmptyString None
| _ => (match (elector_func elect) regexp_x_action str_to_lex with 
                     | None => (OneLexNoMatchErrorResult str_to_lex cur_position, history)
                     | Some elected => computeAction Token Hist regexp_x_action eof_action (ignore_nfirst_char (resultNat elected) str_to_lex) cur_position {| l_number := (l_number cur_position) ; c_number := (c_number cur_position) + (resultNat elected); 
                                                            abs_pos := (abs_pos cur_position) + (resultNat elected) |} history (resultAction elected) (substring 0 (resultNat elected) str_to_lex) None elect
                    end)
end.

Lemma lexergenerator_start_end_position {Token Hist: Set} : forall elect regexp_x_action (eof_action : Action (Token := Token) (Hist := Hist)) str_to_lex param_pos history nhistory r,
      (lexergenerator elect regexp_x_action eof_action str_to_lex param_pos history = (r, nhistory)) -> positionLE param_pos (extractCurrentPosition r).
Proof.
unfold lexergenerator.
unfold eof_process.
induction str_to_lex.
intros param_pos history.
case_eq (semiActionCompute eof_action "" param_pos history "" None
     param_pos).
intros.
induction p.
apply semiActionCompute_start_cur_position in H.
induction a0; inversion H0; auto.
induction a.
inversion H0; auto.
induction a; inversion H0; auto.
induction (elector_func elect regexp_x_action (String a str_to_lex)).
intros.
apply computeAction_start_end_position in H.
assert (positionLE param_pos {|
      l_number := l_number param_pos;
      c_number := c_number param_pos + resultNat a0;
      abs_pos := abs_pos param_pos + resultNat a0 |}).
unfold positionLE; simpl; lia.
eapply positionLE_trans; eauto.
intros.
inversion H.
simpl.
apply positionLE_ident.
Qed.

Lemma lexergenerator_tok_position {Token Hist: Set} : forall elect regexp_x_action (eof_action : Action (Token := Token) (Hist := Hist)) str_to_lex param_pos history nhistory ts_pos tok cur_pos tok_str_val
      remaining_str,
      (lexergenerator elect regexp_x_action eof_action str_to_lex param_pos history = (OneLexSResult
               {|
               token := {|
                        s_pos := ts_pos;
                        tok := tok;
                        str_val := tok_str_val |};
               cur_pos := cur_pos;
               remaining_str := remaining_str; |}, nhistory)) -> positionLE ts_pos cur_pos.
Proof.
unfold lexergenerator.
unfold eof_process.
induction str_to_lex.
intros param_pos history.
case_eq (semiActionCompute eof_action "" param_pos history "" None
     param_pos).
intros.
induction p.
induction a0; inversion H0.
rewrite H2 in H.
apply semiActionCompute_tok_position in H; auto.
apply positionLE_ident.
induction a.
inversion H0; auto.
induction a; inversion H0; auto.
induction (elector_func elect regexp_x_action (String a str_to_lex)).
intros.
apply computeAction_tok_position in H; auto.
unfold positionLE; simpl; lia.
intros.
inversion H.
Qed.

Lemma lexergenerator_start_tok_position {Token Hist: Set} : forall elect regexp_x_action (eof_action : Action (Token := Token) (Hist := Hist)) str_to_lex param_pos history nhistory ts_pos tok cur_pos tok_str_val
      remaining_str,
      (lexergenerator elect regexp_x_action eof_action str_to_lex param_pos history = (OneLexSResult
               {|
               token := {|
                        s_pos := ts_pos;
                        tok := tok;
                        str_val := tok_str_val |};
               cur_pos := cur_pos;
               remaining_str := remaining_str; |}, nhistory)) -> positionLE param_pos ts_pos.
Proof.
unfold lexergenerator.
unfold eof_process.
induction str_to_lex.
intros param_pos history.
case_eq (semiActionCompute eof_action "" param_pos history "" None
     param_pos).
intros.
induction p.
induction a0; inversion H0.
rewrite H2 in H.
apply semiActionCompute_start_tok_position in H; auto.
apply positionLE_ident.
induction a.
inversion H0; auto.
induction a; inversion H0; auto.
induction (elector_func elect regexp_x_action (String a str_to_lex)).
intros.
apply computeAction_start_tok_position in H; auto.
unfold positionLE; simpl; lia.
intros.
inversion H.
Qed.


Lemma lexergenerator_no_implementation_error {Token Hist: Set} : forall elect regexp_x_action (eof_action : Action (Token := Token) (Hist := Hist)) str ncur_pos nhist n history' ncur_pos' str', lexergenerator elect regexp_x_action eof_action str ncur_pos nhist = (OneLexImplementationError n str' ncur_pos', history') -> False.
Proof.
unfold lexergenerator.
unfold eof_process.
induction str.
intros param_pos history.
case_eq (semiActionCompute eof_action "" param_pos history "" None
     param_pos).
intros.
induction p.
induction a0; inversion H0.
induction a; inversion H0.
induction a; inversion H0.
apply semiActionCompute_no_implementation_error in H; auto.
induction (elector_func elect regexp_x_action (String a str)).
intros.
apply computeAction_safe in H; auto.
intros.
inversion H.
Qed.

Lemma lexergenerator_start_cur_position_abs {Token Hist: Set} : forall elect regexp_x_action (eof_action : Action (Token := Token) (Hist := Hist)) str_to_lex param_pos history nhistory r
      ,
      (lexergenerator elect regexp_x_action eof_action str_to_lex param_pos history = (r, nhistory)) -> abs_pos (extractCurrentPosition r) = abs_pos param_pos + ((String.length str_to_lex) - (String.length (extractRemainingString r))).
Proof.
unfold lexergenerator.
unfold eof_process.
induction str_to_lex.
intros param_pos history.
case_eq (semiActionCompute eof_action "" param_pos history "" None
     param_pos).
intros.
induction p.
apply semiActionCompute_start_cur_position_abs in H.
induction a0; inversion H0; simpl in *; auto.
induction a.
inversion H0; auto.
induction a; inversion H0; auto.
intros.
case_eq (elector_func elect regexp_x_action (String a str_to_lex)).
intros.
rewrite H0 in H.
assert (H':=H).
apply computeAction_start_cur_position_abs in H.
simpl in H.
rewrite usefullSubstr2 in H.
apply computeAction_dec_eq in H'.
rewrite usefullSubstr2 in H'.
apply elector_inf_strLen in H0.
lia.
intros.
rewrite H0 in H.
inversion H.
simpl.
lia.
Qed.

Lemma lexergenerator_correct_consum {Token Hist: Set} : forall elect regexp_x_action (eof_action : Action (Token := Token) (Hist := Hist)) str_to_lex param_pos history nhistory r
      ,
      (lexergenerator elect regexp_x_action eof_action str_to_lex param_pos history = (r, nhistory)) -> extractRemainingString r = ignore_nfirst_char ((abs_pos (extractCurrentPosition r)) - (abs_pos param_pos)) str_to_lex.
Proof.
unfold lexergenerator.
unfold eof_process.
induction str_to_lex.
intros param_pos history.
case_eq (semiActionCompute eof_action "" param_pos history "" None
     param_pos).
intros.
induction p.
apply semiActionCompute_correct_consum in H.
induction a0; inversion H0; simpl in *; auto.
induction a.
inversion H0; auto.
induction a; inversion H0; auto.
simpl.
unfold ignore_nfirst_char.
simpl.
induction (abs_pos p0 - abs_pos param_pos); auto.
intros.
case_eq (elector_func elect regexp_x_action (String a str_to_lex)).
intros.
rewrite H0 in H.
assert (H':=H).
apply computeAction_correct_consum in H.
simpl in H.
rewrite ignore_usefull in H.
apply computeAction_start_cur_position_abs in H'.
simpl in H'.
rewrite H.
f_equal.
rewrite usefullSubstr2 in H'.
apply elector_inf_strLen in H0.
lia.
intros.
rewrite H0 in H.
inversion H.
simpl.
replace (abs_pos param_pos - abs_pos param_pos) with 0 by lia.
unfold ignore_nfirst_char.
replace (String.length (String a str_to_lex) - 0) with (String.length (String a str_to_lex)) by lia.
rewrite substr_0_len_str.
auto.
Qed.

Lemma lexergenerator_start_interruption_position {Token Hist: Set} : forall elect regexp_x_action (eof_action : Action (Token := Token) (Hist := Hist)) str_to_lex param_pos history nhistory ts_pos cur_pos tok_str_val remaining_str,
      (lexergenerator elect regexp_x_action eof_action str_to_lex param_pos history = (OneLexSpecNoToken tok_str_val ts_pos remaining_str cur_pos, nhistory)) -> positionLE param_pos ts_pos.
Proof.
unfold lexergenerator.
unfold eof_process.
induction str_to_lex.
intros param_pos history.
case_eq (semiActionCompute eof_action "" param_pos history "" None
     param_pos).
intros.
induction p.
induction a0; inversion H0.
induction a; inversion H0.
rewrite H2 in *.
apply semiActionCompute_start_interruption_position in H; auto.
apply positionLE_ident.
clear IHa.
clear H3.
clear H2.
apply semiActionCompute_start_interruption_position in H; auto.
induction a; inversion H0; rewrite H3 in *; auto.
apply positionLE_ident.
induction (elector_func elect regexp_x_action (String a str_to_lex)).
intros.
apply computeAction_interruption in H; auto.
unfold positionLE; simpl; lia.
intros.
inversion H.
Qed.

Lemma lexergenerator_start_interruption_position2 {Token Hist: Set} : forall elect regexp_x_action (eof_action : Action (Token := Token) (Hist := Hist)) str_to_lex param_pos history nhistory ts_pos cur_pos tok_str_val remaining_str,
      (lexergenerator elect regexp_x_action eof_action str_to_lex param_pos history = (OneLexSpecNoToken tok_str_val ts_pos remaining_str cur_pos, nhistory)) -> positionLE ts_pos cur_pos.
Proof.
unfold lexergenerator.
unfold eof_process.
induction str_to_lex.
intros param_pos history.
case_eq (semiActionCompute eof_action "" param_pos history "" None
     param_pos).
intros.
induction p.
induction a0; inversion H0.
induction a; inversion H0.
rewrite H2 in *.
apply semiActionCompute_start_interruption_position2 in H; auto.
apply positionLE_ident.
clear IHa.
clear H3.
clear H2.
apply semiActionCompute_start_interruption_position2 in H; auto.
induction a; inversion H0; rewrite H3 in *; rewrite H5 in *; auto.
apply positionLE_ident.
induction (elector_func elect regexp_x_action (String a str_to_lex)).
intros.
apply computeAction_interruption2 in H; auto.
unfold positionLE; simpl; lia.
intros.
inversion H.
Qed.

Definition parseElector {Action : Set}:= mkElector Action election election_inf_strLen.

Definition make_lexer {Token Hist : Set} regexp_x_action (eof_action : Action (Token := Token) (Hist := Hist)) := 
  mkRecLexer 
    Token 
    Hist
    (lexergenerator parseElector regexp_x_action eof_action) 
    (lexergenerator_start_end_position parseElector regexp_x_action eof_action)
    (lexergenerator_tok_position parseElector regexp_x_action eof_action)
    (lexergenerator_start_tok_position parseElector regexp_x_action eof_action)
    (lexergenerator_start_cur_position_abs parseElector regexp_x_action eof_action)
    (lexergenerator_correct_consum parseElector regexp_x_action eof_action)
    (lexergenerator_no_implementation_error parseElector regexp_x_action eof_action)
    (lexergenerator_start_interruption_position parseElector regexp_x_action eof_action)
    (lexergenerator_start_interruption_position2 parseElector regexp_x_action eof_action) 
.

(*Helpers****)
Definition new_line p : Position := match p with
| {| l_number := l; c_number := c; abs_pos := abs|} => {| l_number := (S l); c_number := 0; abs_pos := abs|}
end.

Lemma new_line_correct_le : forall p, positionLE p (new_line p).
Proof.
unfold positionLE.
induction p.
simpl; lia.
Qed.

Lemma new_line_correct_abs : forall p, abs_pos p = abs_pos (new_line p).
Proof.
unfold new_line.
induction p.
simpl; lia.
Qed.

Definition newline {Token Hist: Set} : AtomicAction (Token := Token) (Hist := Hist) := PosHandler (mkPosChanger  new_line new_line_correct_le new_line_correct_abs).

Definition OPos := {| l_number := 1;  c_number := 0;  abs_pos := 0 |}.

Definition flush_whole_history {Token: Set} : AtomicAction (Token := Token) (Hist := string) :=  HistoryHandler (fun _ _ _ _ _ _ => EmptyString).

Definition keep_matched_str {Token: Set} : AtomicAction (Token := Token) (Hist := string) :=  HistoryHandler (fun matched_str _ _ _ _ last_history => String.append last_history matched_str).

Definition ignore_matched_str_history {Token Hist: Set} : AtomicAction (Token := Token) (Hist := Hist) := HistoryHandler (fun matched_str _ _ _ _ last_history => last_history).

Definition simplyReturnToken {Token Hist: Set} (tok : Token) : Action (Token := Token) (Hist := Hist):= [TokenReturn (fun _ _ _ _ _ h => (ResultOk tok, h))].

Definition simplyRaiseError {Token Hist: Set} msg : Action (Token := Token) (Hist := Hist) := [TokenReturn (fun _ _ _ _ _ h => (ResultError msg, h))].

(*Lexer definition*)
Definition if_true_err_else_no_token_lexer_generator {Token Hist: Set} (evaluator : Hist -> bool) msg str_to_lex cur_position history : OneLexResult(Token := Token) * Hist := 
if evaluator history then (OneLexUserDefinitionErrorResult msg str_to_lex cur_position, history)
else (OneLexSpecNoToken EmptyString cur_position str_to_lex cur_position, history).

Lemma if_true_err_else_no_token_lexer_start_cur_position {Token Hist: Set} : forall (evaluator : Hist -> bool) err_msg str_to_lex param_pos history nhistory r
      ,
      (if_true_err_else_no_token_lexer_generator(Token := Token) evaluator err_msg str_to_lex param_pos history = (r, nhistory)) -> positionLE param_pos (extractCurrentPosition r).
Proof.
unfold if_true_err_else_no_token_lexer_generator.
intros.
induction (evaluator history); inversion H; simpl; apply positionLE_ident.
Qed.

Lemma if_true_err_else_no_token_lexer_tok_position {Token Hist: Set} : forall (evaluator : Hist -> bool) err_msg str_to_lex param_pos history nhistory ts_pos (tok : Token) cur_pos tok_str_val
      remaining_str,
      (if_true_err_else_no_token_lexer_generator evaluator err_msg str_to_lex param_pos history = (OneLexSResult
               {|
               token := {|
                        s_pos := ts_pos;
                        tok := tok;
                        str_val := tok_str_val |};
               cur_pos := cur_pos;
               remaining_str := remaining_str; |}, nhistory)) -> positionLE ts_pos cur_pos.
Proof.
unfold if_true_err_else_no_token_lexer_generator.
intros.
induction (evaluator history); inversion H.
Qed.

Lemma if_true_err_else_no_token_lexer_start_tok_position {Token Hist: Set} : forall (evaluator : Hist -> bool) err_msg str_to_lex param_pos history nhistory ts_pos (tok : Token) cur_pos tok_str_val
      remaining_str,
      (if_true_err_else_no_token_lexer_generator evaluator err_msg str_to_lex param_pos history = (OneLexSResult
               {|
               token := {|
                        s_pos := ts_pos;
                        tok := tok;
                        str_val := tok_str_val |};
               cur_pos := cur_pos;
               remaining_str := remaining_str; |}, nhistory)) -> positionLE param_pos ts_pos.
Proof.
unfold if_true_err_else_no_token_lexer_generator.
intros.
induction (evaluator history); inversion H.
Qed.

Lemma if_true_err_else_no_token_lexer_start_cur_position_abs {Token Hist: Set} : forall (evaluator : Hist -> bool) err_msg str_to_lex param_pos history nhistory r
      ,
      (if_true_err_else_no_token_lexer_generator(Token := Token) evaluator err_msg str_to_lex param_pos history = (r, nhistory)) -> abs_pos (extractCurrentPosition r) = abs_pos param_pos + ((String.length str_to_lex) - (String.length (extractRemainingString r))).
Proof.
unfold if_true_err_else_no_token_lexer_generator.
intros.
induction (evaluator history); inversion H; simpl; lia.
Qed.


Lemma if_true_err_else_no_token_lexer_correct_consum {Token Hist: Set} : forall (evaluator : Hist -> bool) err_msg str_to_lex param_pos history nhistory r
      ,
      (if_true_err_else_no_token_lexer_generator(Token := Token) evaluator err_msg str_to_lex param_pos history = (r, nhistory)) -> extractRemainingString r = ignore_nfirst_char ((abs_pos (extractCurrentPosition r)) - (abs_pos param_pos)) str_to_lex.
Proof.
unfold if_true_err_else_no_token_lexer_generator.
intros.
induction (evaluator history); inversion H; simpl; replace (abs_pos param_pos - abs_pos param_pos) with 0 by lia; unfold ignore_nfirst_char; replace (String.length str_to_lex - 0) with (String.length str_to_lex) by lia; rewrite substr_0_len_str; auto.
Qed.

Lemma if_true_err_else_no_token_lexer_no_implementation_error {Token Hist: Set} : forall (evaluator : Hist -> bool) err_msg str ncur_pos nhist n history' ncur_pos' rem, 
if_true_err_else_no_token_lexer_generator(Token := Token)(Hist := Hist) evaluator err_msg str ncur_pos nhist = (OneLexImplementationError n rem ncur_pos', history') -> False.
Proof.
unfold if_true_err_else_no_token_lexer_generator.
intros.
induction (evaluator nhist); inversion H; simpl; lia.
Qed.

Lemma if_true_err_else_no_token_lexer_start_interruption_position {Token Hist: Set} : forall (evaluator : Hist -> bool) err_msg str_to_lex param_pos history nhistory ts_pos cur_pos tok_str_val
      remaining_str,
      if_true_err_else_no_token_lexer_generator(Token := Token)(Hist := Hist) evaluator err_msg str_to_lex param_pos history = (OneLexSpecNoToken tok_str_val ts_pos remaining_str cur_pos, nhistory) -> positionLE param_pos ts_pos.
Proof.
unfold if_true_err_else_no_token_lexer_generator.
intros.
induction (evaluator history); inversion H; apply positionLE_ident.
Qed.

Lemma if_true_err_else_no_token_lexer_start_interruption_position2 {Token Hist: Set} : forall (evaluator : Hist -> bool) err_msg str_to_lex param_pos history nhistory ts_pos cur_pos tok_str_val
      remaining_str,
      if_true_err_else_no_token_lexer_generator(Token := Token)(Hist := Hist) evaluator err_msg str_to_lex param_pos history = (OneLexSpecNoToken tok_str_val ts_pos remaining_str cur_pos, nhistory) -> positionLE ts_pos cur_pos.
Proof.
unfold if_true_err_else_no_token_lexer_generator.
intros.
induction (evaluator history); inversion H; apply positionLE_ident.
Qed.


Definition make_if_true_err_else_no_token_lexer {Token Hist : Set} (evaluator : Hist -> bool) err_msg := 
  mkRecLexer 
    Token 
    Hist
    (if_true_err_else_no_token_lexer_generator evaluator err_msg) 
    (if_true_err_else_no_token_lexer_start_cur_position evaluator err_msg)
    (if_true_err_else_no_token_lexer_tok_position evaluator err_msg)
    (if_true_err_else_no_token_lexer_start_tok_position evaluator err_msg)
    (if_true_err_else_no_token_lexer_start_cur_position_abs evaluator err_msg)
    (if_true_err_else_no_token_lexer_correct_consum evaluator err_msg)
    (if_true_err_else_no_token_lexer_no_implementation_error evaluator err_msg)
    (if_true_err_else_no_token_lexer_start_interruption_position evaluator err_msg)
    (if_true_err_else_no_token_lexer_start_interruption_position2 evaluator err_msg)
.

Definition if_then_else {Token Hist: Set} (evaluator : Hist -> bool) (lexer_true : RecLexer (Token:=Token) (Hist:=Hist)) (lexer_false : RecLexer (Token:=Token) (Hist:=Hist)) str_to_lex cur_position history : OneLexResult(Token := Token) * Hist := 
if evaluator history then (lexer lexer_true) str_to_lex cur_position history
else (lexer lexer_false) str_to_lex cur_position history.

Lemma if_then_else_start_cur_position {Token Hist: Set} : forall (evaluator : Hist -> bool) ltrue lfalse str_to_lex param_pos history nhistory r
      ,
      (if_then_else(Token := Token) evaluator ltrue lfalse str_to_lex param_pos history = (r, nhistory)) -> positionLE param_pos (extractCurrentPosition r).
Proof.
unfold if_then_else.
intros.
induction (evaluator history); inversion H; simpl; apply lexer_start_cur_position in H; auto.
Qed.

Lemma if_then_else_tok_position {Token Hist: Set} : forall (evaluator : Hist -> bool) ltrue lfalse str_to_lex param_pos history nhistory ts_pos (tok : Token) cur_pos tok_str_val
      remaining_str,
      (if_then_else(Token := Token) evaluator ltrue lfalse str_to_lex param_pos history = (OneLexSResult
               {|
               token := {|
                        s_pos := ts_pos;
                        tok := tok;
                        str_val := tok_str_val |};
               cur_pos := cur_pos;
               remaining_str := remaining_str; |}, nhistory)) -> positionLE ts_pos cur_pos.
Proof.
unfold if_then_else.
intros.
induction (evaluator history); inversion H; simpl; apply lexer_tok_position in H; auto.
Qed.

Lemma if_then_else_start_tok_position {Token Hist: Set} : forall (evaluator : Hist -> bool) ltrue lfalse str_to_lex param_pos history nhistory ts_pos (tok : Token) cur_pos tok_str_val
      remaining_str,
      (if_then_else evaluator ltrue lfalse str_to_lex param_pos history = (OneLexSResult
               {|
               token := {|
                        s_pos := ts_pos;
                        tok := tok;
                        str_val := tok_str_val |};
               cur_pos := cur_pos;
               remaining_str := remaining_str; |}, nhistory)) -> positionLE param_pos ts_pos.
Proof.
unfold if_then_else.
intros.
induction (evaluator history); inversion H; simpl; apply lexer_start_tok_position in H; auto.
Qed.

Lemma if_then_else_start_cur_position_abs {Token Hist: Set} : forall (evaluator : Hist -> bool) ltrue lfalse str_to_lex param_pos history nhistory r
      ,
      (if_then_else(Token := Token) evaluator ltrue lfalse str_to_lex param_pos history = (r, nhistory)) -> abs_pos (extractCurrentPosition r) = abs_pos param_pos + ((String.length str_to_lex) - (String.length (extractRemainingString r))).
Proof.
unfold if_then_else.
intros.
induction (evaluator history); inversion H; simpl; apply lexer_start_cur_position_abs in H; auto.
Qed.


Lemma if_then_else_correct_consum {Token Hist: Set} : forall (evaluator : Hist -> bool) ltrue lfalse str_to_lex param_pos history nhistory r
      ,
      (if_then_else(Token := Token) evaluator ltrue lfalse str_to_lex param_pos history = (r, nhistory)) -> extractRemainingString r = ignore_nfirst_char ((abs_pos (extractCurrentPosition r)) - (abs_pos param_pos)) str_to_lex.
Proof.
unfold if_then_else.
intros.
induction (evaluator history); inversion H; simpl; apply lexer_correct_consum in H; auto.
Qed.

Lemma if_then_else_no_implementation_error {Token Hist: Set} : forall (evaluator : Hist -> bool) ltrue lfalse str ncur_pos nhist n history' ncur_pos' rem, 
if_then_else(Token := Token)(Hist := Hist) evaluator ltrue lfalse str ncur_pos nhist = (OneLexImplementationError n rem ncur_pos', history') -> False.
Proof.
unfold if_then_else.
intros.
induction (evaluator nhist); inversion H; simpl; apply lexer_no_implementation_error in H; auto.
Qed.

Lemma if_then_else_start_interruption_position {Token Hist: Set} : forall (evaluator : Hist -> bool) ltrue lfalse str_to_lex param_pos history nhistory ts_pos cur_pos tok_str_val
      remaining_str,
      if_then_else(Token := Token)(Hist := Hist) evaluator ltrue lfalse str_to_lex param_pos history = (OneLexSpecNoToken tok_str_val ts_pos remaining_str cur_pos, nhistory) -> positionLE param_pos ts_pos.
Proof.
unfold if_then_else.
intros.
induction (evaluator history); inversion H; simpl; apply lexer_start_interruption_position in H; auto.
Qed.

Lemma if_then_else_start_interruption_position2 {Token Hist: Set} : forall (evaluator : Hist -> bool) ltrue lfalse str_to_lex param_pos history nhistory ts_pos cur_pos tok_str_val
      remaining_str,
      if_then_else(Token := Token) evaluator ltrue lfalse str_to_lex param_pos history = (OneLexSpecNoToken tok_str_val ts_pos remaining_str cur_pos, nhistory) -> positionLE ts_pos cur_pos.
Proof.
unfold if_then_else.
intros.
induction (evaluator history); inversion H; simpl; apply lexer_start_interruption_position2 in H; auto.
Qed.

Definition if_then_else_generator {Token Hist : Set} (evaluator : Hist -> bool) ltrue lfalse := 
  mkRecLexer 
    Token 
    Hist
    (if_then_else evaluator ltrue lfalse) 
    (if_then_else_start_cur_position evaluator ltrue lfalse)
    (if_then_else_tok_position evaluator ltrue lfalse)
    (if_then_else_start_tok_position evaluator ltrue lfalse)
    (if_then_else_start_cur_position_abs evaluator ltrue lfalse)
    (if_then_else_correct_consum evaluator ltrue lfalse)
    (if_then_else_no_implementation_error evaluator ltrue lfalse)
    (if_then_else_start_interruption_position evaluator ltrue lfalse)
    (if_then_else_start_interruption_position2 evaluator ltrue lfalse)
.

Definition ignore_token {Token Token' Hist: Set} (lexer_f : RecLexer (Token:=Token) (Hist:=Hist)) str_to_lex cur_position history : OneLexResult(Token := Token') * Hist := 
match (lexer lexer_f) str_to_lex cur_position history with
| (OneLexSResult
               {|
               token := {|
                        s_pos := ts_pos;
                        tok := tok;
                        str_val := tok_str_val |};
               cur_pos := cur_pos;
               remaining_str := remaining_str; |}, history) => (OneLexSpecNoToken tok_str_val ts_pos remaining_str cur_pos, history)
| (OneLexUserDefinitionErrorResult msg remaining_str cur_pos, history) => (OneLexUserDefinitionErrorResult msg remaining_str cur_pos, history)
| (OneLexSpecNoToken tok_str_val ts_pos remaining_str cur_pos, history) => (OneLexSpecNoToken tok_str_val ts_pos remaining_str cur_pos, history)
| (OneLexSpecError msg remaining_str cur_pos, history) => (OneLexSpecError msg remaining_str cur_pos, history)
| (OneLexImplementationError n remaining_str cur_pos, history) => (OneLexImplementationError n remaining_str cur_pos, history)
| (OneLexNoMatchErrorResult remaining_str cur_pos, history) => (OneLexNoMatchErrorResult remaining_str cur_pos, history)
| (OneLexLoop remaining_str cur_pos, history) => (OneLexLoop remaining_str cur_pos, history)
end.

Lemma ignore_token_start_cur_position {Token Token' Hist: Set} : forall lexer_f str_to_lex param_pos history nhistory r
      ,
      (ignore_token (Token:=Token) (Token':=Token') (Hist:=Hist) lexer_f str_to_lex param_pos history = (r, nhistory)) -> positionLE param_pos (extractCurrentPosition r).
Proof.
unfold ignore_token.
intros.
case_eq (lexer lexer_f str_to_lex param_pos history); intros; rewrite H0 in H.
induction o.
induction o.
induction token0.
inversion H.
simpl.
apply lexer_start_cur_position in H0; simpl in H0; auto.
inversion H; apply lexer_start_cur_position in H0; simpl in *; auto.
inversion H; apply lexer_start_cur_position in H0; simpl in *; auto.
inversion H; apply lexer_start_cur_position in H0; simpl in *; auto.
inversion H; apply lexer_start_cur_position in H0; simpl in *; auto.
inversion H; apply lexer_start_cur_position in H0; simpl in *; auto.
inversion H; apply lexer_start_cur_position in H0; simpl in *; auto.
Qed.

Lemma ignore_token_tok_position {Token Token' Hist: Set} : forall (lexer_f : RecLexer (Token:=Token) (Hist:=Hist)) str_to_lex param_pos history nhistory ts_pos (tok : Token') cur_pos tok_str_val
      remaining_str,
      (ignore_token (Token:=Token) (Token':=Token') (Hist:=Hist) lexer_f str_to_lex param_pos history = (OneLexSResult
               {|
               token := {|
                        s_pos := ts_pos;
                        tok := tok;
                        str_val := tok_str_val |};
               cur_pos := cur_pos;
               remaining_str := remaining_str; |}, nhistory)) -> positionLE ts_pos cur_pos.
Proof.
unfold ignore_token.
intros.
case_eq (lexer lexer_f str_to_lex param_pos history); intros; rewrite H0 in H; induction o; try inversion H.
clear H2.
induction o.
induction token0.
inversion H.
Qed.

Lemma ignore_token_start_tok_position {Token Token' Hist: Set} : forall (lexer_f : RecLexer (Token:=Token) (Hist:=Hist)) str_to_lex param_pos history nhistory ts_pos (tok : Token') cur_pos tok_str_val
      remaining_str,
      (ignore_token (Token:=Token) (Token':=Token') (Hist:=Hist) lexer_f str_to_lex param_pos history = (OneLexSResult
               {|
               token := {|
                        s_pos := ts_pos;
                        tok := tok;
                        str_val := tok_str_val |};
               cur_pos := cur_pos;
               remaining_str := remaining_str; |}, nhistory)) -> positionLE param_pos ts_pos.
Proof.
unfold ignore_token.
intros.
case_eq (lexer lexer_f str_to_lex param_pos history); intros; rewrite H0 in H; induction o; try inversion H.
clear H2.
induction o.
induction token0.
inversion H.
Qed.

Lemma ignore_token_start_cur_position_abs {Token Token' Hist: Set} : forall (lexer_f : RecLexer (Token:=Token) (Hist:=Hist)) str_to_lex param_pos history nhistory r
      ,
      (ignore_token (Token:=Token) (Token':=Token') (Hist:=Hist) lexer_f str_to_lex param_pos history = (r, nhistory)) -> abs_pos (extractCurrentPosition r) = abs_pos param_pos + ((String.length str_to_lex) - (String.length (extractRemainingString r))).
Proof.
unfold ignore_token.
intros.
case_eq (lexer lexer_f str_to_lex param_pos history); intros; rewrite H0 in H.
induction o.
induction o.
induction token0.
inversion H.
simpl.
apply lexer_start_cur_position_abs in H0; simpl in H0; auto.
inversion H; apply lexer_start_cur_position_abs in H0; simpl in *; auto.
inversion H; apply lexer_start_cur_position_abs in H0; simpl in *; auto.
inversion H; apply lexer_start_cur_position_abs in H0; simpl in *; auto.
inversion H; apply lexer_start_cur_position_abs in H0; simpl in *; auto.
inversion H; apply lexer_start_cur_position_abs in H0; simpl in *; auto.
inversion H; apply lexer_start_cur_position_abs in H0; simpl in *; auto.
Qed.


Lemma ignore_token_correct_consum {Token Token' Hist: Set} : forall (lexer_f : RecLexer (Token:=Token) (Hist:=Hist)) str_to_lex param_pos history nhistory r
      ,
      (ignore_token (Token:=Token) (Token':=Token') (Hist:=Hist) lexer_f str_to_lex param_pos history = (r, nhistory)) -> extractRemainingString r = ignore_nfirst_char ((abs_pos (extractCurrentPosition r)) - (abs_pos param_pos)) str_to_lex.
Proof.
unfold ignore_token.
intros.
case_eq (lexer lexer_f str_to_lex param_pos history); intros; rewrite H0 in H.
induction o.
induction o.
induction token0.
inversion H.
simpl.
apply lexer_correct_consum in H0; simpl in H0; auto.
inversion H; apply lexer_correct_consum in H0; simpl in *; auto.
inversion H; apply lexer_correct_consum in H0; simpl in *; auto.
inversion H; apply lexer_correct_consum in H0; simpl in *; auto.
inversion H; apply lexer_correct_consum in H0; simpl in *; auto.
inversion H; apply lexer_correct_consum in H0; simpl in *; auto.
inversion H; apply lexer_correct_consum in H0; simpl in *; auto.
Qed.

Lemma ignore_token_no_implementation_error {Token Token' Hist: Set} : forall (lexer_f : RecLexer (Token:=Token) (Hist:=Hist)) str ncur_pos nhist n history' ncur_pos' rem, 
ignore_token (Token:=Token) (Token':=Token') (Hist:=Hist) lexer_f str ncur_pos nhist = (OneLexImplementationError n rem ncur_pos', history') -> False.
Proof.
unfold ignore_token.
intros.
case_eq (lexer lexer_f str ncur_pos nhist); intros; rewrite H0 in H.
induction o; inversion H.
induction o.
induction token0.
inversion H.
apply lexer_no_implementation_error in H0; auto.
Qed.

Lemma ignore_token_start_interruption_position {Token Token' Hist: Set} : forall (lexer_f : RecLexer (Token:=Token) (Hist:=Hist)) str_to_lex param_pos history nhistory ts_pos cur_pos tok_str_val
      remaining_str,
      ignore_token (Token:=Token) (Token':=Token') (Hist:=Hist) lexer_f str_to_lex param_pos history = (OneLexSpecNoToken tok_str_val ts_pos remaining_str cur_pos, nhistory) -> positionLE param_pos ts_pos.
Proof.
unfold ignore_token.
intros.
case_eq (lexer lexer_f str_to_lex param_pos history); intros; rewrite H0 in H.
induction o.
induction o.
induction token0.
inversion H.
apply lexer_start_tok_position in H0; simpl in H0.
rewrite H3 in *; auto.
inversion H.
inversion H.
apply lexer_start_interruption_position in H0.
rewrite H3 in *; auto.
inversion H.
inversion H.
inversion H.
inversion H.
Qed.

Lemma ignore_token_start_interruption_position2 {Token Token' Hist: Set} : forall (lexer_f : RecLexer (Token:=Token) (Hist:=Hist)) str_to_lex param_pos history nhistory ts_pos cur_pos tok_str_val
      remaining_str,
      ignore_token (Token:=Token) (Token':=Token') (Hist:=Hist) lexer_f str_to_lex param_pos history = (OneLexSpecNoToken tok_str_val ts_pos remaining_str cur_pos, nhistory) -> positionLE ts_pos cur_pos.
Proof.
unfold ignore_token.
intros.
case_eq (lexer lexer_f str_to_lex param_pos history); intros; rewrite H0 in H.
induction o.
induction o.
induction token0.
inversion H.
apply lexer_tok_position in H0; simpl in H0.
rewrite H3 in *; rewrite H5 in *; auto.
inversion H.
inversion H.
apply lexer_start_interruption_position2 in H0.
rewrite H3 in *; rewrite H5 in *; auto.
inversion H.
inversion H.
inversion H.
inversion H.
Qed.

Definition ignore {Token Token' Hist : Set} (lexer_f : RecLexer (Token:=Token) (Hist:=Hist)) := 
  mkRecLexer 
    Token 
    Hist
    (ignore_token lexer_f) 
    (ignore_token_start_cur_position lexer_f)
    (ignore_token_tok_position lexer_f)
    (ignore_token_start_tok_position lexer_f)
    (ignore_token_start_cur_position_abs lexer_f)
    (ignore_token_correct_consum lexer_f)
    (ignore_token_no_implementation_error lexer_f)
    (ignore_token_start_interruption_position lexer_f)
    (ignore_token_start_interruption_position2 lexer_f)
.


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

Inductive MaxLen :=
| NeverSucced : MaxLen
| CanSucced : nat -> MaxLen
| InfSucced : MaxLen.

Fixpoint computeMaxPossibleLen re :=
match re with
| Empty => NeverSucced
| Eps => CanSucced 0
| Char a => CanSucced 1
| Cat r1 r2 => (match computeMaxPossibleLen r1, computeMaxPossibleLen r2 with
                | NeverSucced, _ => NeverSucced
                | _, NeverSucced => NeverSucced
                | InfSucced, _ => InfSucced
                | _, InfSucced => InfSucced
                | CanSucced a, CanSucced b => CanSucced (a + b)
                end)
| Or r1 r2 => (match computeMaxPossibleLen r1, computeMaxPossibleLen r2 with
                | NeverSucced, b => b
                | a, NeverSucced => a
                | _, InfSucced => InfSucced
                | InfSucced, _ => InfSucced
                | CanSucced a, CanSucced b => CanSucced (if a <? b then b else a)
                end)
| Star r => (match computeMaxPossibleLen r with
                | NeverSucced => CanSucced 0
                | CanSucced 0 => CanSucced 0
                | _ => InfSucced
            end)
| Not r => InfSucced
| And r1 r2 => (match computeMaxPossibleLen r1, computeMaxPossibleLen r2 with
                | NeverSucced, _ => NeverSucced
                | _, NeverSucced => NeverSucced
                | a, InfSucced => a
                | InfSucced, b => b
                | CanSucced a, CanSucced b => CanSucced (if a <? b then a else b)
                end)
end.

Lemma And_left_empty_s : forall r, And Empty r =R= Empty.
Proof.
intros.
unfold re_eq.
intros.
rewrite matches_And.
case_eq (Empty ~= s).
intros.
assert (Empty ~!= s).
apply Empty_false.
rewrite H in H0.
discriminate.
auto.
Qed.

Lemma And_right_empty_s : forall r, And r Empty =R= Empty.
Proof.
intros.
unfold re_eq.
intros.
rewrite matches_And.
case_eq (Empty ~= s).
intros.
assert (Empty ~!= s).
apply Empty_false.
rewrite H in H0.
discriminate.
induction (r ~= s); auto.
Qed.

Lemma computeMaxPossibleLenCorrectNeverSucced : forall re, computeMaxPossibleLen re = NeverSucced -> re =R= Empty.
Proof.
induction re; simpl; try discriminate.
intros.
apply re_eq_refl.
case_eq (computeMaxPossibleLen re1); try discriminate; intro.
intros.
apply IHre1 in H.
rewrite H.
apply Cat_left_zero.
case_eq (computeMaxPossibleLen re2); try discriminate intro.
intros.
apply IHre2 in H.
rewrite H.
apply Cat_right_zero.
discriminate.
discriminate.
case_eq (computeMaxPossibleLen re2); try discriminate intro.
intros.
apply IHre2 in H0.
rewrite H0.
apply Cat_right_zero.
discriminate.
discriminate.
case_eq (computeMaxPossibleLen re1); try discriminate; intro.
case_eq (computeMaxPossibleLen re2); try discriminate; intro.
intros.
apply IHre1 in H.
apply IHre2 in H0.
rewrite H.
rewrite H0.
apply Or_left_id.
case_eq (computeMaxPossibleLen re2); try discriminate; intro.
case_eq (computeMaxPossibleLen re2); try discriminate; intro.
case_eq (computeMaxPossibleLen re); try discriminate; intro.
induction n; discriminate.
case_eq (computeMaxPossibleLen re1); try discriminate; intro.
intros.
apply IHre1 in H.
rewrite H.
apply And_left_empty_s.
case_eq (computeMaxPossibleLen re2); try discriminate; intro.
intros.
apply IHre2 in H.
rewrite H.
apply And_right_empty_s.
case_eq (computeMaxPossibleLen re2); try discriminate; intro.
apply IHre2 in H0.
rewrite H0.
intros.
apply And_right_empty_s.
Qed.

Lemma match_len_Empty : forall s, match_len Empty s = None.
Proof.
induction s; simpl; auto.
rewrite IHs; auto.
Qed.

Lemma match_len_Eps : forall s, match_len Eps s = Some 0.
Proof.
induction s; simpl; auto.
rewrite match_len_Empty; auto.
Qed.

Lemma match_len_Char : forall s a n, match_len (Char a) s = Some n -> n = 1.
Proof.
induction s; simpl; try discriminate.
intros.
induction (ascii_dec a0 a).
rewrite match_len_Eps in H.
inversion H; auto.
rewrite match_len_Empty in H.
discriminate.
Qed.

Lemma match_lenOr_left_None : forall str re1 re2, match_len re1 str = None ->  match_len (Or re1 re2) str = match_len re2 str.
Proof.
induction str.
simpl.
intros re1 re2.
induction (nu re1), (nu re2); try discriminate; simpl; auto.
simpl.
intro.
case_eq (match_len (re1 / a) str); try discriminate.
intros H re2.
induction (nu re1); try discriminate; simpl.
intros.
rewrite IHstr; auto.
Qed.

Lemma match_lenOr_right_None : forall str re1 re2, match_len re2 str = None ->  match_len (Or re1 re2) str = match_len re1 str.
Proof.
induction str.
simpl.
intros re1 re2.
induction (nu re1), (nu re2); try discriminate; simpl; auto.
simpl.
intros re1 re2.
case_eq (match_len (re2 / a) str); try discriminate.
induction (nu re2); try discriminate; simpl.
intros.
rewrite IHstr; auto.
rewrite orb_false_r; auto.
Qed.

Lemma match_lenOr : forall str re1 re2 n1 n2, match_len re1 str = Some n1 -> match_len re2 str = Some n2 -> match_len (Or re1 re2) str = Some(if n1 <? n2 then n2 else n1).
Proof.
induction str; simpl.
intros re1 re2.
induction (nu re1), (nu re2); try discriminate; simpl.
intros.
inversion H.
inversion H0.
auto.
intros re1 re2.
induction (nu re1), (nu re2); try discriminate; simpl.
case_eq (match_len (re1 / a) str); intros n.
case_eq (match_len (re2 / a) str); intros.
intros.
inversion H1.
inversion H2.
rewrite (IHstr (re1 / a) (re2 / a) n n0); auto.
f_equal.
case_eq (n <? n0); intros.
apply Nat.leb_le in H3.
assert (S n <? S n0 = true).
apply Nat.leb_le.
lia.
rewrite H6.
auto.
assert (S n <? S n0 = false).
apply Nat.leb_gt in H3.
apply Nat.leb_gt.
lia.
rewrite H6; auto.
rewrite match_lenOr_right_None; auto.
rewrite H0.
inversion H1.
inversion H2.
assert (S n <? 0 = false).
apply Nat.leb_gt; lia.
rewrite H3; auto.
rewrite match_lenOr_left_None; auto.
intros.
inversion H0.
induction (match_len (re2 / a) str); inversion H; inversion H2; auto.
case_eq (match_len (re1 / a) str); try discriminate; intro.
case_eq (match_len (re2 / a) str); try discriminate; intro.
intros.
inversion H1.
inversion H2.
rewrite (IHstr (re1 / a) (re2 / a) n n0); auto.
f_equal.
case_eq (n <? n0); intros.
apply Nat.leb_le in H3.
assert (S n <? S n0 = true).
apply Nat.leb_le.
lia.
rewrite H6; auto.
assert (S n <? S n0 = false).
apply Nat.leb_gt in H3.
apply Nat.leb_gt.
lia.
rewrite H6; auto.
rewrite match_lenOr_left_None; auto.
intros.
inversion H0.
induction (match_len (re2 / a) str); inversion H1; auto.
case_eq (match_len (re1 / a) str); try discriminate; intro.
case_eq (match_len (re2 / a) str); try discriminate; intro.
intros.
rewrite (IHstr (re1 / a) (re2 / a) n n0); auto.
inversion H1.
inversion H2.
case_eq (n <? n0); intros.
apply Nat.leb_le in H3.
assert (S n <? S n0 = true).
apply Nat.leb_le.
lia.
rewrite H6; auto.
assert (S n <? S n0 = false).
apply Nat.leb_gt in H3.
apply Nat.leb_gt.
lia.
rewrite H6; auto.
intros.
inversion H1.
inversion H2.
rewrite match_lenOr_right_None; simpl; auto.
rewrite H0; auto.
case_eq (match_len (re1 / a) str); try discriminate; intro.
case_eq (match_len (re2 / a) str); try discriminate; intro.
intros.
inversion H1; inversion H2.
rewrite (IHstr (re1 / a) (re2 / a) n n0); auto.
f_equal.
case_eq (n <? n0); intros.
apply Nat.leb_le in H3.
assert (S n <? S n0 = true).
apply Nat.leb_le.
lia.
rewrite H6; auto.
assert (S n <? S n0 = false).
apply Nat.leb_gt in H3.
apply Nat.leb_gt.
lia.
rewrite H6; auto.
Qed.


Lemma append_length : forall s s', String.length (s ++ s') = (String.length s) + (String.length s').
Proof.
induction s; simpl; auto.
Qed.

Require Import RegExp.Star.

Lemma star_of_Empty : forall re, re =R= Empty -> Star re =R= Eps.
Proof.
intros.
rewrite matches_Star_right.
assert (re ++ Star re =R= Empty).
rewrite H.
apply Cat_left_zero.
rewrite H0.
rewrite Or_right_id.
apply re_eq_refl.
Qed.


Lemma reEmptyString_Star : forall re, (forall str : string, re ~== str -> str = ""%string) -> (forall str, Star re ~== str -> str = ""%string).
Proof.
intros.
induction str; auto.
apply divide_Star_left in H0.
destruct H0.
destruct s.
destruct a0.
destruct H1.
destruct H2.
apply H in H3.
contradict H1; auto.
intuition.
inversion H1.
Qed.



Lemma computeMaxPossibleLenCorrectCanSucced : forall re n str, computeMaxPossibleLen re = CanSucced n -> matches re str = true -> (String.length str) <= n.
Proof.
induction re; simpl; try discriminate.
intros.
inversion H.
induction str; simpl; auto.
simpl in H0.
assert ( Empty ~!= str ) .
apply Empty_false.
rewrite H0 in H1.
discriminate.
intros.
inversion H.
induction str.
simpl in H0.
discriminate.
case_eq str; auto.
intros.
rewrite H1 in H0.
simpl in H0.
induction (ascii_dec a a0); simpl in H0.
assert ( Empty ~!= s ) .
apply Empty_false.
rewrite H0 in H3.
discriminate.
assert ( Empty ~!= s ) .
apply Empty_false.
rewrite H0 in H3.
discriminate.
case_eq (computeMaxPossibleLen re1); try discriminate.
case_eq (computeMaxPossibleLen re2); try discriminate.
intros.
apply divide_Cat in H2.
induction H2.
induction p.
destruct p.
destruct H3.
apply (IHre1 n0 x) in H0; auto.
apply (IHre2 n x0) in H; auto.
rewrite H2.
rewrite append_length.
inversion H1.
lia.
induction (computeMaxPossibleLen re2); discriminate.
case_eq (computeMaxPossibleLen re1); intros; try discriminate.
rewrite matches_Or in H1.
apply computeMaxPossibleLenCorrectNeverSucced in H.
assert (re1 ~= str = false).
rewrite H.
apply Empty_false.
rewrite H2 in H1.
simpl in H1.
apply (IHre2 n str) in H0; auto.
case_eq (computeMaxPossibleLen re2); intros; rewrite H2 in H0; intros; try discriminate.
rewrite matches_Or in H1.
apply computeMaxPossibleLenCorrectNeverSucced in H2.
assert (re2 ~= str = false).
rewrite H2.
apply Empty_false.
rewrite H3 in H1.
rewrite orb_false_r in H1.
inversion H0.
apply (IHre1 n str) in H; auto.
lia.
inversion H0.
rewrite matches_Or in H1.
apply orb_true_iff in H1.
destruct H1.
apply (IHre1 n str) in H; auto.
assert ((if n <? n1 then n1 else n)>=n).
case_eq (n <? n1); intros.
apply Nat.ltb_lt in H3; lia.
apply Nat.ltb_ge in H3; lia.
lia.
apply (IHre2 n1 str) in H2; auto.
assert ((if n <? n1 then n1 else n)>=n1).
case_eq (n <? n1); intros.
apply Nat.ltb_lt in H3; lia.
apply Nat.ltb_ge in H3; lia.
lia.
induction (computeMaxPossibleLen re2); discriminate.
case_eq (computeMaxPossibleLen re); try discriminate.
intros.
inversion H0.
apply computeMaxPossibleLenCorrectNeverSucced in H.
apply star_of_Empty in H; auto.
rewrite H in H1.
induction str; auto.
simpl in H1.
assert (Empty ~!= str).
apply Empty_false.
rewrite H1 in H2; discriminate.
induction n; try discriminate.
intros.
assert (forall str, re ~== str -> str = EmptyString).
intros.
apply (IHre 0 str0) in H2; auto.
induction str0; auto; simpl in H2; try lia.
apply reEmptyString_Star in H1; auto.
rewrite H1; simpl; lia.
case_eq (computeMaxPossibleLen re1); try discriminate.
case_eq (computeMaxPossibleLen re2); try discriminate.
intros.
rewrite matches_And in H2.
apply andb_true_iff in H2.
destruct H2.
induction (n0 <? n); inversion H1; try rewrite H5 in *.
apply (IHre1 n1 str) in H0; auto.
apply (IHre2 n1 str) in H; auto.
intros.
rewrite matches_And in H2.
apply andb_true_iff in H2.
destruct H2.
inversion H1.
rewrite <- H5.
apply (IHre1 n str) in H0; auto.
intros.
case_eq (computeMaxPossibleLen re2); intros; rewrite H2 in H0; try discriminate.
rewrite matches_And in H1.
apply andb_true_iff in H1.
destruct H1.
inversion H0.
rewrite <- H5.
apply (IHre2 n0 str) in H2; auto.
Qed.

Lemma NeverSucced_MatchLen : forall re str, computeMaxPossibleLen re = NeverSucced -> match_len re str = None.
Proof.
intros.
apply computeMaxPossibleLenCorrectNeverSucced in H.
assert (forall m, matches re (substring 0 m str) = false).
intros.
rewrite H.
apply Empty_false.
apply correct_match_len_none_substrFalse; auto.
Qed.

Lemma MatchLen_Max : forall  n str re, match_len re str = Some n -> match_len re (substring 0 n str) = Some n.
Proof.
induction n.
induction str; auto.
intros.
apply correct_match_len_some0_nu in H.
simpl.
rewrite H; auto.
induction str; auto.
simpl.
intro.
case_eq (match_len (re / a) str); intros.
case_eq (match_len (re / a) (substring 0 n str)); intros.
inversion H0.
rewrite H3 in H.
apply IHn in H; auto.
rewrite H in H1.
inversion H1; auto.
inversion H0.
rewrite H3 in H.
apply IHn in H; auto.
rewrite H in H1.
inversion H1.
induction (nu re); try discriminate H0.
Qed.

Lemma MatchLen_None_Impl : forall str m re, match_len re str = None -> match_len re (substring 0 m str) = None.
Proof.
induction str.
simpl.
intros.
induction m; simpl; auto.
induction m; simpl; auto.
intros.
induction (match_len (re / a) str), (nu re); try discriminate H; auto.
intros.
case_eq (match_len (re / a) str); intros; rewrite H0 in H; try discriminate.
apply (IHstr m ) in H0.
rewrite H0; auto.
Qed.

Lemma MatchLen_Max2 : forall m n str re, match_len re str = Some n -> m >= n -> match_len re (substring 0 m str) = Some n.
Proof.
induction m.
intros.
assert (n=0) by lia.
rewrite H1 in H.
rewrite H1.
apply correct_match_len_some0_nu in H.
induction str; simpl; auto.
rewrite H; auto.
rewrite H; auto.
intros.
inversion H0.
rewrite H1 in H.
apply MatchLen_Max; auto.
induction str.
simpl in H.
simpl.
induction (nu re); auto; try discriminate.
simpl in H.
simpl.
case_eq (match_len (re / a) str); intros; rewrite H3 in H.
inversion H.
apply IHm in H3; try lia.
rewrite H3; auto.
apply (MatchLen_None_Impl str m (re / a)) in H3.
rewrite H3; auto.
Qed.

Lemma CanSucced_MatchLen : forall re str n, computeMaxPossibleLen re = CanSucced n -> match_len re str = match_len re (substring 0 n str).
Proof.
intros.
case_eq (match_len re str).
intros.
assert (H0':=H0).
assert (H0'':=H0).
apply correct_match_len_some_substr in H0.
apply (computeMaxPossibleLenCorrectCanSucced re n (substring 0 n0 str) ) in H; auto.
apply matchlen_inf in H0'.
rewrite length_substr0 in H; auto.
apply eq_sym.
eapply (MatchLen_Max2); eauto.
intros.
apply eq_sym.
apply MatchLen_None_Impl; auto.
Qed.

Definition match_len_speed_up re str := 
match computeMaxPossibleLen re with
| NeverSucced => None
| CanSucced n => match_len re (substring 0 n str)
| InfSucced => match_len re str
end.


Lemma match_len_speed_up_correct : forall re str, match_len re str = match_len_speed_up re str.
Proof.
unfold match_len_speed_up.
intro.
case_eq (computeMaxPossibleLen re); intros.
apply NeverSucced_MatchLen; auto.
apply CanSucced_MatchLen; auto.
auto.
Qed.

Fixpoint match_len_speed_up_v2_0 re s := match s with
| EmptyString => if nu re then Some 0 else None
| String a s2 => (match computeMaxPossibleLen (re/a) with
                  | NeverSucced => if nu re then Some 0 else None
                  | _ => (match match_len_speed_up_v2_0 (re/a) s2 with
                          | Some l => Some (S l)
                          | None => if nu re then Some 0 else None
                          end)
                  end)
end.


Lemma match_len_speed_up_v2_0_correct : forall str re, match_len re str = match_len_speed_up_v2_0 re str.
Proof.
induction str.
auto.
simpl.
intros.
case_eq (computeMaxPossibleLen (re / a)); intros.
apply (NeverSucced_MatchLen (re/a) str) in H; auto.
rewrite H; auto.
rewrite IHstr; auto.
rewrite IHstr; auto.
Qed.

Definition match_len_speed_up_v2 re str := 
match computeMaxPossibleLen re with
| NeverSucced => None
| CanSucced n => match_len_speed_up_v2_0 re (substring 0 n str)
| InfSucced => match_len_speed_up_v2_0 re str
end.

Lemma match_len_speed_up_v2_correct : forall re str, match_len re str = match_len_speed_up_v2 re str.
Proof.
unfold match_len_speed_up_v2.
intro.
case_eq (computeMaxPossibleLen re); intros.
apply NeverSucced_MatchLen; auto.
rewrite <- match_len_speed_up_v2_0_correct.
apply CanSucced_MatchLen; auto.
rewrite <- match_len_speed_up_v2_0_correct.
auto.
Qed.

















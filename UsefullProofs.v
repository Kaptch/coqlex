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
Require Import micromega.Lia.

Definition regexp_eq : forall (r1 r2:RegExp), {r1=r2} + {r1<>r2}.
    intros.
    decide equality. apply ascii_dec.
  Defined.

Lemma substr_1_step : forall n a str, String a (substring 0 n str) = (substring 0 (S n) (String a str)).
Proof.
induction str; simpl; auto.
Qed.

Lemma ge_S_S : forall n n0, S n0 >= S n <-> n0 >= n.
Proof.
intros.
lia.
Qed.


Lemma substr_0_len_str : forall str, (substring 0 (length str) str) = str.
Proof.
induction str; simpl; auto.
f_equal; auto.
Qed.

Lemma len_substr_n_m_lt_len : forall str n m, length (substring n m str) <= length str.
Proof.
induction str.
simpl.
intros.
induction n, m; auto.
intros.
induction n.
simpl.
induction m; simpl; auto.
lia.
apply le_n_S.
auto.
simpl.
assert (length (substring n m str) <= length str); auto.
Qed.

Lemma substr_nSupStrLen : forall s n m, n >= String.length s -> substring n m s = ""%string.
Proof.
induction s; simpl; auto.
induction n; simpl; auto.
induction m; simpl; auto.
intros.
induction n; simpl; try lia; auto.
assert (n >= length s) by lia.
apply IHs; auto.
Qed.

Definition ignore_nfirst_char n str := substring n ((length str)- n) str.

Lemma ignore_concat : forall str n, (append (substring 0 n str) (ignore_nfirst_char n str)) = str.
Proof.
unfold ignore_nfirst_char.
induction str, n; simpl; auto.
f_equal.
apply substr_0_len_str.
f_equal.
apply IHstr.
Qed.

Lemma ignore_dec_length : forall n str, String.length (ignore_nfirst_char n str) <= String.length str.
Proof.
unfold ignore_nfirst_char.
induction n; induction str; simpl; auto.
replace (length str - 0) with (length str) in IHstr by lia.
lia.
Qed.

Lemma ignore_decroiss_length : forall n a str, n > 0 -> String.length (ignore_nfirst_char n (String a str)) < String.length (String a str).
Proof.
unfold ignore_nfirst_char.
induction n.
intros.
lia.
intros.
simpl.
assert (length (ignore_nfirst_char n str) <= length str).
apply ignore_dec_length.
unfold ignore_nfirst_char in H0.
lia.
Qed.

Lemma length_substr0 : forall n str, n <= length str -> length (substring 0 n str) = n.
Proof.
unfold ignore_nfirst_char.
induction n, str; simpl; auto.
lia.
intros.
f_equal.
apply IHn.
lia.
Qed.

Lemma concat_empty : forall str, append str ""%string = str.
Proof.
induction str; simpl; f_equal; auto.
Qed.

Lemma concat_length : forall s s', String.length (s ++ s') = (String.length s) + (String.length s').
Proof.
induction s; simpl; auto.
Qed.

Require Import Coq.Lists.List.
Import ListNotations.

Lemma filter_empty {A : Type} : forall l f , filter f l = nil <-> (forall e, List.In (A := A) e l -> f e = false).
Proof.
induction l.
simpl.
split.
intros.
inversion H0.
auto.
intros.
split.
intros.
inversion H0.
unfold filter in H.
rewrite H1 in H.
induction (f e).
discriminate H.
auto.
unfold filter in H.
induction (f a); try discriminate.
apply IHl; auto.
intros.
simpl.
assert (f a = false).
apply H.
constructor; auto.
rewrite H0.
apply IHl.
intros.
destruct (H e); auto.
apply in_cons; auto.
Qed.

Lemma filter_cons {A : Type} : forall l f a, filter f (a::l) = [] -> filter (A:=A) f l = [].
Proof.
intros.
unfold filter in *.
induction (f a).
inversion H.
auto.
Qed.

(* Variable A : Type.

Hypothesis dec_A : forall x y : A, {x = y} + {x <> y}.
 *)
Lemma notin_remove {A : Type} : forall (dec_A : forall x y : A, {x = y} + {x <> y}) l x, ~ In x l -> remove dec_A x l = l.
Proof.
induction l; auto.
simpl.
intros.
intuition.
induction (dec_A x a).
apply eq_sym in a0.
intuition.
f_equal.
auto.
Qed.

Lemma notin_remove2 {A : Type} : forall (dec_A : forall x y : A, {x = y} + {x <> y}) l x y, ~ In x l -> ~In x (remove dec_A y l).
Proof.
induction l; auto.
simpl.
intuition.
induction (dec_A y a).
eapply IHl; eauto.
simpl in H0.
destruct H0.
auto.
eapply IHl; eauto.
Qed.

Lemma not_in_s_implies {A : Type} : forall (dec_A : forall x y : A, {x = y} + {x <> y}) l s a, ~In a s -> ~In a (fold_left (fun l x => remove dec_A x l) l s).
Proof.
induction l; auto.
simpl.
intros.
apply IHl.
apply notin_remove2; auto.
Qed.

Lemma rm_fold_left_correct {A : Type} : forall (dec_A : forall x y : A, {x = y} + {x <> y}) l s a, In a l -> ~In a (fold_left (fun l x => remove dec_A x l) l s).
Proof.
induction l.
intros.
auto.
simpl.
intros.
destruct H.
rewrite H.
apply not_in_s_implies.
apply remove_In.
apply IHl.
auto.
Qed.

Lemma notin_remove3 {A : Type} : forall (dec_A : forall x y : A, {x = y} + {x <> y}) l x y, x<>y -> (In x l <-> In x (remove dec_A y l)).
Proof.
induction l.
simpl.
intuition.
simpl.
intros.
induction (dec_A y a).
split.
intros.
destruct H0.
rewrite H0 in a0.
apply eq_sym in a0.
intuition.
eapply IHl in H0; eauto.
intros.
eapply IHl in H0; eauto.
split.
intros.
simpl.
destruct H0.
auto.
right.
eapply IHl in H0; eauto.
simpl.
intros.
destruct H0.
auto.
eapply IHl in H0; eauto.
Qed.

Lemma rm_fold_left_correct2 {A : Type} : forall (dec_A : forall x y : A, {x = y} + {x <> y}) l s a, ~In a l -> In a s -> In a (fold_left (fun l x => remove dec_A x l) l s).
Proof.
induction l.
simpl.
intros.
intuition.
simpl.
intros.
apply IHl.
intuition.
eapply notin_remove3 in H0; eauto.
Qed.





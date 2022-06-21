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

(* 
  MatchLen (or score) implements the rule of the longest possible lexeme
  Verification : 
    Important props : 
                  * forall str regex total_s, match_len regex str = Some total_s -> matches regex (substring 0 total_s str) = true.
                  * forall str regex, match_len regex str = None -> (forall m, matches regex (substring 0 m str) = false)
                  * forall str regex, matches regex str = true <-> match_len regex str = Some (length str).
                  * forall str regex total_s result, total_s <= length str -> matches regex (substring 0 total_s str) = true -> match_len regex str = Some result -> result >= total_s.
    with matches, a verified function returning true if a regex matches a string.
 *)
Require Import RegExp.Definitions.
Require Import RegExp.Boolean.
Require Import RegExp.Char.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Compare.
Require Import Coq.Arith.PeanoNat.
Require Import micromega.Lia.
Require Import UsefullProofs.


Fixpoint match_len re s := match s with
| EmptyString => if nu re then Some 0 else None
| String a s2 => (match match_len (re/a) s2 with
                  | Some l => Some (S l)
                  | None => if nu re then Some 0 else None
                  end)
end.

Lemma correct_match_len_some_substr : forall str regex total_s, match_len regex str = Some total_s -> matches regex (substring 0 total_s str) = true.
Proof.
induction str.
simpl.
intros.
assert (nu regex = true).
induction (nu regex); auto; try discriminate H.
induction total_s; simpl; auto.
simpl.
intros.
case_eq (match_len (regex / a) str).
intros.
assert (Hb := H).
rewrite -> H0 in Hb.
inversion Hb.
simpl.
apply IHstr; auto.
intros.
assert (Hb := H).
rewrite -> H0 in Hb.
assert (nu regex = true).
induction (nu regex); simpl; auto; discriminate Hb.
rewrite -> H1 in Hb.
inversion Hb.
simpl; auto.
Qed.


Lemma correct_match_len_none_false : forall str regex, match_len regex str = None -> matches regex str = false.
Proof.
induction str; auto.
simpl.
intros.
induction (nu regex); auto; discriminate H.
intros.
simpl in H.
simpl.
apply IHstr.
induction (match_len (regex / a) str); auto;  try discriminate H.
Qed.

Lemma correct_match_len_some0_nu : forall str regex, match_len regex str = Some 0 -> nu regex = true.
Proof.
induction str; simpl; auto; intros.
induction (nu regex); auto; discriminate H.
induction (match_len (regex / a) str); auto.
discriminate H.
induction (nu regex); auto; discriminate H.
Qed.


Lemma correct_match_len_Sstring_some0_match : forall str a regex, match_len regex (String a str) = Some 0 -> matches regex (String a str) = false.
Proof.
induction str.
simpl.
intros.
induction (nu (regex / a)); auto; discriminate H.
intros.
assert (Hdup := H).
apply correct_match_len_some0_nu in Hdup.
simpl in H.
rewrite -> Hdup in H.
assert (match_len (regex / a0 / a) str = None).
induction (match_len (regex / a0 / a) str); auto.
discriminate H.
apply correct_match_len_none_false in H0.
auto.
Qed.

Lemma correct_match_len_matchStr_lenStr : forall str regex, matches regex str = true <-> match_len regex str = Some (length str).
Proof.
induction str.
split.
simpl.
intros.
rewrite -> H; auto.
simpl.
intros.
induction (nu regex); auto; discriminate H.
split.
simpl.
case_eq (match_len (regex / a) str).
intros.
apply IHstr in H0.
rewrite -> H in H0.
inversion H0.
f_equal.
intros.
apply correct_match_len_none_false in H.
unfold matches in *.
rewrite -> H in H0.
discriminate.
simpl.
case_eq (match_len (regex / a) str).
intros.
inversion H0.
rewrite H2 in H.
apply IHstr; auto.
intros.
induction (nu regex); discriminate H0.
Qed.

Lemma correct_match_len_none_substrFalse : forall str regex, match_len regex str = None <-> (forall m, matches regex (substring 0 m str) = false).
Proof.
induction str.
simpl.
split.
intros.
assert (nu regex = false).
induction (nu regex); simpl; auto; discriminate.
induction m; auto.
intros.
assert (nu regex = false).
apply (H 0).
rewrite H0; auto.
split.
simpl.
intros.
assert (match_len (regex / a) str = None).
induction (match_len (regex / a) str); auto; discriminate H.
assert (nu regex = false).
rewrite H0 in H.
induction (nu regex); simpl; auto; discriminate.
induction m; auto.
simpl.
apply IHstr; auto.
intros.
assert (nu regex = false).
apply (H 0).
case_eq (match_len (regex / a) str).
intros.
apply correct_match_len_some_substr in H1.
assert (regex / a ~!= substring 0 n str).
apply (H (S n)).
unfold matches in H2, H1.
rewrite H2 in H1.
discriminate.
intros.
simpl.
rewrite H1.
rewrite H0; auto.
Qed.

Lemma correct_match_len_some_substrTrue : forall str regex m, matches regex (substring 0 m str) = true -> (exists e, match_len regex str = Some e).
Proof.
induction str.
simpl.
intros.
induction m.
simpl in H.
rewrite H.
exists 0; auto.
simpl in H.
rewrite H.
exists 0; auto.
simpl.
intros.
induction m.
induction (match_len (regex / a) str).
exists (S a0); auto.
simpl in H.
rewrite H.
exists 0; auto.
simpl in H.
apply IHstr in H.
destruct H.
rewrite H.
exists (S x); auto.
Qed.


Lemma correct_match_matchesSubstr_inf_matchlenResult : forall str regex total_s result, total_s <= length str -> matches regex (substring 0 total_s str) = true -> match_len regex str = Some result -> result >= total_s.
Proof.
induction str.
simpl.
intros.
lia.
intros.
case_eq total_s.
intros.
lia.
intros.
simpl in H.
rewrite -> H2 in *.
apply le_S_n in H.
simpl in H0.
simpl in H1.
case_eq (match_len (regex / a) str).
intros.
rewrite -> H3 in H1.
inversion H1.
apply ge_S_S.
apply (IHstr (regex / a)); auto.
intros.
assert (regex / a ~!= substring 0 n str).
apply correct_match_len_none_substrFalse; auto.
unfold matches in H0, H4.
rewrite -> H0 in H4.
discriminate.
Qed.

Lemma matchlen_inf : forall str regex e, match_len regex str = Some e -> e <= String.length str.
Proof.
induction str.
simpl.
intros.
induction (nu regex); inversion H; auto.
simpl.
intros regex e.
case_eq (match_len (regex / a) str).
intros.
apply IHstr in H.
inversion H0.
lia.
intros.
induction (nu regex); inversion H0; auto.
lia.
Qed.

Lemma matchesFalse_impl_matchlen : forall str l regex, matches regex str = false -> match_len regex str = Some l -> l < String.length str.
Proof.
induction str.
simpl.
intros.
rewrite H in H0.
discriminate H0.
simpl.
intros l regex.
case_eq (match_len (regex / a) str); intros.
apply IHstr in H; auto.
inversion H1.
lia.
induction (nu regex).
inversion H1.
lia.
inversion H1.
Qed.

Lemma matchlen_concat : forall str s l regex, match_len regex str = Some l -> (exists l', match_len regex (str ++ s) = Some l').
Proof.
induction str.
induction s.
simpl.
intros.
exists l; auto.
simpl.
intros.
induction (match_len (regex / a) s).
exists (S a0); auto.
exists l; auto.
simpl.
intros s l regex.
case_eq (match_len (regex / a) str); intros.
apply (IHstr s) in H.
destruct H.
rewrite H.
exists (S x); auto.
induction (match_len (regex / a) (str ++ s)).
exists (S a0); auto.
induction (nu regex); auto; try discriminate H0.
exists 0; auto.
Qed.

Lemma matchlen_concat2 : forall str s regex, match_len regex (str ++ s) = None -> match_len regex str = None.
Proof.
induction str.
induction s.
auto.
simpl in IHs.
simpl.
intros.
assert (match_len (regex / a) s = None).
induction (match_len (regex / a) s); try discriminate H; auto.
rewrite H0 in H.
auto.
simpl.
intros.
assert (match_len (regex / a) (str ++ s) = None).
induction (match_len (regex / a) (str ++ s)); try discriminate H; auto.
assert ( H1 := H0 ).
apply IHstr in H0.
rewrite H0.
rewrite H1 in H.
auto.
Qed.

Lemma matchlen_concat_croiss : forall str s l l' regex, match_len regex str = Some l -> match_len regex (str ++ s) = Some l' -> l <= l'.
Proof.
induction str.
simpl.
intros.
assert (nu regex = true).
induction (nu regex); auto; try discriminate H.
rewrite H1 in H.
inversion H.
lia.
simpl.
intros s l l' regex.
case_eq (match_len (regex / a) str); intro.
case_eq (match_len (regex / a) (str ++ s)); intros.
apply (IHstr s (n) (n0) (regex/a)) in H; auto.
inversion H1. 
inversion H2.
lia.
apply (matchlen_concat str s n) in H0.
destruct H0.
rewrite H0 in H.
inversion H.
intros.
assert (nu regex = true).
induction (nu regex); auto; try discriminate H0.
rewrite H2 in H0.
inversion H0.
lia.
Qed.

Lemma matchLen_Some0 : forall s c regex, match_len regex (String c s) = Some 0 -> match_len (regex/c) s = None.
Proof.
simpl.
intros.
induction (match_len (regex / c) s); auto; try discriminate H.
Qed.

Lemma matchLen_Some0_inv : forall s c regex,  match_len (regex/c) s = None -> nu regex = true -> match_len regex (String c s) = Some 0.
Proof.
simpl.
intros.
rewrite H.
rewrite H0.
auto.
Qed.


Lemma matchesFalse_impl_or : forall s regex l, matches regex s = false -> (match_len regex s = None \/ (match_len regex s = Some l -> l < String.length s)).
Proof.
intros.
case_eq (match_len regex s); auto.
intros.
right.
intros.
apply (matchesFalse_impl_matchlen s l regex); auto.
inversion H1.
rewrite <- H3; auto.
Qed.

Lemma matchlen_infStrLen_impl_matchesFalse : forall str l regex, match_len regex str = Some l -> l < String.length str -> matches regex str = false.
Proof.
intros.
case_eq (matches regex str); auto.
intros.
apply correct_match_len_matchStr_lenStr in H1.
rewrite H1 in H.
inversion H.
rewrite H3 in H0.
lia.
Qed.


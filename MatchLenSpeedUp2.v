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
Require Import MatchLen.


Fixpoint simplify (re:RegExp):RegExp :=
match re with
| Empty => Empty
| Eps => Eps
| Char c => Char c
| Cat r s => (match (simplify r), (simplify s) with
    | Empty, _ => Empty
    | _, Empty => Empty
    | Eps, s' => s'
    | r', Eps => r'
    | r', s' => Cat r' s'
  end)
| Or r s => (match (simplify r), (simplify s) with
    | Empty, s' => s'
    | r', Empty => r'
    | s', r' => Or s' r'
  end)
| Star r => (match (simplify r) with
    | Empty => Eps
    | Eps => Eps
    | r' => Star r'
  end)
| Not r => Not (simplify r)
| And r s => (match (simplify r), (simplify s) with
    | Empty, s' => Empty
    | r', Empty => Empty
    | s', r' => And s' r'
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

Lemma simpl_correct_empty : forall re, simplify re = Empty -> re =R= Empty.
Proof.
induction re; simpl; try discriminate.
intros.
apply re_eq_refl.
case_eq (simplify re2); case_eq (simplify re1); try discriminate; intros.
apply IHre1 in H.
rewrite H.
rewrite Cat_left_zero; auto.
apply re_eq_refl.
apply IHre2 in H0.
rewrite H0.
rewrite Cat_right_zero; auto.
apply re_eq_refl.
apply IHre2 in H0.
rewrite H0.
rewrite Cat_right_zero; auto.
apply re_eq_refl.
apply IHre2 in H0.
rewrite H0.
rewrite Cat_right_zero; auto.
apply re_eq_refl.
apply IHre2 in H0.
rewrite H0.
rewrite Cat_right_zero; auto.
apply re_eq_refl.
apply IHre2 in H0.
rewrite H0.
rewrite Cat_right_zero; auto.
apply re_eq_refl.
apply IHre2 in H0.
rewrite H0.
rewrite Cat_right_zero; auto.
apply re_eq_refl.
apply IHre2 in H0.
rewrite H0.
rewrite Cat_right_zero; auto.
apply re_eq_refl.
apply IHre1 in H.
rewrite H.
rewrite Cat_left_zero; auto.
apply re_eq_refl.
apply IHre1 in H.
rewrite H.
rewrite Cat_left_zero; auto.
apply re_eq_refl.
apply IHre1 in H.
rewrite H.
rewrite Cat_left_zero; auto.
apply re_eq_refl.
apply IHre1 in H.
rewrite H.
rewrite Cat_left_zero; auto.
apply re_eq_refl.
apply IHre1 in H.
rewrite H.
rewrite Cat_left_zero; auto.
apply re_eq_refl.
apply IHre1 in H.
rewrite H.
rewrite Cat_left_zero; auto.
apply re_eq_refl.
apply IHre1 in H.
rewrite H.
rewrite Cat_left_zero; auto.
apply re_eq_refl.
case_eq (simplify re2); case_eq (simplify re1); try discriminate; intros.
apply IHre1 in H.
rewrite H.
rewrite Or_left_id ; auto.
case_eq (simplify re); try discriminate.
case_eq (simplify re2); case_eq (simplify re1); try discriminate; intros.
apply IHre2 in H0.
apply IHre1 in H.
rewrite H.
apply And_left_empty_s.
apply IHre2 in H0.
rewrite H0.
apply And_right_empty_s.
apply IHre2 in H0.
rewrite H0.
apply And_right_empty_s.
apply IHre2 in H0.
rewrite H0.
apply And_right_empty_s.
apply IHre2 in H0.
rewrite H0.
apply And_right_empty_s.
apply IHre2 in H0.
rewrite H0.
apply And_right_empty_s.
apply IHre2 in H0.
rewrite H0.
apply And_right_empty_s.
apply IHre2 in H0.
rewrite H0.
apply And_right_empty_s.
apply IHre1 in H.
rewrite H.
apply And_left_empty_s.
apply IHre1 in H.
rewrite H.
apply And_left_empty_s.
apply IHre1 in H.
rewrite H.
apply And_left_empty_s.
apply IHre1 in H.
rewrite H.
apply And_left_empty_s.
apply IHre1 in H.
rewrite H.
apply And_left_empty_s.
apply IHre1 in H.
rewrite H.
apply And_left_empty_s.
apply IHre1 in H.
rewrite H.
apply And_left_empty_s.
Qed.

Require Import RegExp.Star.

Lemma simpl_correct_eps : forall re, simplify re = Eps -> re =R= Eps.
Proof.
induction re; simpl; try discriminate.
intros.
apply re_eq_refl.
case_eq (simplify re2); case_eq (simplify re1); try discriminate; intros.
apply IHre1 in H.
rewrite H.
rewrite Cat_left_id; auto.
case_eq (simplify re2); case_eq (simplify re1); try discriminate; intros.
apply IHre1 in H.
rewrite H.
apply simpl_correct_empty in H0.
rewrite H0.
apply Or_right_id.
apply simpl_correct_empty in H.
rewrite H.
rewrite Or_left_id ; auto.
case_eq (simplify re); try discriminate.
intros.
apply simpl_correct_empty in H.
assert (H' := matches_Star_right re).
rewrite H'.
rewrite H.
rewrite Cat_left_zero.
rewrite Or_right_id.
apply re_eq_refl.
intros.
assert (H' := matches_Star_right re).
apply IHre in H.
rewrite H'.
rewrite H in *.
rewrite Cat_left_id.
unfold re_eq.
induction s; simpl; auto.
rewrite Or_left_id.
rewrite Cat_left_zero; auto.
case_eq (simplify re2); case_eq (simplify re1); try discriminate; intros.
Qed.

Lemma star_of_Eps : Star Eps =R= Eps.
Proof.
unfold re_eq.
induction s; simpl; auto.
rewrite Cat_left_zero; auto.
Qed.


Lemma simpl_correct: forall re, re =R= (simplify re).
Proof.
induction re.
simpl; apply re_eq_refl.
simpl; apply re_eq_refl.
simpl; apply re_eq_refl.
simpl.
case_eq (simplify re2); try discriminate; intros.
apply simpl_correct_empty in H.
rewrite H.
rewrite Cat_right_zero; auto.
induction (simplify re1); apply re_eq_refl.
apply simpl_correct_eps in H.
rewrite H.
rewrite Cat_right_id; auto.
replace (match simplify re1 with
| Empty => Empty
| Eps => Eps
| Char a => Char a
| r0 ++ r1 => r0 ++ r1
| Or r0 r1 => Or r0 r1
| Star r0 => Star r0
| Not r0 => Not r0
| And r0 r1 => And r0 r1
end) with (simplify re1); auto.
induction (simplify re1); auto.
rewrite <- H.
case_eq (simplify re1); intros.
apply simpl_correct_empty in H0.
rewrite H0.
rewrite Cat_left_zero; auto.
simpl; apply re_eq_refl.
apply simpl_correct_eps in H0.
rewrite H0.
rewrite Cat_left_id; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H.
case_eq (simplify re1); intros.
apply simpl_correct_empty in H0.
rewrite H0.
rewrite Cat_left_zero; auto.
simpl; apply re_eq_refl.
apply simpl_correct_eps in H0.
rewrite H0.
rewrite Cat_left_id; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.

rewrite <- H.
case_eq (simplify re1); intros.
apply simpl_correct_empty in H0.
rewrite H0.
rewrite Cat_left_zero; auto.
simpl; apply re_eq_refl.
apply simpl_correct_eps in H0.
rewrite H0.
rewrite Cat_left_id; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.

rewrite <- H.
case_eq (simplify re1); intros.
apply simpl_correct_empty in H0.
rewrite H0.
rewrite Cat_left_zero; auto.
simpl; apply re_eq_refl.
apply simpl_correct_eps in H0.
rewrite H0.
rewrite Cat_left_id; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.

rewrite <- H.
case_eq (simplify re1); intros.
apply simpl_correct_empty in H0.
rewrite H0.
rewrite Cat_left_zero; auto.
simpl; apply re_eq_refl.
apply simpl_correct_eps in H0.
rewrite H0.
rewrite Cat_left_id; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.

rewrite <- H.
case_eq (simplify re1); intros.
apply simpl_correct_empty in H0.
rewrite H0.
rewrite Cat_left_zero; auto.
simpl; apply re_eq_refl.
apply simpl_correct_eps in H0.
rewrite H0.
rewrite Cat_left_id; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.
rewrite <- H0.
unfold re_eq.
intros.
apply Cat_morphism_s; auto.

simpl.
case_eq (simplify re1); intros; try rewrite <- H.
apply simpl_correct_empty in H.
rewrite H.
rewrite Or_left_id; auto.
case_eq (simplify re2); intros; try rewrite <- H0.
apply simpl_correct_empty in H0.
rewrite H0.
rewrite <- IHre1.
apply Or_right_id ; auto.
rewrite H.
apply simpl_correct_eps in H.
apply simpl_correct_eps in H0.
rewrite H.
rewrite H0.
apply re_eq_refl.
rewrite <- IHre1.
apply simpl_correct_eps in H.
rewrite H.
rewrite <- IHre2.
apply re_eq_refl.

rewrite H.
apply simpl_correct_eps in H.
rewrite H.
rewrite <- IHre2.
apply re_eq_refl.
rewrite <- IHre2.
rewrite <- IHre1.
apply re_eq_refl.

rewrite <- IHre2; rewrite <- IHre1; apply re_eq_refl.
rewrite <- IHre2; rewrite <- IHre1; apply re_eq_refl.
rewrite <- IHre2; rewrite <- IHre1; apply re_eq_refl.

case_eq (simplify re2); intros; try rewrite <- H0; try rewrite <- IHre2; try rewrite <- IHre1; try apply re_eq_refl.
apply simpl_correct_empty in H0.
rewrite H0.
apply Or_right_id.

case_eq (simplify re2); intros; try rewrite <- H0; try rewrite <- IHre2; try rewrite <- IHre1; try apply re_eq_refl; apply simpl_correct_empty in H0; rewrite H0; apply Or_right_id.
case_eq (simplify re2); intros; try rewrite <- H0; try rewrite <- IHre2; try rewrite <- IHre1; try apply re_eq_refl; apply simpl_correct_empty in H0; rewrite H0; apply Or_right_id.
case_eq (simplify re2); intros; try rewrite <- H0; try rewrite <- IHre2; try rewrite <- IHre1; try apply re_eq_refl; apply simpl_correct_empty in H0; rewrite H0; apply Or_right_id.
case_eq (simplify re2); intros; try rewrite <- H0; try rewrite <- IHre2; try rewrite <- IHre1; try apply re_eq_refl; apply simpl_correct_empty in H0; rewrite H0; apply Or_right_id.
case_eq (simplify re2); intros; try rewrite <- H0; try rewrite <- IHre2; try rewrite <- IHre1; try apply re_eq_refl; apply simpl_correct_empty in H0; rewrite H0; apply Or_right_id.
simpl.
case_eq (simplify re); intros.
apply simpl_correct_empty in H.
rewrite H.

(* Star Empty =R= Eps *)
assert (H':=matches_Star_left Empty).
rewrite H'.
rewrite Cat_right_zero.
rewrite Or_right_id.
apply re_eq_refl.
apply simpl_correct_eps in H.
rewrite H.
apply star_of_Eps.

rewrite <- H; rewrite <- IHre; apply re_eq_refl.
rewrite <- H; rewrite <- IHre; apply re_eq_refl.
rewrite <- H; rewrite <- IHre; apply re_eq_refl.
rewrite <- H; rewrite <- IHre; apply re_eq_refl.
rewrite <- H; rewrite <- IHre; apply re_eq_refl.
rewrite <- H; rewrite <- IHre; apply re_eq_refl.
simpl.
rewrite <- IHre; apply re_eq_refl.

simpl; case_eq (simplify re1); intros; try rewrite <- H.
rewrite H.
apply simpl_correct_empty in H.
rewrite H.

apply And_left_empty_s.
case_eq (simplify re2); intros; try rewrite <- H0; try rewrite <- IHre2; try rewrite <- IHre1; try apply re_eq_refl.
apply simpl_correct_empty in H0.
rewrite H0.
apply And_right_empty_s.
apply simpl_correct_eps in H.
apply simpl_correct_eps in H0.
rewrite H0.
rewrite H.
apply re_eq_refl.

case_eq (simplify re2); intros; try rewrite <- H0; try rewrite <- IHre2; try rewrite <- IHre1; try apply re_eq_refl.
apply simpl_correct_empty in H0.
rewrite H0.
apply And_right_empty_s.
case_eq (simplify re2); intros; try rewrite <- H0; try rewrite <- IHre2; try rewrite <- IHre1; try apply re_eq_refl.
apply simpl_correct_empty in H0.
rewrite H0.
apply And_right_empty_s.
case_eq (simplify re2); intros; try rewrite <- H0; try rewrite <- IHre2; try rewrite <- IHre1; try apply re_eq_refl; apply simpl_correct_empty in H0; rewrite H0; apply And_right_empty_s.
case_eq (simplify re2); intros; try rewrite <- H0; try rewrite <- IHre2; try rewrite <- IHre1; try apply re_eq_refl; apply simpl_correct_empty in H0; rewrite H0; apply And_right_empty_s.
case_eq (simplify re2); intros; try rewrite <- H0; try rewrite <- IHre2; try rewrite <- IHre1; try apply re_eq_refl; apply simpl_correct_empty in H0; rewrite H0; apply And_right_empty_s.
case_eq (simplify re2); intros; try rewrite <- H0; try rewrite <- IHre2; try rewrite <- IHre1; try apply re_eq_refl; apply simpl_correct_empty in H0; rewrite H0; apply And_right_empty_s.
Qed.

Fixpoint match_len_opt re s := 
match simplify re with
| Empty => None
| Eps => Some 0
| re' => (
  match s with
  | EmptyString => if nu re' then Some 0 else None
  | String a s2 => (match match_len_opt (simplify (re'/a)) s2 with
                    | Some l => Some (S l)
                    | None => if nu re' then Some 0 else None
                    end)
  end
)
end.

Lemma match_len_re_eq : forall s re re', re =R= re' -> match_len re s = match_len re' s.
Proof.
induction s; simpl; intros.
rewrite H; auto.
assert (H' := derive_equals re re' H a).
apply IHs in H'.
rewrite H'.
assert (H'' := nu_equals re re' H).
rewrite H''; auto.
Qed.

Lemma match_lenEmpty : forall s, match_len Empty s = None.
Proof.
induction s; simpl; auto.
rewrite IHs; auto.
Qed.

Lemma match_lenEps : forall s, match_len Eps s = Some 0.
Proof.
induction s; simpl; auto.
rewrite match_lenEmpty; auto.
Qed.

Lemma match_len_equiv_opt__ : forall s re, match_len_opt re s = (
  match s with
  | EmptyString => if nu re then Some 0 else None
  | String a s2 => (match match_len_opt (simplify ( (simplify re) /a)) s2 with
                    | Some l => Some (S l)
                    | None => if nu (simplify re) then Some 0 else None
                    end)
  end
).
Proof.
induction s.
simpl.
intros. 
case_eq (simplify re); intros; assert (H0 := simpl_correct re); assert (H1 := nu_equals re (simplify re) H0); rewrite H in *; simpl in *; rewrite H1; auto.
simpl.
intros.
case_eq (simplify re); simpl; auto.
intros.
case_eq s; simpl; auto.
case_eq s; simpl; auto.
Qed.

Lemma match_len_equiv_opt : forall s re, match_len re s = match_len_opt re s.
Proof.
induction s.
intro.
simpl; case_eq (simplify re); simpl; auto; intros.
apply simpl_correct_empty in H.
rewrite H; simpl; auto.
apply simpl_correct_eps in H.
rewrite H; simpl; auto.
assert (H0 := simpl_correct re); assert (H1 := nu_equals re (simplify re) H0); rewrite H in *; simpl in *; rewrite H1; auto.
assert (H0 := simpl_correct re); assert (H1 := nu_equals re (simplify re) H0); rewrite H in *; simpl in *; rewrite H1; auto.
assert (H0 := simpl_correct re); assert (H1 := nu_equals re (simplify re) H0); rewrite H in *; simpl in *; rewrite H1; auto.
assert (H0 := simpl_correct re); assert (H1 := nu_equals re (simplify re) H0); rewrite H in *; simpl in *; rewrite H1; auto.
assert (H0 := simpl_correct re); assert (H1 := nu_equals re (simplify re) H0); rewrite H in *; simpl in *; rewrite H1; auto.
assert (H0 := simpl_correct re); assert (H1 := nu_equals re (simplify re) H0); rewrite H in *; simpl in *; rewrite H1; auto.
intros.
rewrite match_len_equiv_opt__.
simpl (match_len re (String a s)).
assert (match_len (re / a) s = match_len (simplify (simplify re / a)) s).
apply match_len_re_eq.
assert (re / a =R= simplify re / a ).
apply derive_equals.
apply simpl_correct.
rewrite H.
apply simpl_correct.
assert (H0 := IHs (simplify (simplify re / a))).
rewrite H in *.
rewrite H0 in *.
assert (nu re = nu (simplify re)).
apply nu_equals.
apply simpl_correct.
rewrite H1; auto.
Qed.

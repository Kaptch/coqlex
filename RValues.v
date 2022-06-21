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
Require Import Coq.Lists.List.
Import ListNotations.
Require Import micromega.Lia.
Require Import UsefullProofs.
Import Arith.PeanoNat.

Fixpoint charList_to_re l := match l with
| [] => Empty
| h::t => Or (Char h) (charList_to_re t)
end.


Lemma charList_to_re_correct : forall l c s, matches (charList_to_re l) (String c s) = true <-> (s = EmptyString /\ In c l).
Proof.
induction l.
simpl.
split.
intros.
assert (Empty ~!= s).
apply Empty_false.
unfold matches in *.
rewrite H0 in H.
discriminate.
intros.
destruct H.
auto.
split.
intros.
simpl.
simpl (charList_to_re (a :: l)) in H.
rewrite matches_Or in H.
apply Bool.orb_true_iff in H.
simpl (Char a ~== String c s) in H.
destruct (ascii_dec a c).
destruct H.
assert (s = ""%string).
case_eq s; auto.
intros.
assert (Eps ~!= (String a0 s0)).
apply Eps_false.
intuition.
inversion H1.
rewrite H0 in H.
unfold matches in H, H1.
rewrite H in H1.
discriminate.
auto.
apply IHl in H.
destruct H.
auto.
destruct H.
assert (Empty ~!= s).
apply Empty_false.
unfold matches in H, H0.
rewrite H in H0; try discriminate.
apply IHl in H.
destruct H.
split.
auto.
right.
auto.
intros.
destruct H.
inversion H0.
rewrite H.
simpl.
induction (ascii_dec a c).
auto.
auto.
simpl (charList_to_re (a :: l)).
rewrite matches_Or.
apply Bool.orb_true_iff.
right.
apply IHl.
auto.
Qed.

(* Definition regex_any := charList_to_re ["000"%char; "001"%char; "002"%char; "003"%char; "004"%char; "005"%char; "006"%char; "007"%char; "008"%char; "009"%char; "010"%char; "011"%char; "012"%char; "013"%char; "014"%char; "015"%char; "016"%char; "017"%char; "018"%char; "019"%char; "020"%char; "021"%char; "022"%char; "023"%char; "024"%char; "025"%char; "026"%char; "027"%char; "028"%char; "029"%char; "030"%char; "031"%char; "032"%char; "033"%char; "034"%char; "035"%char; "036"%char; "037"%char; "038"%char; "039"%char; "040"%char; "041"%char; "042"%char; "043"%char; "044"%char; "045"%char; "046"%char; "047"%char; "048"%char; "049"%char; "050"%char; "051"%char; "052"%char; "053"%char; "054"%char; "055"%char; "056"%char; "057"%char; "058"%char; "059"%char; "060"%char; "061"%char; "062"%char; "063"%char; "064"%char; "065"%char; "066"%char; "067"%char; "068"%char; "069"%char; "070"%char; "071"%char; "072"%char; "073"%char; "074"%char; "075"%char; "076"%char; "077"%char; "078"%char; "079"%char; "080"%char; "081"%char; "082"%char; "083"%char; "084"%char; "085"%char; "086"%char; "087"%char; "088"%char; "089"%char; "090"%char; "091"%char; "092"%char; "093"%char; "094"%char; "095"%char; "096"%char; "097"%char; "098"%char; "099"%char; "100"%char; "101"%char; "102"%char; "103"%char; "104"%char; "105"%char; "106"%char; "107"%char; "108"%char; "109"%char; "110"%char; "111"%char; "112"%char; "113"%char; "114"%char; "115"%char; "116"%char; "117"%char; "118"%char; "119"%char; "120"%char; "121"%char; "122"%char; "123"%char; "124"%char; "125"%char; "126"%char; "127"%char; "128"%char; "129"%char; "130"%char; "131"%char; "132"%char; "133"%char; "134"%char; "135"%char; "136"%char; "137"%char; "138"%char; "139"%char; "140"%char; "141"%char; "142"%char; "143"%char; "144"%char; "145"%char; "146"%char; "147"%char; "148"%char; "149"%char; "150"%char; "151"%char; "152"%char; "153"%char; "154"%char; "155"%char; "156"%char; "157"%char; "158"%char; "159"%char; "160"%char; "161"%char; "162"%char; "163"%char; "164"%char; "165"%char; "166"%char; "167"%char; "168"%char; "169"%char; "170"%char; "171"%char; "172"%char; "173"%char; "174"%char; "175"%char; "176"%char; "177"%char; "178"%char; "179"%char; "180"%char; "181"%char; "182"%char; "183"%char; "184"%char; "185"%char; "186"%char; "187"%char; "188"%char; "189"%char; "190"%char; "191"%char; "192"%char; "193"%char; "194"%char; "195"%char; "196"%char; "197"%char; "198"%char; "199"%char; "200"%char; "201"%char; "202"%char; "203"%char; "204"%char; "205"%char; "206"%char; "207"%char; "208"%char; "209"%char; "210"%char; "211"%char; "212"%char; "213"%char; "214"%char; "215"%char; "216"%char; "217"%char; "218"%char; "219"%char; "220"%char; "221"%char; "222"%char; "223"%char; "224"%char; "225"%char; "226"%char; "227"%char; "228"%char; "229"%char; "230"%char; "231"%char; "232"%char; "233"%char; "234"%char; "235"%char; "236"%char; "237"%char; "238"%char; "239"%char; "240"%char; "241"%char; "242"%char; "243"%char; "244"%char; "245"%char; "246"%char; "247"%char; "248"%char; "249"%char; "250"%char; "251"%char; "252"%char; "253"%char; "254"%char; "255"%char].

Definition regex_az := charList_to_re ["097"%char; "098"%char; "099"%char; "100"%char; "101"%char; "102"%char; "103"%char; "104"%char; "105"%char; "106"%char; "107"%char; "108"%char; "109"%char; "110"%char; "111"%char; "112"%char; "113"%char; "114"%char; "115"%char; "116"%char; "117"%char; "118"%char; "119"%char; "120"%char; "121"%char; "122"%char].

Definition regex_AZ := charList_to_re ["065"%char; "066"%char; "067"%char; "068"%char; "069"%char; "070"%char; "071"%char; "072"%char; "073"%char; "074"%char; "075"%char; "076"%char; "077"%char; "078"%char; "079"%char; "080"%char; "081"%char; "082"%char; "083"%char; "084"%char; "085"%char; "086"%char; "087"%char; "088"%char; "089"%char; "090"%char].

Definition regex_09 := charList_to_re ["048"%char; "049"%char; "050"%char; "051"%char; "052"%char; "053"%char; "054"%char; "055"%char; "056"%char; "057"%char].

Definition regex_alpha := Or regex_az regex_AZ.

Definition regex_alphanum := Or regex_alpha regex_09. *)

Fixpoint rangeAscii l len :=
match len with
| 0 => []
| S n => if Nat.ltb l 256 then (ascii_of_nat l)::(rangeAscii (S l) n) else []
end.

Lemma rangeAscii_correct : forall len l a, (nat_of_ascii a) >= l -> (nat_of_ascii a) < l + len -> In a (rangeAscii l len).
Proof.
induction len.
intros.
lia.
simpl.
intros.
case_eq (l <? 256).
intros.
apply Nat.ltb_lt in H1.
simpl.
inversion H.
left.
apply ascii_nat_embedding; auto.
right.
apply IHlen; lia.
intro.
apply Nat.ltb_ge in H1.
assert (nat_of_ascii a < 256).
apply nat_ascii_bounded.
lia.
Qed.

Lemma rangeAscii_correct2 : forall len l a, In a (rangeAscii l len) -> (nat_of_ascii a) >= l /\ (nat_of_ascii a) < l + len.
Proof.
induction len.
simpl.
intros.
intuition.
simpl.
intro.
case_eq (l <? 256).
intros.
apply Nat.ltb_lt in H.
inversion H0.
assert (nat_of_ascii (ascii_of_nat l) = nat_of_ascii a).
f_equal.
auto.
rewrite nat_ascii_embedding in H2.
lia.
auto.
apply IHlen in H1.
lia.
intros.
inversion H0.
Qed.

Definition rangeAscii2 a b := rangeAscii (min (nat_of_ascii a) (nat_of_ascii b)) (S ((max (nat_of_ascii a) (nat_of_ascii b)) - (min (nat_of_ascii a) (nat_of_ascii b)))).

Lemma min_plus_delta : forall a b, min a b + S ((max a b) - (min a b)) = S (max a b).
Proof.
induction a, b; simpl; try lia.
Qed.

Lemma rangeAscii2_correct : forall a l u, In a (rangeAscii2 l u) <-> (nat_of_ascii a) >= (min (nat_of_ascii l) (nat_of_ascii u)) /\ (nat_of_ascii a) <= (max (nat_of_ascii l) (nat_of_ascii u)).
Proof.
split.
intros.
unfold rangeAscii2 in H.
apply rangeAscii_correct2 in H.
rewrite min_plus_delta in H.
lia.
intros.
unfold rangeAscii2.
apply rangeAscii_correct.
lia.
rewrite min_plus_delta.
lia.
Qed.

(* Compute (rangeAscii2 "a"%char "b"%char).
 *)
Definition regex_any := charList_to_re (rangeAscii2 "000"%char "255"%char).

Definition regex_az := charList_to_re (rangeAscii2 "a"%char "z"%char).

Definition regex_AZ := charList_to_re (rangeAscii2 "A"%char "Z"%char).

Definition regex_09 := charList_to_re (rangeAscii2 "0"%char "9"%char).

Definition regex_alpha := Or regex_az regex_AZ.

Definition regex_alphanum := Or regex_alpha regex_09.

Definition all_char := rangeAscii2 "000"%char "255"%char.

Lemma any_char_is_in_all_char : forall i, In i all_char.
Proof.
intros.
apply rangeAscii2_correct.
simpl.
split.
lia.
unfold nat_of_ascii.
simpl.
unfold BinPos.Pos.to_nat.
simpl.
assert (BinNat.N.to_nat (N_of_ascii i) < 256).
apply nat_ascii_bounded.
lia.
Qed.

Definition any_char_but_list l := fold_left (fun l x => remove ascii_dec x l) l all_char.

Lemma any_char_but_list_correct1 : forall l a, In a l -> ~In a (any_char_but_list l).
Proof.
intros.
unfold any_char_but_list.
apply (rm_fold_left_correct ascii_dec l); auto.
Qed.

Lemma any_char_but_list_correct2 : forall l a, ~In a l -> In a (any_char_but_list l).
Proof.
intros.
eapply (rm_fold_left_correct2 ascii_dec); eauto.
apply any_char_is_in_all_char.
Qed.

Definition class_char_except l := charList_to_re (any_char_but_list l).

Lemma class_char_except_correct : forall l c s, matches (class_char_except l) (String c s) = true <-> (s = EmptyString /\ ~In c l).
Proof.
unfold class_char_except.
split.
intros.
apply charList_to_re_correct in H.
destruct H.
split.
auto.
intuition.
apply any_char_but_list_correct1 in H1.
contradiction.
intros.
apply charList_to_re_correct.
destruct H.
split.
auto.
apply any_char_but_list_correct2; auto.
Qed.

Definition num_of_ascii (c: ascii) : option nat :=
 match c with
   | "0"%char => Some 0
   | "1"%char => Some 1
   | "2"%char => Some 2
   | "3"%char => Some 3
   | "4"%char => Some 4
   | "5"%char => Some 5
   | "6"%char => Some 6
   | "7"%char => Some 7
   | "8"%char => Some 8
   | "9"%char => Some 9
   | _ => None
end.

Fixpoint reverseStringAcc s acc := match s with
| EmptyString => acc
| String h t => reverseStringAcc t (String h acc)
end.

Definition reverseString s := reverseStringAcc s ""%string.

(* Compute (reverseString "hello5").
 *)
Fixpoint num_of_string_rec (s : string) : option nat :=
  match s with
    | EmptyString => Some 0
    | String c rest => 
       match (num_of_ascii c), (num_of_string_rec rest) with
          | Some n, Some m => Some (n + 10 * m)
          | _ , _ => None
       end
   end.

Fixpoint num_of_string s := num_of_string_rec (reverseString s).

(* Compute (num_of_string "526").
 *)

Definition regex_0_255_3digits := 
  Or 
    (Cat (charList_to_re (rangeAscii2 "0"%char "1"%char)) (Cat (charList_to_re (rangeAscii2 "0"%char "9"%char)) (charList_to_re (rangeAscii2 "0"%char "9"%char))))
    (Or 
      (Cat (Char "2"%char) (Cat (charList_to_re (rangeAscii2 "0"%char "4"%char)) (charList_to_re (rangeAscii2 "0"%char "9"%char))))
      (Cat (Char "2"%char) (Cat (Char "5"%char) (charList_to_re (rangeAscii2 "0"%char "5"%char))))).

Definition escaped_char_simple := Cat (Char "\"%char) (charList_to_re ["\"%char; """"%char; "'"%char; "n"%char; "t"%char; "b"%char; "r"%char ]).

Definition escaped_char_num := Cat (Char "\"%char) regex_0_255_3digits.

Definition ponctuation := Or (charList_to_re (rangeAscii2 " "%char "/"%char)) (Or (charList_to_re (rangeAscii2 ":"%char "@"%char)) (Or (charList_to_re (rangeAscii2 "["%char "`"%char)) (charList_to_re (rangeAscii2 "{"%char "~"%char)))).

(* Compute (matches ponctuation "["). *)

Fixpoint removeLast s := match s with
    | String e EmptyString => EmptyString
    | EmptyString => EmptyString
    | String e st => String e (removeLast st)
  end.

Definition removeFirst s := match s with
    | String e s => s
    | EmptyString => EmptyString
  end.

(* Compute (matches escaped_char_simple "\n").
 *)
(* Compute (matches escaped_char_num "\255"). *)
Definition removeFirstAndLast str := removeLast (removeFirst str).

Definition to_Char str := match str with
| String h EmptyString => Some h
| _ => None
end.

Definition minus r r' := And r (Not r').

Lemma minus_correct : forall s r r', matches (minus r r') s = (andb (matches r s) (negb (matches r' s))).
Proof.
unfold minus.
intros.
rewrite matches_And.
rewrite matches_Not.
auto.
Qed.

Fixpoint list_diff a b := match a with
| [] => []
| ha::ta => if existsb (Ascii.eqb ha) b then list_diff ta b else ha::(list_diff ta b)
end.

Lemma exists_eqb_true_in : forall a b, existsb (Ascii.eqb a) b = true <-> In a b.
Proof.
intros.
split; intros.
apply existsb_exists in H.
destruct H.
destruct H.
apply Ascii.eqb_eq in H0.
rewrite H0 in *; auto.
induction b; auto.
simpl.
simpl in H.
apply Bool.orb_true_iff.
destruct H.
left.
apply Ascii.eqb_eq; auto.
right.
apply IHb; auto.
Qed.

Lemma exists_eqb_false_in : forall b a , existsb (Ascii.eqb a) b = false <-> ~In a b.
Proof.
induction b; simpl.
split; auto.
split.
intros.
apply Bool.orb_false_iff in H.
destruct H.
apply Ascii.eqb_neq in H.
apply IHb in H0.
intuition.
intros.
intuition.
apply Bool.orb_false_iff .
split.
apply Ascii.eqb_neq.
intuition.
apply IHb; auto.
Qed.

Lemma list_diff_correct : forall a b e, In e (list_diff a b) <-> In e a /\ ~In e b.
Proof.
induction a.
simpl.
intuition.
simpl.
intro.
case_eq (existsb (Ascii.eqb a) b); intro.
split; intros.
apply exists_eqb_true_in in H.
apply IHa in H0.
split.
right.
intuition.
intuition.
apply exists_eqb_true_in in H.
apply IHa.
destruct H0.
destruct H0.
rewrite H0 in *.
intuition.
intuition.
apply exists_eqb_false_in in H.
simpl.
split.
intros.
destruct H0.
rewrite H0 in *.
intuition.
apply IHa in H0.
intuition.
intros.
destruct H0.
destruct H0.
intuition.
right.
apply IHa.
intuition.
Qed.

Definition identifier := (Cat regex_az (Star (Or regex_alphanum (Char "_"%char)))).

Definition printable_chars := charList_to_re (rangeAscii2 " "%char "~"%char).

Definition string_regex := (Cat (Char """"%char) (Cat (Star (Or (Cat (Char "\"%char) regex_any ) (class_char_except ["\"%char; """"%char] ) )) (Char """"%char))).

(* Definition string_regex := (Cat (Char """"%char) (Cat (Star (Or (Cat (Char "\"%char) (Char """"%char) ) (charList_to_re (list_diff (rangeAscii2 " "%char "~"%char) [""""%char] )) )) (Char """"%char))). *)

Require Import MatchLenSpeedUp2.

Fixpoint ocamlStrInterp str := match str with
| (String "\"%char (String "n"%char s)) => String "010"%char (ocamlStrInterp s)
| (String "\"%char (String "t"%char s)) => String "009"%char (ocamlStrInterp s)
| (String "\"%char (String "b"%char s)) => String "008"%char (ocamlStrInterp s)
| (String "\"%char (String """"%char s)) => String "034"%char (ocamlStrInterp s)
| (String "\"%char (String "'"%char s)) => String "039"%char (ocamlStrInterp s)
| (String "\"%char (String "\"%char s)) => String "092"%char (ocamlStrInterp s)
| (String "\"%char (String "r"%char s)) => String "013"%char (ocamlStrInterp s) 
| (String "\"%char r )
    => (match match_len_opt regex_0_255_3digits r, r with
        | Some _, (String p (String p2 (String p3 s))) => 
          (match num_of_string (String p (String p2 (String p3 EmptyString))) with
           | Some v => String (ascii_of_nat v) (ocamlStrInterp s)
           | None => String ("\"%char) (ocamlStrInterp r)
          end)
        | _, _ => String ("\"%char) (ocamlStrInterp r)
        end)
| (String h t) => String h (ocamlStrInterp t)
| EmptyString => EmptyString
end.

Definition char_regex := (Cat (Char "'"%char) (Cat (Or printable_chars (Or escaped_char_num escaped_char_simple))  (Char "'"%char))).
(* 
Definition contains_no_bracket := (Star (class_char_except ["{"%char; "}"%char] )).

Definition bracket_that_contains_no_nested_brackets := (Cat (Char "{"%char) (Cat contains_no_bracket (Char "}"%char))).

Definition bracket_that_can_contain_L1_nested_brackets := (Cat (Char "{"%char) (Cat (Star (Or contains_no_bracket bracket_that_contains_no_nested_brackets)) (Char "}"%char))).

Definition accepted_bracket_content := bracket_that_can_contain_L1_nested_brackets .*)


(* Compute (matches string_regex """\"""""). *)









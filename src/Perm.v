From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.

Check lt.

Check Nat.ltb.

Locate "_ < _".
Locate "_ <? _".

Print Nat.ltb.
Print lt.


Notation "a >=? b" := (Nat.leb b a)
                        (at level 70) : nat_scope.
Notation "a >? b" := (Nat.ltb b a)
                       (at level 70) : nat_scope.

Theorem omega_example2:
  forall i j k,
    i < j -> ~(k - 3 <= j) -> k > i.
Proof.
  intros.
  omega.
Qed.

Print reflect.

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros.
  apply iff_reflect.
  symmetry.
  apply Nat.eqb_eq.
Qed.

Check Nat.eqb_eq.

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros.
  apply iff_reflect.
  symmetry.
  apply Nat.ltb_lt.
Qed.

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros.
  apply iff_reflect.
  symmetry.
  apply Nat.leb_le.
Qed.

Example reflect_example1': forall a,
    (if a <? 5 then a else 2) < 6.
Proof.
  intros.
  destruct (ltb_reflect a 5); omega.
Qed.

Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

Example reflect_example2: forall a,
    (if a <? 5 then a else 2) < 6.
Proof.
  intros.
  bdestruct (a <? 5); omega.
Qed.

Definition maybe_swap (al: list nat) : list nat :=
  match al with
  | a :: b :: ar => if a >? b then b :: a :: ar else a :: b :: ar
  | _ => al
  end.

Theorem maybe_swap_idempotent: forall al,
    maybe_swap (maybe_swap al) = maybe_swap al.
Proof.
  intros [ | a [ | b al]]; try reflexivity.
  simpl.
  bdestruct (a <? b); simpl.
  { bdestruct (a >? b); simpl.
    { omega. }
    { bdestruct (a >? b).
      { omega. }
      { reflexivity. } } }
  { bdestruct (a >? b).
    { simpl.
      bdestruct (b >? a).
      { omega. }
      { reflexivity. } }
    { simpl.
      bdestruct (a >? b).
      { omega. }
      { reflexivity. } } }
Qed.

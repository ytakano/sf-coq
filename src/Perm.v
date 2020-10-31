From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Require Export Permutation.
Export ListNotations.


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

Print Permutation.

Definition manual_grade_for_Permutation_properties : option (nat * string) := None.

Example butterfly : forall b u t e r f l y : nat,
    Permutation ([b;u;t;t;e;r]++[f;l;y]) ([f;l;u;t;t;e;r]++[b;y]).
Proof.
  intros.
  change [b;u;t;t;e;r] with ([b]++[u;t;t;e;r]).
  change [f;l;u;t;t;e;r] with ([f;l]++[u;t;t;e;r]).
  remember [u;t;t;e;r] as utter.
  clear Hequtter.
  change [f;l;y] with ([f;l]++[y]).
  remember [f;l] as fl.
  clear Heqfl.
  replace ((fl++utter)++[b;y]) with (fl++utter++[b;y]) by apply app_assoc.
  apply perm_trans with (fl++[y]++([b]++utter)).
  { replace (fl++[y]++[b]++utter) with ((fl++[y])++[b]++utter).
    { apply Permutation_app_comm. }
    { rewrite <- app_assoc.
      reflexivity. } }
  { apply Permutation_app_head.
    apply perm_trans with (utter++([y]++[b])).
    { replace ([y]++[b]++utter) with (([y]++[b])++utter).
      { apply Permutation_app_comm. }
      { rewrite app_assoc.
        reflexivity. } }
    { apply Permutation_app_head.
      apply perm_swap. } }
Qed.

Check perm_skip.
Check perm_trans.
Check Permutation_refl.
Check Permutation_app_comm.
Check app_assoc.
Check app_nil_r.
Check app_comm_cons.

Example permut_example : forall (a b : list nat),
    Permutation (5 :: 6 :: a ++ b) ((5 :: b) ++ (6 :: a ++ [])).
Proof.
  intros.
  rewrite app_nil_r.
  rewrite <- app_comm_cons.
  apply perm_skip.
  rewrite app_comm_cons.
  apply Permutation_app_comm.
Qed.

Check Permutation_cons_inv.
Check Permutation_length_1_inv.

Example not_a_permutation:
  ~ Permutation [1;1] [1;2].
Proof.
  unfold not.
  intros.
  apply Permutation_cons_inv in H.
  apply Permutation_length_1_inv in H.
  discriminate.
Qed.

Theorem maybe_swap_perm: forall al,
    Permutation al (maybe_swap al).
Proof.
  unfold maybe_swap.
  destruct al as [ | a [ | b al]].
  { apply perm_nil. }
  { apply Permutation_refl. }
  { bdestruct (b <? a).
    { apply perm_swap. }
    { apply Permutation_refl. } }
Qed.

Definition first_le_second (al : list nat) : Prop :=
  match al with
  | a :: b :: _ => a <= b
  | _ => True
  end.

Theorem maybe_swap_correct : forall al,
    Permutation al (maybe_swap al) /\ first_le_second (maybe_swap al).
Proof.
  intros.
  split.
  { apply maybe_swap_perm. }
  { unfold maybe_swap.
    destruct al as [ | a [ | b al]]; simpl; auto.
    bdestruct (a >? b); simpl; omega. }
Qed.

Ltac inv H := inversion H; clear H; subst.

Print perm_nil.

Print Forall.

Print Permutation.

Theorem Forall_perm: forall {A} (f : A -> Prop) al bl,
    Permutation al bl -> Forall f al -> Forall f bl.
Proof.
  intros.
  induction H.
  { constructor. }
  { constructor.
    { inv H0.
      assumption. }
    { apply IHPermutation.
      inv H0.
      assumption. } }
  { inv H0.
    inv H3.
    repeat constructor; assumption. }
  { apply IHPermutation2.
    apply IHPermutation1.
    assumption. }
Qed.

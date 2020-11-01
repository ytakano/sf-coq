From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
Require Import Perm.

Fixpoint insert (i : nat) (l : list nat) :=
  match l with
  | [] => [i]
  | h :: t => if i <=? h then i :: h :: t else h :: insert i t
  end.

Fixpoint sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)
  end.

Example sort_pi : sort [3;1;4;1;5;9;2;6;5;3;5] = [1;1;2;3;3;4;5;5;5;6;9].
Proof.
  reflexivity.
Qed.

Inductive sorted : list nat -> Prop :=
| sorted_nil : sorted []
| sorted_l : forall x, sorted [x]
| sorted_cons : forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Check nth : forall A : Type, nat -> list A -> A -> A.
Check nth_error : forall A : Type, list A -> nat -> option A.

Definition sorted'' (al : list nat) := forall i j,
    i < j < length al -> nth i al 0 <= nth j al 0.

Definition sorted' (al : list nat) := forall i j iv jv,
    i < j ->
    nth_error al j = Some jv ->
    nth_error al j = Some jv ->
    iv <= jv.

Definition is_a_sorting_algorithm (f : list nat -> list nat) := forall al,
    Permutation al (f al) /\ sorted (f al).

Lemma insert_sorted: forall a l,
    sorted l -> sorted (insert a l).
Proof.
  intros a l S.
  induction S; simpl.
  { constructor. }
  { bdestruct (x >=? a); constructor; try assumption; try constructor.
    omega. }
  { bdestruct (x >=? a).
    { repeat constructor; assumption. }
    { bdestruct (y >=? a); repeat constructor; try assumption; try omega.
      simpl in IHS.
      bdestruct (y >=? a); try omega; assumption. } }
Qed.

Theorem sort_sorted : forall l, sorted (sort l).
Proof.
  induction l.
  { simpl.
    constructor. }
  { simpl.
    apply insert_sorted.
    assumption. }
Qed.

Lemma insert_perm : forall x l,
    Permutation (x :: l) (insert x l).
Proof.
  induction l.
  { repeat constructor. }
  { simpl.
    bdestruct (a >=? x); auto.
    apply Permutation_sym.
    replace (x :: a :: l) with ([x] ++ a :: l).
    { apply Permutation_cons_app.
      simpl.
      apply Permutation_sym.
      assumption. }
    { reflexivity. } }
Qed.

Lemma insert_perm_h : forall x l l',
    Permutation l l' -> Permutation (x :: l) (insert x l').
Proof.
  intros.
  induction H.
  { simpl; repeat constructor. }
  { simpl.
    bdestruct (x0 >=? x).
    { repeat constructor; assumption. }
    { apply Permutation_sym.
      replace (x :: x0 :: l) with ([x] ++ x0 :: l).
      { apply Permutation_cons_app.
        simpl.
        apply Permutation_sym.
        assumption. }
      { reflexivity. } } }
  { simpl.
    bdestruct (x0 >=? x).
    { constructor.
      replace (x0 :: y :: l) with ([x0] ++ y :: l).
      { apply Permutation_cons_app.
        auto. }
      { reflexivity. } }
    { bdestruct (y >=? x).
      { replace (x0 :: x :: y :: l) with ([x0] ++ x :: y :: l).
        { repeat apply Permutation_cons_app.
          auto. }
        { reflexivity. } }
      { apply Permutation_sym.
        replace (x :: y :: x0 :: l) with ([x;y] ++ x0 :: l).
        { apply Permutation_cons_app.
          simpl.
          replace (x :: y :: l) with ([x] ++ y :: l).
          { apply Permutation_cons_app,Permutation_sym.
            simpl.
            apply insert_perm. }
          { reflexivity. } }
        { reflexivity. } } } }
  { apply perm_trans with (l'':=l'') in H; try assumption.
    apply perm_skip with (x:=x) in H.
    apply Permutation_sym in H.
    apply perm_trans with (l'':=(insert x l')) in H; try assumption.
    apply perm_skip with (x:=x) in H0.
    apply Permutation_sym in H.
    apply perm_trans with (l'':=x::l'') in IHPermutation1; try assumption.
    apply Permutation_sym in H0.
    apply perm_trans with (l'':=x::l') in IHPermutation1; try assumption.
    apply perm_trans with (l'':=(insert x l'')) in IHPermutation1; try assumption. }
Qed.

Theorem sort_perm : forall l, Permutation l (sort l).
Proof.
  intros.
  induction l; try reflexivity.
  simpl.
  inv IHl.
  { reflexivity. }
  { simpl.
    rewrite <- H.
    simpl.
    bdestruct (x >=? a).
    { auto. }
    {



  induction sort.
  { inv IHl.
    { simpl.
      repeat constructor. }
    { simpl.
      apply Permutation_sym,Permutation_nil in H0.
      subst.
      apply Permutation_sym,Permutation_nil in H.
      subst.
      repeat constructor. } }
  { simpl.
    bdestruct (a0 >=? a).

From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
Require Import Psatz.
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
| sorted_1 : forall x, sorted [x]
| sorted_cons : forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Check nth : forall A : Type, nat -> list A -> A -> A.
Check nth_error : forall A : Type, list A -> nat -> option A.

Definition sorted'' (al : list nat) := forall i j,
    i < j < length al -> nth i al 0 <= nth j al 0.

Definition sorted' (al : list nat) := forall i j iv jv,
    i < j ->
    nth_error al i = Some iv ->
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
    lia. }
  { bdestruct (x >=? a).
    { repeat constructor; assumption. }
    { bdestruct (y >=? a); repeat constructor; try assumption; try lia.
      simpl in IHS.
      bdestruct (y >=? a); try lia; assumption. } }
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

Lemma perm_then_insert : forall x l l',
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
    { apply Permutation_sym.
      replace (a :: x :: l0) with ([a] ++ x :: l0).
      { apply Permutation_cons_app.
        simpl.
        apply Permutation_sym.
        apply perm_then_insert.
        assumption. }
      { reflexivity. } } }
  { simpl.
    apply perm_then_insert.
    rewrite <- H1.
    replace (x :: y :: l0) with ([x] ++ y :: l0).
    { apply Permutation_cons_app.
      auto. }
    { reflexivity. } }
  { apply perm_then_insert.
    apply perm_trans with (l:=l) (l':=l') (l'':=(sort l)) in H; assumption. }
Qed.

Theorem insertion_sort_correct:
  is_a_sorting_algorithm sort.
Proof.
  unfold is_a_sorting_algorithm.
  intros.
  split.
  { apply sort_perm. }
  { apply sort_sorted. }
Qed.

Lemma nil_nth_none: forall (A : Type) (l : list A) n,
    l = [] -> nth_error l n = None.
Proof.
  intros.
  induction n.
  { rewrite H.
    reflexivity. }
  { simpl.
    rewrite H.
    reflexivity. }
Qed.

(*
Lemma nth_succ: forall (A : Type) x y (l : list A) n,
    nth_error (x :: y :: l) 0 = Some n -> nth_error (y :: l) 1 = Some n.
Proof.
  intros.
 *)

Lemma add_min_sorted: forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).
Proof.
  intros.
  constructor; assumption.
Qed.

Lemma nth_error_elm1: forall (A : Type) (x y : A) n,
    nth_error [x] n = Some y -> n = 0.
Proof.
  intros.
  induction n.
  { reflexivity. }
  { simpl in H.
    remember [] in H.
    apply nil_nth_none with (n:=n) in Heql.
    rewrite Heql in H.
    discriminate. }
Qed.

Lemma add_min_sorted'_1: forall x y,
    x <= y -> sorted' ([x;y]).
Proof.
  unfold sorted'.
  intros.
  destruct H0.
  { simpl in H2.
    remember H2.
    clear Heqe.
    apply nth_error_elm1 in H2.
    subst.
    simpl in e.
    simpl in H1.
    inv H1.
    inv e.
    assumption. }
  { remember H2.
    simpl in H2.
    clear Heqe.
    apply nth_error_elm1 in H2.
    subst.
    inv H0. }
Qed.

Lemma sorted'_nil: sorted' [].
Proof.
  unfold sorted'.
  intros.
  remember [] in H0.
  apply nil_nth_none with (n:=i) in Heql.
  rewrite Heql in H0.
  discriminate.
Qed.

Lemma sorted'_1: forall x,
    sorted' [x].
Proof.
  unfold sorted'.
  intros.
  remember H0.
  remember H1.
  clear Heqe.
  clear Heqe0.
  apply nth_error_elm1 in H0.
  apply nth_error_elm1 in H1.
  subst.
  inv H.
Qed.

Lemma sorted'_head_min: forall x y n l,
    sorted' (x :: l) -> nth_error (x :: l) n = Some y -> x <= y.
Proof.
  intros.
  destruct n.
  { simpl in H0.
    inversion H0.
    lia. }
  { induction n.
    { unfold sorted' in H.
      apply H with (i:=0) (j:=1); auto. }
    { unfold sorted' in H.
      apply H with (i:=0) (j:=S (S n)); auto.
      lia. } }
Qed.

Lemma sorted'_cons: forall x y l,
    x <= y -> sorted' (y :: l) -> sorted' (x :: y :: l).
Proof.
  intros.
  unfold sorted'.
  induction j.
  { unfold sorted' in H0.
    intros.
    induction i; inv H1. }
  { induction i.
    { intros.
      simpl in H2.
      inv H2.
      simpl in H3.
      apply sorted'_head_min with (y:=jv) (n:=j) in H0; auto; lia. }
    { intros.
      simpl in H2.
      simpl in H3.
      apply H0 with (i:=i) (j:=j); auto; lia. } }
Qed.

Lemma sorted_sorted': forall al,
    sorted al -> sorted' al.
Proof.
  intros.
  induction H.
  { unfold sorted'.
    induction i; intros; discriminate. }
  { unfold sorted'.
    induction i.
    { intros.
      simpl in H0.
      inv H0.
      induction j.
      { simpl in H1.
        inv H1.
        reflexivity. }
      { simpl in H1.
        remember [] as l.
        apply nil_nth_none with (n:=j) in Heql.
        rewrite Heql in H1.
        discriminate. } }
    { intros.
      inv H0.
      remember [] as l.
      apply nil_nth_none with (n:=i) in Heql.
      rewrite Heql in H3.
      discriminate. } }
  { apply sorted'_cons; auto. }
Qed.

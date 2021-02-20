From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
Require Import Psatz.
Require Import Sort.
Require Import Perm.
Export ListNotations.

Definition value := nat.
Definition multiset := value -> nat.

Definition empty : multiset :=
  fun x => 0.

Definition singleton (v : value) : multiset :=
  fun x => if x =? v then 1 else 0.

Definition union (a b : multiset) : multiset :=
  fun x => a x + b x.

Lemma union_assoc: forall a b c : multiset,
    union a (union b c) = union (union a b) c.
Proof.
  intros.
  extensionality x.
  unfold union.
  lia.
Qed.

Lemma union_comm: forall a b : multiset,
    union a b = union b a.
Proof.
  intros.
  extensionality x.
  unfold union.
  lia.
Qed.

Lemma union_swap: forall a b c : multiset,
    union a (union b c) = union b (union a c).
Proof.
  intros.
  extensionality x.
  unfold union.
  lia.
Qed.

Fixpoint contents (al : list value) : multiset :=
  match al with
  | [] => empty
  | a :: bl => union (singleton a) (contents bl)
  end.

Example sort_pi_same_contents:
  contents (sort [3;1;4;1;5;9;2;6;5;3;5]) = contents [3;1;4;1;5;9;2;6;5;3;5].
Proof.
  extensionality x.
  repeat (destruct x; try reflexivity).
Qed.

Definition is_a_sorting_algorithm' (f : list nat -> list nat) := forall al,
    contents al = contents (f al) /\ sorted (f al).

Lemma insert_contents: forall x l,
    contents (insert x l) = contents (x :: l).
Proof.
  intros.
  induction l.
  { simpl.
    reflexivity. }
  { inversion IHl.
    simpl.
    destruct (x <=? a).
    { simpl.
      reflexivity. }
    { simpl.
      rewrite H0.
      apply union_swap. } }
Qed.

Theorem sort_contents: forall l,
    contents l = contents (sort l).
Proof.
  intros.
  induction l.
  { simpl.
    reflexivity. }
  { simpl.
    replace (contents (insert a (sort l))) with (contents (a :: (sort l))).
    { simpl.
      rewrite IHl.
      reflexivity. }
    { symmetry.
      apply insert_contents. } }
Qed.

Theorem insertion_sort_correct:
  is_a_sorting_algorithm' sort.
Proof.
  unfold is_a_sorting_algorithm'.
  intros.
  split.
  { apply sort_contents. }
  { apply sort_sorted. }
Qed.

Definition manual_grade_for_permutations_vs_multiset : option (nat * string) := None.

Lemma perm_contents: forall al bl : list nat,
    Permutation al bl -> contents al = contents bl.
Proof.
  intros.
  induction H.
  { reflexivity. }
  { simpl.
    rewrite IHPermutation.
    reflexivity. }
  { simpl.
    apply union_swap. }
  { rewrite IHPermutation1.
    rewrite IHPermutation2.
    reflexivity. }
Qed.

Lemma contents_nil_inv: forall l,
    (forall x, 0 = contents l x) -> l = nil.
Proof.
  intros.
  induction l.
  { reflexivity. }
  { simpl in H.
    unfold union in H.
    unfold singleton in H.
    specialize H with (x := a).
    bdestruct (a =? a).
    { discriminate. }
    { contradiction. } }
Qed.

Lemma contents_cons_inv: forall l x n,
    S n = contents l x ->
    exists l1 l2, l = l1 ++ x :: l2 /\ contents (l1 ++ l2) x = n.
Proof.
  induction l.
  { intros.
    discriminate. }
  { intros.
    simpl in H.
    unfold union, singleton in H.
    bdestruct (x =? a).
    { subst.
      exists [], l.
      simpl.
      simpl in H.
      inv H.
      auto. }
    { simpl in H.
      apply IHl in H.
      destruct H.
      destruct H.
      destruct H.
      subst.
      exists (a :: x0), x1.
      simpl.
      unfold union, singleton.
      bdestruct (x =? a); try contradiction.
      simpl.
      auto. } }
Qed.

Lemma contents_insert_other: forall l1 l2 x y,
    y <> x -> contents (l1 ++ x :: l2) y = contents (l1 ++ l2) y.
Proof.
  intros.
  induction l1.
  { simpl.
    unfold union, singleton.
    bdestruct (y =? x); try contradiction.
    auto. }
  { induction l2.
    { simpl.
      unfold union, singleton.
      bdestruct (y =? a).
      { simpl.
        rewrite IHl1.
        reflexivity. }
      { simpl.
        rewrite IHl1.
        reflexivity. } }
    { simpl.
      simpl in IHl2.
      unfold union, singleton.
      unfold union, singleton in IHl2.
      bdestruct (y =? a).
      { simpl.
        subst.
        rewrite IHl1.
        reflexivity. }
      { simpl.
        rewrite IHl1.
        reflexivity. } } }
Qed.

Lemma contents_perm: forall al bl,
    contents al = contents bl -> Permutation al bl.
Proof.
  intros al bl H0.
  assert (H: forall x, contents al x = contents bl x).
  { rewrite H0. auto. }
  clear H0.
  generalize dependent bl.
  induction al.
  { induction bl.
    { intros.
      auto. }
    { intros.
      specialize (H a).
      simpl in H.
      unfold union in H.
      unfold singleton in H.
      bdestruct (a =? a); try contradiction.
      unfold empty in H.
      discriminate. } }
  { intros.
    pose proof (H a).
    simpl in H0.
    unfold union,singleton in H0.
    bdestruct (a =? a); try contradiction.
    apply contents_cons_inv in H0.
    destruct H0.
    destruct H0.
    destruct H0.
    inv H2.
    apply Permutation_cons_app.
    apply IHal.
    intros.
    specialize (H x1).
    simpl in H.
    unfold union,singleton in H.
    bdestruct (x1 =? a).
    { simpl in H.
      apply contents_cons_inv in H.
      destruct H.
      destruct H.
      destruct H.
      subst.
      auto. }
    { simpl in H.
      apply contents_insert_other with (l1 := x) (l2 := x0) in H0.
      rewrite H0 in H.
      assumption. } }
Qed.

Theorem same_contents_iff_perm: forall al bl,
    contents al = contents bl <-> Permutation al bl.
Proof.
  intros.
  split.
  - apply contents_perm.
  - apply perm_contents.
Qed.

Theorem sort_specification_equivalent: forall sort,
    is_a_sorting_algorithm sort <-> is_a_sorting_algorithm' sort.
Proof.
  unfold is_a_sorting_algorithm.
  unfold is_a_sorting_algorithm'.
  split;
    intros;
    specialize (H al);
    destruct H;
    split;
    try assumption;
    apply same_contents_iff_perm;
    assumption.
Qed.

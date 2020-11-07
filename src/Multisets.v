From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Strings.String.

Export ListNotations.

Require Import Perm.
Require Import Sort.

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
  omega.
Qed.

Lemma union_comm: forall a b : multiset,
    union a b = union b a.
Proof.
  intros.
  extensionality x.
  unfold union.
  omega.
Qed.

Lemma union_swap: forall a b c : multiset,
    union a (union b c) = union b (union a c).
Proof.
  intros.
  replace (union b (union a c)) with (union (union b a) c).
  replace (union b a) with (union a b).
  replace (union (union a b) c) with (union a (union b c)).
  reflexivity.

  apply union_assoc.
  apply union_comm.
  symmetry.
  apply union_assoc.
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

Definition is_a_sorting_algorithm' (f: list nat -> list nat) := forall al,
    contents al = contents (f al) /\ sorted (f al).

Lemma insert_contents: forall x l,
    contents (insert x l) = contents (x :: l).
Proof.
  intros.
  induction l; try reflexivity.
  simpl.
  bdestruct (x <=? a); try reflexivity.
  simpl.
  rewrite IHl.
  simpl.
  apply union_swap.
Qed.

Lemma sort_contents: forall l,
    contents l = contents (sort l).
Proof.
  intros.
  induction l; try reflexivity.
  simpl.
  rewrite insert_contents.
  rewrite IHl.
  reflexivity.
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

Definition manual_grade_for_permutations_vs_multiset: option (nat * string) := None.

Print Permutation.

Lemma contents_cons: forall l l' x,
    contents l = contents l' -> contents (x :: l) = contents (x :: l').
Proof.
  intros.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Lemma perm_contents: forall al bl : list nat,
    Permutation al bl -> contents al = contents bl.
Proof.
  intros.
  induction H.
  { reflexivity. }
  { induction l.
    { apply Permutation_nil in H.
      subst.
      reflexivity. }
    { induction l'.
      { apply Permutation_sym in H.
        apply Permutation_nil in H.
        rewrite H.
        reflexivity. }
      { apply contents_cons.
        assumption. } } }
  { induction l; simpl; apply union_swap. }
  { simpl.
    rewrite IHPermutation2 in IHPermutation1.
    assumption. }
Qed.

Lemma contents_cons_x: forall l x n,
    n = contents (x :: l) x -> n > 0.
Proof.
  intros.
  simpl in H.
  unfold union in H.
  unfold singleton in H.
  bdestruct (x =? x); omega.
Qed.

Lemma contens_nil_inv: forall l,
    (forall x, 0 = contents l x) -> l = nil.
Proof.
  intros.
  induction l.
  { reflexivity. }
  { apply contents_cons_x in H.
    omega. }
Qed.

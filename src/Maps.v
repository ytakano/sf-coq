From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Theorem eqb_string_refl : forall s : string,
    true = eqb_string s s.
Proof.
  intros s.
  unfold eqb_string.
  destruct (string_dec s s) as [|Hs].
  { reflexivity. }
  { destruct Hs.
    reflexivity. }
Qed.

Theorem eqb_string_true_iff : forall x y : string,
    eqb_string x y = true <-> x = y.
Proof.
  intros x y.
  unfold eqb_string.
  destruct (string_dec x y).
  { constructor.
    { intros.
      assumption. }
    { intros.
      reflexivity. } }
  { constructor.
    { intros.
      discriminate. }
    { intros.
      contradiction. } }
Qed.

Theorem eqb_string_false_iff : forall x y : string,
    eqb_string x y = false <-> x <> y.
Proof.
  intros x y.
  unfold eqb_string.
  destruct (string_dec x y).
  { constructor.
    { intros.
      discriminate. }
    { intros.
      contradiction. } }
  { constructor.
    { intros.
      assumption. }
    { intros.
      reflexivity. } }
Qed.

Theorem false_eqb_string : forall x y : string,
    x <> y -> eqb_string x y = false.
Proof.
  intros x y H .
  unfold eqb_string.
  destruct (string_dec x y).
  { contradiction. }
  { reflexivity. }
Qed.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A := (fun _ => v).

Definition t_update {A : Type} (m : total_map A) (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v) (at level 100, right associativity).

Example example_empty := (_ !-> false).

Notation "x '!->' v ';' m" := (t_update m x v)
                                (at level 100, v at next level, right associativity).

Definition examplemap' :=
  (
    "bar" !-> true;
  "foor" !-> true;
  _ !-> false
  ).

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof.
  intros A x v.
  compute.
  reflexivity.
Qed.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 -> (x1 !-> v ; m) x2 = m x2.
Proof.
  intros A m x1 x2 v H.
  unfold t_update.
  unfold eqb_string.
  destruct (string_dec x1 x2).
  { contradiction. }
  { reflexivity. }
Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros.
  extensionality x'.
  unfold t_update.
  unfold eqb_string.
  destruct (string_dec x x').
  { reflexivity. }
  { reflexivity. }
Qed.

Lemma eqb_stringP : forall x y : string,
    reflect (x = y) (eqb_string x y).
Proof.
  intros.
  unfold eqb_string.
  destruct (string_dec x y).
  { constructor.
    assumption. }
  { constructor.
    assumption. }
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  intros.
  unfold t_update.
  extensionality x'.
  unfold eqb_string.
  destruct (string_dec x x').
  { rewrite e.
    reflexivity. }
  { reflexivity. }
Qed.

Theorem t_update_permute : forall (A : Type) (m : total_map A) v1 v2 x1 x2,
    x2 <> x1 -> (x1 !-> v1 ; x2 !-> v2 ; m) = (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros.
  unfold t_update.
  extensionality x'.
  unfold eqb_string.
  destruct (string_dec x1 x').
  { destruct (string_dec x2 x').
    { rewrite e in H.
      rewrite e0 in H.
      contradiction. }
    { reflexivity. } }
  { destruct (string_dec x2 x').
    { reflexivity. }
    { reflexivity. } }
Qed.

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A := t_empty None.

Definition update {A : Type} (m : partial_map A) (x : string) (v : A) :=
  (x !-> Some v ; m).

Notation "x '|->' v ';' m" := (update m x v)
                                (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v) (at level 100).

Example examplemap := ("Church" |-> true ; "Turing" |-> false).

Lemma apply_empty : forall (A : Type) (x : string),
    @empty A x = None.
Proof.
  intros.
  compute.
  reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
    (x |-> v ; m) x = Some v.
Proof.
  intros.
  unfold update.
  unfold t_update.
  unfold eqb_string.
  destruct (string_dec x x).
  { reflexivity. }
  { contradiction. }
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
    x2 <> x1 -> (x2 |-> v ; m) x1 = m x1.
Proof.
  intros.
  unfold update.
  unfold t_update.
  unfold eqb_string.
  destruct (string_dec x2 x1).
  { rewrite e in H.
    contradiction. }
  { reflexivity. }
Qed.

Theorem update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
    (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros.
  unfold update.
  unfold t_update.
  extensionality x'.
  unfold eqb_string.
  destruct (string_dec x x'); reflexivity.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A) x1 x2 v1 v2,
    x2 <> x1 -> (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros.
  unfold update.
  unfold t_update.
  extensionality x'.
  unfold eqb_string.
  destruct (string_dec x1 x').
  { destruct (string_dec x2 x').
    { rewrite e in H.
      rewrite e0 in H.
      contradiction. }
    { reflexivity. } }
  { reflexivity. }
Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  intros.
  unfold t_update.
  unfold eqb_string.
  destruct string_dec.
  { reflexivity. }
  { contradiction. }
Qed.

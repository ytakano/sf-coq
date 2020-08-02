Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

Require Export Maps.

Module AExp.
  Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

  Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

  Fixpoint aeval (a : aexp) : nat :=
    match a with
    | ANum n => n
    | APlus a1 a2 => (aeval a1) + (aeval a2)
    | AMinus a1 a2 => (aeval a1) - (aeval a2)
    | AMult a1 a2 => (aeval a1) * (aeval a2)
    end.

  Example test_aeavl1 : aeval (APlus (ANum 2) (ANum 2)) = 4.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Fixpoint beval (b : bexp) : bool :=
    match b with
    | BTrue => true
    | BFalse => false
    | BEq a1 a2 => (aeval a1) =? (aeval a2)
    | BLe a1 a2 => (aeval a1) <=? (aeval a2)
    | BNot b1 => negb (beval b1)
    | BAnd b1 b2 => andb (beval b1) (beval b2)
    end.

  Fixpoint optimize_0plus (a : aexp) : aexp :=
    match a with
    | ANum n => ANum n
    | APlus (ANum 0) e2 => optimize_0plus e2
    | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
    | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
    | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
    end.

  Example test_optimize_0plus :
    optimize_0plus (APlus (ANum 2)
                          (APlus (ANum 0)
                                 (APlus (ANum 0) (ANum 1))))
    = APlus (ANum 2) (ANum 1).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Theorem optimize_0plus_sound : forall a,
      aeval (optimize_0plus a) = aeval a.
  Proof.
    intros.
    induction a.
    { simpl.
      reflexivity. }
    { destruct a1.
      { destruct a2.
        { simpl.
          destruct n.
          { simpl.
            reflexivity. }
          { simpl.
            reflexivity. } }
        { destruct n.
          { simpl.
            inversion IHa2.
            reflexivity. }
          { simpl.
            inversion IHa2.
            reflexivity. } }
        { destruct n.
          { inversion IHa2.
            simpl.
            assumption. }
          { simpl.
            inversion IHa2.
            reflexivity. } }
        { destruct n.
          { simpl.
            inversion IHa2.
            reflexivity. }
          { simpl.
            inversion IHa2.
            reflexivity. } } }
      { simpl.
        inversion IHa1.
        rewrite IHa2.
        reflexivity. }
      { simpl.
        inversion IHa1.
        rewrite IHa2.
        reflexivity. }
      { simpl.
        inversion IHa1.
        rewrite IHa2.
        reflexivity. } }
    { simpl.
      inversion IHa1.
      inversion IHa2.
      reflexivity. }
    { simpl.
      inversion IHa1.
      inversion IHa2.
      reflexivity. }
  Qed.

  Theorem optimize_0plus_sound' : forall a,
      aeval (optimize_0plus a) = aeval a.
  Proof.
    intros.
    induction a;
      try (simpl; inversion IHa1; rewrite IHa2; reflexivity).
    { simpl.
      reflexivity. }
    { destruct a1;
        try (simpl; inversion IHa1; rewrite IHa2; reflexivity).
      destruct a2;
        (destruct n;
         simpl;
         inversion IHa2;
         reflexivity). }
  Qed.

  Theorem In10 : In 10 [1; 2; 3; 4; 5; 6; 7; 8; 9; 10].
  Proof.
    repeat (try (left; reflexivity); right).
  Qed.

  Theorem In10' : In 10 [1; 2; 3; 4; 5; 6; 7; 8; 9; 10].
  Proof.
    repeat (left; reflexivity).
    repeat (right; try (left; reflexivity)).
  Qed.

  Fixpoint optimize_0plus_b (b : bexp) : bexp :=
    match b with
    | BTrue => BTrue
    | BFalse => BFalse
    | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
    | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
    | BNot b1 => BNot b1
    | BAnd b1 b2 => BAnd b1 b2
    end.

  Theorem optimize_0plus_b_sound : forall b,
      beval (optimize_0plus_b b) = beval b.
  Proof.
    intros.
    induction b;
      try (simpl; reflexivity).
    { induction a1;
        (induction a2;
         try (simpl;
               reflexivity);
         try (unfold optimize_0plus_b;
               unfold beval;
               repeat (rewrite optimize_0plus_sound);
               reflexivity));
        (unfold optimize_0plus_b;
         unfold beval;
         repeat (rewrite optimize_0plus_sound);
         reflexivity). }
    { unfold optimize_0plus_b.
      unfold beval.
      repeat (rewrite optimize_0plus_sound).
      reflexivity. }
  Qed.

  Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

  Example silliy_presburger_example : forall m n o p,
      m + n <= n + o /\ o + 3 = p + 3 -> m <= p.
  Proof.
    intros.
    omega.
  Qed.

  Reserved Notation "e '\\' n" (at level 90, left associativity).

  Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) \\ n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)
  where "e '\\' n" := (aevalR e n) : type_scope.

  Reserved Notation "e '\\@' n" (at level 90, left associativity).

  Inductive bevalR : bexp -> bool -> Prop :=
  | E_BTrue (n : bool) :
      BTrue \\@ true
  | E_BFalse (n : bool) :
      BFalse \\@ false
  | E_BEq (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (BEq e1 e2) \\@ n1 =? n2
  | E_BLe (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (BLe e1 e2) \\@ n1 <=? n2
  | E_BNot (e : bexp) (n : bool) :
      (e \\@ n) -> (BNot e) \\@ (negb n)
  | E_BAnd (e1 e2 : bexp) (n1 n2 : bool) :
      (e1 \\@ n1) -> (e2 \\@ n2) -> (BAnd e1 e2) \\@ (andb n1 n2)
  where "e '\\@' n" := (bevalR e n) : type_scope.

  Definition manual_grade_for_beval_rules : option (nat * string) := None.

  Theorem aeval_iff_aevalR : forall a n,
      (a \\ n) <-> aeval a = n.
  Proof.
    split.
    { intros.
      induction H;
        try (simpl;
             reflexivity);
        try (simpl;
             rewrite IHaevalR1;
             rewrite IHaevalR2;
             reflexivity). }
    { generalize dependent n.
      induction a;
        try (simpl; intros; subst);
        try (constructor;
             try (apply IHa1; reflexivity);
             try (apply IHa2; reflexivity)). }
  Qed.

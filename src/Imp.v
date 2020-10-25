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

  Reserved Notation "e '==>' n" (at level 90, left associativity).

  Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (APlus e1 e2) ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (AMult e1 e2) ==> (n1 * n2)
  where "e '==>' n" := (aevalR e n) : type_scope.

  Reserved Notation "e '==>b' b" (at level 90, left associativity).

  Inductive bevalR : bexp -> bool -> Prop :=
  | E_BTrue (n : bool) :
      BTrue ==>b true
  | E_BFalse (n : bool) :
      BFalse ==>b false
  | E_BEq (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (BEq e1 e2) ==>b n1 =? n2
  | E_BLe (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (BLe e1 e2) ==>b n1 <=? n2
  | E_BNot (e : bexp) (n : bool) :
      (e ==>b n) -> (BNot e) ==>b (negb n)
  | E_BAnd (e1 e2 : bexp) (n1 n2 : bool) :
      (e1 ==>b n1) -> (e2 ==>b n2) -> (BAnd e1 e2) ==>b (andb n1 n2)
  where "e '==>b' b" := (bevalR e b) : type_scope.

  Definition manual_grade_for_beval_rules : option (nat * string) := None.

  Theorem aeval_iff_aevalR : forall a n,
      (a ==> n) <-> aeval a = n.
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

  Theorem aeval_iff_aevalR' : forall a n,
      (a ==> n) <-> aeval a = n.
  Proof.
    split.
    { intros H; induction H; subst; reflexivity. }
    { generalize dependent n.
      induction a; simpl; intros; subst; constructor;
        try apply IHa1; try apply IHa2; reflexivity. }
  Qed.

  Lemma beval_bnot_n : forall b,
      beval (BNot b) = negb (beval b).
  Proof.
    intros.
    destruct b; simpl; reflexivity.
  Qed.

  Lemma beval_iff_bevalR : forall b bv,
      b ==>b bv <-> beval b = bv.
  Proof.
    split.
    { intros.
      induction H; simpl; try reflexivity;
        try (apply aeval_iff_aevalR in H;
             apply aeval_iff_aevalR in H0);
        try (subst;
             reflexivity). }
    { intros.
      subst bv.
      induction b;
        try (constructor;
             constructor);
        try (simpl;
             constructor;
             apply aeval_iff_aevalR;
             reflexivity);
        try (simpl;
             constructor;
             repeat assumption). }
  Qed.

End AExp.

Definition state := total_map nat.

Inductive aexp : Type :=
| ANum (n : nat)
| AId (x : string)
| APlus (a1 a2 : aexp)
| AMinus (a1 a2 : aexp)
| AMult (a1 a2 : aexp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
| BTrue
| BFalse
| BEq (a1 a2 : aexp)
| BLe (a1 a2 : aexp)
| BNot (b : bexp)
| BAnd (b1 b2 : bexp).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                         (in custom com at level 0, only parsing,
                             f constr at level 0, x constr at level 9,
                             y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x = y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

Definition example_aexp : aexp := <{ 3 + (X * 2) }>.
Definition example_bexp : bexp := <{ true && ~(X <= 4) }>.

Print example_aexp.
Print example_bexp.

Set Printing Coercions.
Print example_bexp.
Unset Printing Coercions.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{~ b1}> => negb (beval st b1)
  | <{b1 && b2}> => andb (beval st b1) (beval st b2)
  end.

Definition empty_st := (_ !-> 0).

Notation "x '!->' v" := (t_update empty_st x v) (at level 100).

Example aexp1 : aeval (X !-> 5) <{ (3 + (X * 2))}> = 13.
Proof. reflexivity. Qed.

Example bexp1 : beval (X !-> 5) <{ true && ~(X <= 4)}> = true.
Proof. reflexivity. Qed.

Inductive com : Type :=
| CSkip
| CAss (x : string) (a : aexp)
| CSeq (c1 c2 : com)
| CIf (b : bexp) (c1 c2 : com)
| CWhile (b : bexp) (c : com).

Notation "'skip'" := CSkip (in custom com at level 0) : com_scope.
Notation "x := y" := (CAss x y)
                       (in custom com at level 0, x constr at level 0,
                           y at level 85, no associativity) : com_scope.
Notation "x ; y" := (CSeq x y)
                      (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
  (CIf x y z)
    (in custom com at level 89, x at level 99,
        y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
  (CWhile x y)
    (in custom com at level 89, x at level 99, y at level 99) : com_scope.

Definition fact_in_coq : com :=
  <{ Z := X;
     Y := 1;
     while ~(Z = 0) do
       Y := Y * Z;
       Z := Z - 1
     end }>.

Print fact_in_coq.

Unset Printing Notations.
Print fact_in_coq.
Set Printing Notations.

Set Printing Coercions.
Print fact_in_coq.
Unset Printing Coercions.

Locate "&&".
Locate ";".
Locate "while".
Locate aexp.

Definition plus2 : com :=
  <{ X := X + 2 }>.

Definition XtimesYinZ : com :=
  <{ Z := X * Y }>.

Definition subtract_slowly_body : com :=
  <{ Z := Z - 1 ;
     X := X - 1}>.

Definition subtract_slowly : com :=
  <{ while ~(X = 0) do
       subtract_slowly_body
     end }>.

Definition subtract_3_from_5_slowly : com :=
  <{ X := 3 ;
     Z := 5 ;
     subtract_slowly }>.

Definition loop : com :=
  <{ while true do
       skip
     end }>.

Reserved Notation "st '=[' c ']=>' st'" (at level 40, c custom com at level 99,
                                         st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
| E_Skip : forall st,
    st =[ skip ]=> st
| E_Ass : forall st a n x,
    aeval st a = n ->
    st =[ x := a ]=> (x !-> n; st)
| E_Seq : forall c1 c2 st st' st'',
    st =[ c1 ]=> st' ->
    st' =[ c2 ]=> st'' ->
    st =[ c1 ; c2 ]=> st''
| E_IfTrue : forall st st' b c1 c2,
    beval st b = true ->
    st =[ c1 ]=> st' ->
    st =[ if b then c1 else c2 end]=> st'
| E_IfFalse : forall st st' b c1 c2,
    beval st b = false ->
    st =[ c2 ]=> st' ->
    st =[ if b then c1 else c2 end]=> st'
| E_WhileFalse : forall b st c,
    st =[ while b do c end]=> st
| E_WhileTrue : forall st st' st'' b c,
    beval st b = true ->
    st =[ c ]=> st' ->
    st' =[ while b do c end]=> st'' ->
    st =[ while b do c end]=> st''
where "st =[ c ]=> st'" := (ceval c st st').

Example ceval_example1:
  empty_st =[
    X := 2;
    if (X <= 1)
      then Y := 3
      else Z := 4
    end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  apply E_Seq with (X !-> 2).
  { constructor.
    reflexivity. }
  { apply E_IfFalse.
    reflexivity.
    apply E_Ass.
    reflexivity. }
Qed.

Example ceval_example2:
  empty_st =[
    X := 0;
    Y := 1;
    Z := 2
  ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
  apply E_Seq with (X !-> 0).
  { constructor.
    reflexivity. }
  { apply E_Seq with (Y !-> 1 ; X !-> 0).
    { constructor.
      reflexivity. }
    { constructor.
      reflexivity. }}
Qed.

Definition pup_to_n : com :=
  <{ Y := 0;
     while ~(X = 0) do
       Y := Y + X;
       X := X - 1
     end}>.

Theorem pup_to_n_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
Proof.
  apply E_Seq with (Y !-> 0 ; X !-> 2).
  { constructor.
    reflexivity. }
  { apply E_WhileTrue with (X !-> 1; Y !-> 2; Y !-> 0; X !-> 2).
    { reflexivity. }
    { apply E_Seq with (Y !-> 2; Y !-> 0; X !-> 2).
      { constructor.
        reflexivity. }
      { apply E_Ass.
        reflexivity. } }
    { apply E_WhileTrue with (X !-> 0; Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2).
      { constructor. }
      { apply E_Seq with (Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2).
        { constructor.
          compute.
          reflexivity. }
        { constructor.
          reflexivity. } }
      { constructor. } } }
Qed.

Theorem ceval_deterministic: forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  induction c.
  { intros.
    inversion H.
    inversion H0.
    subst st1 st2.
    reflexivity. }
  { intros.
    inversion H.
    inversion H0.
    subst n0.
    subst n.
    reflexivity. }
  { intros.
    inversion H.
    inversion H0.
    apply IHc1 with (st:=st) (st1:=st') (st2:=st'0) in H3.
    { subst st'0.
      apply IHc2 with (st:=st') (st1:=st1) (st2:=st2) in H6.
      { assumption. }
      { assumption. } }
    { assumption. } }
  { admit. }
  { admit. }
Admitted.

Theorem plus2_spec : forall st n st',
    st X = n -> st =[ plus2 ]=> st' -> st' X = n + 2.
Proof.
  intros.
  inversion H0.
  subst.
  clear H0.
  simpl.
  apply t_update_eq.
Qed.

Theorem loop_never_stops : forall st st',
    ~(st =[ loop ]=> st').
Proof.
  intros st st' contra.
  unfold loop in contra.
  remember <{ while true do skip end }> as loopdef eqn:Heqloopdef.
  induction contra; try discriminate.
  {
    admit.
  }
  { apply IHcontra2.
    assumption. }
Admitted.

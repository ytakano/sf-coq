Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Eval simpl in (next_weekday friday).
Eval simpl in (next_weekday (next_weekday saturday)).

Example test_next_weekday :
  (next_weekday (next_weekday saturday)) = tuesday.

Proof.
  simpl.
  reflexivity.
Qed.

Inductive bool : Type :=
| true : bool
| false : bool.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => negb b2
  | false => b2
  end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => match b2 with
            | true => b3
            | false => false
            end
  | false => false
  end.


Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check (negb true).
Check negb.

Module Playground1.
  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.
End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Check (S (S (S (S O)))).
Eval simpl in (minustwo 4).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. reflexivity. Qed.

Module Playground2.
  Fixpoint plus (n:nat) (m:nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

  Eval simpl in (plus (S (S (S O))) (S (S O))).

  Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.

  Fixpoint minus (n m : nat) : nat :=
    match n, m with
    | O , _ => O
    | S _, O => n
    | S n', S m' => minus n' m'
    end.
End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => S O
  | S n' => mult (S n') (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
            | O => false
            | S m' => ble_nat n' m'
            end
  end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool :=
  negb (ble_nat m n).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. compute. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. compute. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. compute. reflexivity. Qed.

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

Check ((0 + 1) + 1).

Theorem plus_O_n : forall n:nat, 0 + n = n.
Proof.
  reflexivity.
Qed.

Eval simpl in (forall n:nat, n + 0 = n).
Eval simpl in (forall n:nat, 0 + n = n).

Theorem plus_O_n'' : forall n:nat, 0 + n = n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem plus_1_r : forall n:nat, n + 1 = S n.
Proof.
  intros n.
  induction n.
  { reflexivity. }
  { simpl.
    rewrite -> IHn.
    reflexivity. }
Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem plus_id_example : forall n m:nat,
    n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite <- H.
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
    (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
Qed.

Theorem mult_1_plus : forall n m : nat,
    (1 + n) * m = m + (n * m).
Proof.
  intros n m.
  rewrite -> plus_1_l.
  simpl.
  reflexivity.
Qed.

Theorem plus_1_neq_0 : forall n : nat,
    beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [| n'].
  reflexivity.
  reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  reflexivity.
  reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
    beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n.
  { reflexivity. }
  { reflexivity. }
Qed.

Theorem andb_true_elim1 : forall b c : bool,
    andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  { reflexivity. }
  { rewrite <- H.
    reflexivity. }
Qed.

Theorem andb_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  { reflexivity. }
  { rewrite <- H.
    destruct b.
    { reflexivity. }
    { reflexivity. }
    }
Qed.

Theorem plus_0_r_firsttry : forall n:nat,
    n + 0 = n.
Proof.
  intros n.
  induction n as [| n'].
  { reflexivity. }
  { simpl.
    rewrite -> IHn'.
    reflexivity. }
Qed.

Theorem minus_diag : forall n,
    minus n n = 0.
Proof.
  intros n.
  induction n as [| n'].
  { simpl.
    reflexivity. }
  { simpl.
    rewrite -> IHn'.
    reflexivity. }
Qed.

Theorem mult_0_r : forall n:nat,
    n * 0 = 0.
Proof.
  intros n.
  induction n as [| n'].
  { simpl.
    reflexivity. }
  { simpl.
    rewrite -> IHn'.
    reflexivity. }
Qed.

Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n.
  { simpl.
    reflexivity. }
  { simpl.
    rewrite -> IHn.
    reflexivity. }
Qed.

Theorem plus_comm : forall n m : nat,
    n + m = m + n.
Proof.
  intros n m.
  induction n.
  { simpl.
    induction m.
    { reflexivity. }
    { simpl.
      rewrite <- IHm.
      reflexivity. } }
  { simpl.
    induction m.
    { simpl.
      rewrite -> IHn.
      simpl.
      reflexivity. }
    { rewrite -> IHn.
      simpl.
      rewrite -> plus_n_Sm.
      reflexivity. } }
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros n.
  induction n.
  { simpl.
    reflexivity. }
  { simpl.
    rewrite -> IHn.
    rewrite -> plus_n_Sm.
    reflexivity. }
Qed.

Theorem plus_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n'].
  { reflexivity. }
  { simpl.
    rewrite -> IHn'.
    reflexivity. }
Qed.

Theorem beq_nat_refl : forall n : nat,
    true = beq_nat n n.
Proof.
  intros n.
  induction n as [| n'].
  { simpl.
    reflexivity. }
  { simpl.
    rewrite <- IHn'.
    reflexivity. }
Qed.

Theorem mult_0_plus' : forall n m : nat,
    (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
  { reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm.
    reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm.
    reflexivity. }
  rewrite -> H.
  rewrite -> plus_assoc.
  reflexivity.
Qed.

Theorem mult_Sn : forall m n : nat,
    n * S m = n + n * m.
Proof.
  intros n m.
  simpl.
  induction m.
  { simpl.
    reflexivity. }
  { simpl.
    rewrite -> IHm.
    rewrite -> plus_swap.
    reflexivity. }
Qed.
  

Theorem mult_comm : forall m n : nat,
    m * n = n * m.
Proof.
  intros m n.
  induction m.
  { simpl.
    induction n.
    { simpl.
      reflexivity. }
    { simpl.
      rewrite <- IHn.
      reflexivity. } }
  { simpl.
    induction n.
    { simpl.
      rewrite -> mult_0_r.
      reflexivity. }
    { simpl.
      rewrite -> IHm.
      rewrite -> mult_Sn.
      simpl.
      rewrite -> plus_swap.
      reflexivity. } }
Qed.

Theorem evenb_n__oddb_Sn : forall n : nat,
    evenb n = negb (evenb (S n)).
Proof.
  intros n.
  induction n.
  { simpl.
    reflexivity. }
  { simpl.
    rewrite -> IHn.
    rewrite -> negb_involutive.
    simpl.
    reflexivity. }
Qed.

Theorem ble_nat_refl : forall n:nat,
    true = ble_nat n n.
Proof.
  intros n.
  induction n.
  { simpl.
    reflexivity. }
  { simpl.
    rewrite <- IHn.
    reflexivity. }
Qed.

Theorem zero_nbeq_S : forall n:nat,
    beq_nat 0 (S n) = false.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
    andb b false = false.
Proof.
  intros b.
  destruct b.
  { simpl.
    reflexivity. }
  { simpl.
    reflexivity. }
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
    ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros n m p.
  intros.
  induction p.
  { simpl.
    rewrite -> H.
    reflexivity. }
  { simpl.
    rewrite -> IHp.
    reflexivity. }
Qed.

Theorem S_nbeq_0 : forall n:nat,
    beq_nat (S n) 0 = false.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n.
  simpl.
  rewrite -> plus_0_r_firsttry.
  reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
           (negb c)) = true.
Proof.
  intros b c.
  destruct b.
  { destruct c.
    { simpl.
      reflexivity. }
    { simpl.
      reflexivity. } }
  { destruct c.
    { simpl.
      reflexivity. }
    { simpl.
      reflexivity. } }
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
    (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction n.
  { simpl.
    reflexivity. }
  { simpl.
    rewrite -> IHn.
    rewrite -> plus_assoc.
    reflexivity. }
Qed.

Theorem mult_assoc : forall n m p : nat,
    n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n.
  { simpl.
    reflexivity. }
  { simpl.
    rewrite -> IHn.
    rewrite -> mult_plus_distr_r.
    reflexivity. }
Qed.

Theorem succ_dist : forall n m : nat, S (m + n) = m + S n.
Proof.
  intros n m.
  induction m.
  { simpl.
    reflexivity. }
  { simpl.
    rewrite -> IHm.
    reflexivity. }
Qed.

Theorem plus_reflect : forall n m : nat, m + n = n + m.
Proof.
  intros n m.
  induction n.
  { simpl.
    rewrite -> plus_0_r_firsttry.
    reflexivity. }
  { simpl.
    induction m.
    { simpl.
      rewrite -> plus_0_r_firsttry.
      reflexivity. }
    { simpl.
      rewrite <- IHn.
      simpl.
      rewrite <- succ_dist.
      reflexivity. } }
Qed.

Theorem plus_swap' : forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  replace (n + m) with (m + n).
  { reflexivity. }
  { rewrite -> plus_reflect.
    reflexivity. }
Qed.

(*
  0b1011 = (Bx1 (Bx1 (Bx0 (Bx1 B0))))

  0b1011 + 1 = 0b1100
  (Bx0 (Bx0 (Bx1 (Bx1 B0))))


  0b11 = (Bx1 (Bx1 B0))

  0b11 + 1 = 0b100
  (Bx0 (Bx0 (Bx1 B0)))
*)

Inductive bin : Type :=
| B0 : bin
| Bx0 : bin -> bin
| Bx1 : bin -> bin.

Fixpoint bin_increment (b:bin) : bin :=
  match b with
  | B0 => Bx1 B0
  | Bx0 x => Bx1 x
  | Bx1 x => Bx0 (bin_increment x)
  end.

Fixpoint bin_to_nat (b:bin) : nat :=
  match b with
  | B0 => 0
  | Bx0 x => 2 * (bin_to_nat x)
  | Bx1 x => 2 * (bin_to_nat x) + 1
  end.

Eval simpl in bin_to_nat (B0).
Eval simpl in bin_to_nat (Bx1 (Bx1 B0)).
Eval simpl in bin_to_nat (Bx0 (Bx1 B0)).
Eval simpl in bin_to_nat (Bx1 (Bx1 (Bx1 B0))).
Eval simpl in bin_to_nat (Bx0 (Bx0 (Bx1 B0))).
Eval simpl in bin_to_nat (Bx0 (Bx1 (Bx1 B0))).

Theorem bin_to_nat_comm : forall b:bin,
    bin_to_nat (bin_increment b) = S (bin_to_nat b).
Proof.
  intros n.
  induction n.
  { simpl.
    reflexivity. }
  { simpl.
    rewrite -> plus_0_r_firsttry.
    rewrite -> plus_n_Sm.
    replace (S (bin_to_nat n)) with (bin_to_nat n + 1).
    rewrite -> plus_assoc.
    reflexivity.
    { rewrite -> plus_1_r.
      reflexivity. } }
  { simpl.
    rewrite -> plus_0_r_firsttry.
    rewrite -> plus_0_r_firsttry.
    rewrite -> IHn.
    simpl.
    replace (S (bin_to_nat n)) with (bin_to_nat n + 1).
    rewrite -> plus_assoc.
    reflexivity.
    { rewrite -> plus_1_r.
      reflexivity. } }
Qed.

Fixpoint nat_to_bin (n:nat) (b:bin) : bin :=
  match n with
  | O => b
  | S n' => nat_to_bin n' (bin_increment b)
  end.

Theorem nat_to_bin_1 : forall (n:nat),
    nat_to_bin n (Bx1 B0) = nat_to_bin (S n) B0.
Proof.
  intros n.
  induction n.
  { simpl.
    reflexivity. }
  { simpl.
    reflexivity. }
Qed.

Theorem nat_to_bin_comm : forall n:nat,
    nat_to_bin n (Bx1 B0) = bin_increment (nat_to_bin n B0).
Proof.
  intros n.
  induction n.
  { simpl.
    reflexivity. }
  { simpl.
Admitted.


Theorem nat_bin_nat : forall n:nat,
    bin_to_nat (nat_to_bin n B0) = n.
Proof.
  intros n.
  induction n.
  { simpl.
    reflexivity. }
  { simpl.
    rewrite -> nat_to_bin_comm.
    rewrite -> bin_to_nat_comm.
    rewrite -> IHn.
    reflexivity. }
Qed.

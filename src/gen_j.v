Require Export poly_j.

Theorem double_injective_take2 : forall n m,
    double n = double m -> n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m'].
  { simpl.
    destruct n.
    { reflexivity. }
    { intros eq.
      inversion eq. } }
  { intros n eq.
    destruct n as [| n'].
    { inversion eq. }
    { assert (n' = m') as H.
      { apply IHm'.
        inversion eq.
        reflexivity. }
      rewrite -> H.
      reflexivity. } }
Qed.

Theorem plus_n_n_injective_take2 : forall n m,
    n + n = m + m -> n = m.
Proof.
  induction n.
  { intros m H.
    destruct m.
    { reflexivity. }
    { simpl in H.
      inversion H. } }
  { intros m H.
    destruct m.
    { inversion H. }
    { apply eq_remove_S.
      apply IHn.
      simpl in H.
      inversion H.
      replace (n + S n) with (S n + n) in H1.
      replace (m + S m) with (S m + m) in H1.
      inversion H1.
      reflexivity.
      { apply plus_comm. }
      { apply plus_comm.  } } }
Qed.

Theorem index_after_last : forall (n : nat) (X : Type) (l : list X),
    length l = n -> index (S n) l = None.
Proof.
  intros n X l H.
  generalize dependent n.
  induction l.
  { reflexivity. }
  { intros n H.
    simpl.
    simpl in H.
    rewrite <- H.
    apply IHl.
    reflexivity. }
Qed.

Theorem length_snoc''' : forall (n : nat) (X : Type) (v : X) (l : list X),
    length l = n -> length (snoc l v) = S n.
Proof.
  intros n X v l H.
  generalize dependent n.
  generalize dependent v.
  induction l.
  { intros v n H.
    simpl.
    simpl in H.
    rewrite <- H.
    reflexivity. }
  { intros v n H.
    simpl in H.
    simpl.
    rewrite <- H.
    apply eq_remove_S.
    apply IHl.
    reflexivity. }
Qed.

Theorem app_length_cons : forall (X : Type) (l1 l2 : list X) (x : X) (n : nat),
    length (l1 ++ (x :: l2)) = n -> S (length (l1 ++ l2)) = n.
Proof.
  intros X l1 l2 x n.
  generalize dependent n.
  induction l1.
  { intros n H.
    simpl in H.
    simpl.
    apply H. }
  { intros n H.
    simpl.
    simpl in H.
    rewrite <- H.
    apply eq_remove_S.
    apply IHl1.
    reflexivity. }
Qed.

Theorem app_length_cons_2 : forall (X : Type) (l1 l2 : list X) (x : X) (n : nat),
    S (length (l1 ++ l2)) = n -> length (l1 ++ (x :: l2)) = n.
Proof.
  intros X l1 l2 x n.
  generalize dependent n.
  induction l1.
  { intros n H.
    apply H. }
  { intros n H.
    simpl.
    simpl in H.
    rewrite <- H.
    apply eq_remove_S.
    apply IHl1.
    reflexivity. }
Qed.

Theorem app_length_twice : forall (X : Type) (n : nat) (l : list X),
    length l = n -> length (l ++ l) = n + n.
Proof.
  intros X n l.
  generalize dependent n.
  induction l.
  { intros n H.
    simpl.
    simpl in H.
    rewrite <- H.
    reflexivity. }
  { intros n H.
    simpl.
    simpl in H.
    rewrite <- H.
    simpl.
    apply eq_remove_S.
    apply app_length_cons_2.
    simpl.
    rewrite -> plus_comm.
    simpl.
    apply eq_remove_S.
    apply IHl.
    reflexivity. }
Qed.

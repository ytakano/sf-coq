Require Export prop_j.

Definition funny_prop1 := forall n, forall (E : ev n), ev (n + 4).

Definition funny_prop1' := forall n, forall (_ : ev n), ev (n + 4).

Definition funny_prop1'' := forall n, ev n -> ev (n + 4).

Check conj.

Theorem and_example : (ev 0) /\ (ev 4).
Proof.
  apply conj.
  apply ev_0.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Print and_example.

Theorem and_example' : (ev 0) /\ (ev 4).
Proof.
  split.
  apply ev_0.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Theorem proj1 : forall P Q : Prop,
    P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HP.
Qed.

Theorem proj2 : forall P Q : Prop,
    P /\ Q -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HQ.
Qed.

Theorem and_commut : forall P Q : Prop,
    P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  split.
  { apply HQ. }
  { apply HP. }
Qed.

Print and_commut.

Theorem and_assoc : forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split.
  { split.
    { apply HP. }
    { apply HQ. } }
  { apply HR. }
Qed.

Theorem even_ev : forall n : nat,
    (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  intros n.
  induction n.
  { split.
    { intros.
      apply ev_0. }
    { intros.
      inversion H. } }
  { inversion IHn.
    split.
    { apply H0. }
    { intros.
      inversion H1.
      fold (even n) in H3.
      apply H in H3.
      apply ev_SS.
      apply H3. } }
Qed.

Check conj.

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P : Prop) =>
    fun (Q : Prop) =>
      fun (R : Prop) =>
        fun (c1 : P /\ Q) =>
          fun (c2 : Q /\ R) =>
            match c1 with
            | conj p q =>
              match c2 with
              | conj q' r =>
                conj p r
              end
            end.

Theorem iff_implies : forall P Q : Prop,
    (P <-> Q) -> P -> Q.
Proof.
  intros P Q H.
  inversion H.
  apply H0.
Qed.

Theorem iff_sym : forall P Q : Prop,
    (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q H.
  inversion H.
  split.
  { apply H1. }
  { apply H0. }
Qed.

Theorem iff_refl : forall P : Prop,
    P <-> P.
Proof.
  intros P.
  split.
  { intros.
    apply H. }
  { intros.
    apply H. }
Qed.

Theorem iff_trans : forall P Q R : Prop,
    (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R H1 H2.
  inversion H1.
  inversion H2.
  split.
  { intros.
    apply H in H5.
    apply H3 in H5.
    apply H5. }
  { intros.
    apply H4 in H5.
    apply H0 in H5.
    apply H5. }
Qed.

Theorem MyProp_iff_ev : forall n, MyProp n <-> ev n.
Proof.
  intros n.
  split.
  { intros.
    apply ev_MyProp'.
    apply H. }
  { intros.
    apply MyProp_ev.
    apply H. }
Qed.

Print MyProp_iff_ev.

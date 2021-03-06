Require Export prop_j.
Require Export gen_j.

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

Definition MyProp_iff_ev : forall n, MyProp n <-> ev n :=
  fun n =>
    conj (fun H : (MyProp n) => ev_MyProp' n H)
         (fun H : (ev n) => MyProp_ev n H).

Theorem or_commut : forall P Q : Prop,
    P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
  { apply or_intror.
    apply HP. }
  { apply or_introl.
    apply HQ. }
Qed.

Theorem or_commut' : forall P Q : Prop,
    P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
  { right.
    assumption. }
  { left.
    assumption. }
Qed.

Definition or_commut'' : forall (P Q : Prop), P \/ Q -> Q \/ P :=
  fun (P : Prop) =>
    fun (Q : Prop) =>
      fun (H : P \/ Q) =>
        match H with
        | or_introl p => or_intror p
        | or_intror q => or_introl q
        end.

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
    P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R H.
  inversion H as [HP | [HQ HR]].
  { split.
    { left.
      assumption. }
    { left.
      assumption. } }
  { split.
    { right.
      assumption. }
    { right.
      assumption. } }
Qed.

Theorem or_distributes_over_and_2 : forall P Q R : Prop,
    (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R H.
  inversion H.
  inversion H0.
  { left.
    assumption. }
  { inversion H1.
    { left.
      assumption. }
    { right.
      apply conj.
      { assumption. }
      { assumption. } } }
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  { apply or_distributes_over_and_1. }
  { apply or_distributes_over_and_2. }
Qed.

Theorem andb_true__and : forall b c,
    andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  split.
  { destruct b.
    { reflexivity. }
    { inversion H. } }
  { destruct c.
    { reflexivity. }
    { destruct b.
      { inversion H. }
      { inversion H. } } }
Qed.

Theorem and__andb_false : forall b c,
    b = true /\ c = true -> andb b c = true.
Proof.
  intros b c H.
  inversion H.
  rewrite H0.
  rewrite H1.
  reflexivity.
Qed.

Theorem andb_false : forall b c,
    andb b c = false -> b = false \/ c = false.
Proof.
  intros b c H.
  destruct b.
  { inversion H.
    destruct c.
    { inversion H. }
    { simpl in H.
      right.
      assumption. } }
  { simpl in H.
    left.
    assumption. }
Qed.

Theorem orb_true : forall b c,
    orb b c = true -> b = true \/ c = true.
Proof.
  intros b c H.
  destruct b.
  { simpl in H.
    left.
    assumption. }
  { simpl in H.
    right.
    assumption. }
Qed.

Theorem orb_false : forall b c,
    orb b c = false -> b = false /\ c = false.
Proof.
  intros b c H.
  split.
  { destruct b.
    { simpl in H.
      discriminate. }
    { reflexivity. } }
  { destruct b.
    { simpl in H.
      discriminate. }
    { simpl in H.
      assumption.  } }
Qed.

Theorem False_implies_nonsenc : False -> 2 + 2 = 5.
Proof.
  intros.
  inversion H.
Qed.

Theorem nonsense_implies_False : 2 + 2 = 5 -> False.
Proof.
  intros.
  discriminate.
Qed.

Theorem ex_falso_quodlibet : forall (P : Prop),
    False -> P.
Proof.
  intros P contra.
  inversion contra.
Qed.

Print True.

Check True_ind.

Print not.

Theorem not_false : ~False.
Proof.
  unfold not.
  intros.
  inversion H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
    (P /\ ~P) -> Q.
Proof.
  intros P Q H.
  inversion H.
  unfold not in H1.
  apply H1 in H0.
  inversion H0.
Qed.

Theorem double_neg : forall P : Prop,
    P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros.
  apply H0 in H.
  inversion H.
Qed.

Theorem contrapositive : forall P Q : Prop,
    (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H1 H2.
  unfold not.
  unfold not in H2.
  intros HN.
  apply H1 in HN.
  apply H2 in HN.
  inversion HN.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
    ~ (P /\ ~P).
Proof.
  intros P.
  unfold not.
  intros H.
  inversion H.
  apply H1 in H0.
  inversion H0.
Qed.

Theorem five_not_even :
  ~ ev 5.
Proof.
  unfold not.
  intros.
  inversion H.
  inversion H1.
  inversion H3.
Qed.

Theorem ev_not_ev_S : forall n,
    ev n -> ~ ev (S n).
Proof.
  unfold not.
  intros n H.
  induction H.
  { intros.
    inversion H. }
  { intros.
    apply SSev_even in H0.
    apply IHev in H0.
    inversion H0. }
Qed.

(*
Definition peirce := forall P Q : Prop,
    ((P -> Q) -> P) -> P.

Definition classic := forall P : Prop,
    ~~P -> P.

Definition excluded_middle := forall P : Prop,
    P \/ ~P.
 *)

Theorem not_false_then_true : forall b : bool,
    b <> false -> b = true.
Proof.
  intros b H.
  destruct b.
  { reflexivity. }
  { unfold not in H.
    apply ex_falso_quodlibet.
    apply H.
    reflexivity. }
Qed.

Theorem not_eq_beq_false : forall n n' : nat,
    n <> n' -> beq_nat n n' = false.
Proof.
  induction n.
  { intros n' H.
    destruct n'.
    { unfold not in H.
      apply ex_falso_quodlibet.
      apply H.
      reflexivity. }
    { simpl.
      reflexivity. } }
  { intros n' H.
    induction n'.
    { reflexivity. }
    { simpl.
      apply IHn.
      unfold not.
      intros.
      unfold not in H.
      rewrite <- H0 in H.
      apply H.
      reflexivity. } }
Qed.

Theorem beq_false_not_eq : forall n m,
    false = beq_nat n m -> n <> m.
Proof.
  induction n.
  { intros m H.
    unfold not.
    intros.
    rewrite <- H0 in H.
    simpl in H.
    discriminate. }
  { intros m H.
    unfold not.
    intros.
    rewrite <- H0 in H.
    simpl in H.
    apply IHn in H.
    unfold not in H.
    apply H.
    reflexivity. }
Qed.

Print ex.

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (x := 2).
  reflexivity.
Qed.

Print exists_example_1.
Check ex_intro.
Print ex.

Example exsits_example_1' : exists n, n + (n * n) = 6.
Proof.
  exists 2.
  reflexivity.
Qed.

Theorem exists_example_2 : forall n,
    (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm].
  exists (2 + m).
  apply Hm.
Qed.

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
    (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H.
  unfold not.
  intros.
  inversion H0.
  apply H1.
  apply H.
Qed.

Definition excluded_middle := forall P : Prop,
    P \/ ~P.

Theorem not_exists_dist : excluded_middle -> forall (X : Type) (P : X -> Prop),
      ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros EX X P H x.
  unfold excluded_middle in EX.
  unfold not in H.
  assert (P x \/ ~ P x).
  { apply EX. }
  { inversion H0.
    { apply H1. }
    { apply ex_falso_quodlibet.
      apply H.
      exists x.
      unfold not in H1.
      apply H1. } }
Qed.

Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
    (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  { intros.
    inversion H.
    inversion H0.
    { left.
      exists x.
      assumption. }
    { right.
      exists x.
      assumption. } }
  { intros.
    inversion H.
    { inversion H0.
      exists x.
      left.
      assumption. }
    { inversion H0.
      exists x.
      right.
      assumption. } }
Qed.

Module MyEquality.
  Inductive eq (X : Type) : X -> X -> Prop :=
    refl_equal : forall x, eq X x x.

  Notation "x = y" := (eq _ x y) (at level 70, no associativity) : type_scope.

  Inductive eq' (X : Type) (x : X) : X -> Prop :=
    refl_equal' : eq' X x x.

  Notation "x =' y" := (eq' _ x y) (at level 70, no associativity) : type_scope.

  Theorem two_defs_of_eq_coincide : forall (X : Type) (x y : X),
      x = y <-> x =' y.
  Proof.
    intros TX x y.
    split.
    { intros.
      inversion H.
      apply refl_equal'. }
    { intros.
      inversion H.
      apply refl_equal. }
  Qed.

  Check eq'_ind.

  Definition four : 2 + 2 = 1 + 3 :=
    refl_equal nat 4.

  Definition singleton : forall (X : Set) (x : X), [] ++ [x] = x :: [] :=
    fun (X : Set) (x : X) => refl_equal (list X) [x].

  Check singleton.

End MyEquality.

Module LeFirstTry.
  Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).
End LeFirstTry.

Check le_ind.

Theorem test_le1 :
  3 <= 3.
Proof.
  apply le_n.
Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  apply le_S.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.

Theorem test_le3 :
  ~ (2 <= 1).
Proof.
  intros H.
  inversion H.
  inversion H1.
Qed.

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat (n : nat) : nat -> Prop :=
| nn : next_nat n (S n).

Inductive next_even (n : nat) : nat -> Prop :=
| ne_1 : ev (S n) -> next_even n (S n)
| ne_2 : ev (S (S n)) -> next_even n (S (S n)).


Module R.
  Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 : forall m n o, R m n o -> R (S m) n (S o)
  | c3 : forall m n o, R m n o -> R m (S n) (S o)
  | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
  | c5 : forall m n o, R m n o -> R n m o.
End R.

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
| all_nil  : all X P []
| all_cons : forall x, P x -> forall l, all X P l -> all X P (x :: l).

Check all_nil nat ev.

Print eq_refl.

Theorem all_x : forall (X : Type) (test : X -> bool) (x : X) (l : list X),
    forallb test (x :: l) = true -> test x = true.
Proof.
  intros X test x l H.
  inversion H.
  apply andb_true_elim1 in H.
  rewrite -> H.
  simpl.
  rewrite -> H in H1.
  simpl in H1.
  symmetry.
  assumption.
Qed.

Theorem all_eq_forallb :
  forall (X : Type) (test : X -> bool) (P : X -> Prop) (l : list X),
    forallb test l = true -> all X (fun x => true = test x) l.
Proof.
  induction l.
  { intros.
    apply all_nil. }
  { intros.
    apply all_cons.
    { apply all_x in H.
      symmetry.
      assumption. }
    { apply IHl.
      simpl in H.
      apply andb_true_elim2 in H.
      assumption. } }
Qed.

Inductive appears_in {X : Type} (a : X) : list X -> Prop :=
| ai_here : forall l, appears_in a (a :: l)
| ai_later : forall b l, appears_in a l -> appears_in a (b :: l).

Theorem appears_in__ex : forall (X : Type) (a : X) (l : list X),
    appears_in a l -> ~ all X (fun x => x <> a) l.
Proof.
  intros X a l H.
  induction H.
  { unfold not.
    intros.
    inversion H.
    apply H2.
    apply eq_refl. }
  { unfold not.
    intros.
    inversion H0.
    unfold not in IHappears_in.
    apply IHappears_in.
    assumption. }
Qed.

Theorem app_nil_end : forall (X : Type) (l : list X),
    l ++ [] = l.
Proof.
  intros X l.
  induction l.
  { reflexivity. }
  { simpl.
    rewrite -> IHl.
    reflexivity. }
Qed.

Lemma appears_in_app : forall {X : Type} (xs ys : list X) (x : X),
    appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  intros X xs ys x H.
  induction xs.
  { simpl in H.
    right.
    assumption. }
  { inversion H.
    { left.
      apply ai_here. }
    { apply IHxs in H1.
      inversion H1.
      { left.
        apply ai_later.
        assumption. }
      { right.
        assumption. } } }
Qed.

Theorem app_n : forall (X : Type) (l1 l2:list X) (n : X),
    (n :: l1) ++ l2 = n :: l1 ++ l2.
Proof.
  intros X l1 l2 n.
  simpl.
  reflexivity.
Qed.

Lemma appers_l__l_app : forall (X : Type) (xs ys : list X) (x : X),
    appears_in x xs -> appears_in x (xs ++ ys).
Proof.
  induction xs.
  { intros ys x H.
    inversion H. }
  { intros ys x0 H.
    rewrite app_n.
    inversion H.
    { apply ai_here. }
    { apply ai_later.
      apply IHxs.
      assumption. } }
Qed.

Lemma app_appears_in : forall {X : Type} (xs ys : list X) (x : X),
    appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  induction xs.
  { intros ys x H.
    destruct H.
    { inversion H. }
    { assumption. } }
  { intros ys x0 H.
    inversion H.
    { apply appers_l__l_app.
      assumption. }
    { rewrite app_n.
      apply ai_later.
      apply IHxs.
      right.
      assumption. } }
Qed.

Inductive disjoint {X : Type} : list X -> list X -> Prop :=
| disj_nil : disjoint [] []
| disj_cons1 : forall a xs ys, disjoint xs ys -> ~ (appears_in a xs) -> disjoint xs (a :: ys)
| disj_cons2 : forall a xs ys, disjoint xs ys -> ~ (appears_in a ys) -> disjoint (a :: xs) ys.

Inductive no_repeats {X : Type} : list X -> Prop :=
| no_rep_nil : no_repeats []
| no_rep_cons : forall a l, no_repeats l -> ~ (appears_in a l) -> no_repeats (a :: l).

Example no_repeats_ex1 : no_repeats [1, 2, 3, 4].
Proof.
  apply no_rep_cons.
  apply no_rep_cons.
  apply no_rep_cons.
  apply no_rep_cons.
  apply no_rep_nil.

  unfold not.
  intros.
  inversion H.

  unfold not.
  intros.
  inversion H.
  inversion H1.

  unfold not.
  intros.
  inversion H.
  inversion H1.
  inversion H4.

  unfold not.
  intros.
  inversion H.
  inversion H1.
  inversion H4.
  inversion H7.
Qed.

Theorem O_le_n : forall n,
    0 <= n.
Proof.
  induction n.
  { apply le_n. }
  { apply le_S.
    assumption. }
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
    n <= m -> S n <= S m.
Proof.
  induction n.
  { intros m H.
    induction m.
    { constructor. }
    { constructor.
      apply IHm.
      apply O_le_n. } }
  { intros m H.
    induction m.
    { inversion H. }
    { inversion H.
      { constructor. }
      { constructor.
        apply IHm.
        assumption. } } }
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
    S n <= S m -> n <= m.
Proof.
  induction n.
  { intros m H.
    apply O_le_n. }
  { induction m.
    { intros.
      inversion H.
      inversion H1. }
    { intros.
      inversion H.
      { constructor. }
      { constructor.
        apply IHm.
        assumption. } } }
Qed.

Theorem le_plus_l : forall a b,
    a <= a + b.
Proof.
  induction a.
  { simpl.
    intros b.
    apply O_le_n. }
  { intros b.
    simpl.
    apply n_le_m__Sn_le_Sm.
    apply IHa. }
Qed.

Theorem O_l_Sn : forall n,
    0 < S n.
Proof.
  intros.
  induction n.
  { constructor. }
  { constructor.
    inversion IHn.
    { constructor. }
    { constructor.
      assumption. } }
Qed.

Theorem Sn_l_Sm__n_l_m : forall n m,
    S n < S m -> n < m.
Proof.
  induction n.
  { intros m H.
    induction m.
    { inversion H.
      inversion H1. }
    { apply O_l_Sn. } }
  { induction m.
    { intros.
      inversion H.
      inversion H1. }
    { intros.
      inversion H.
      { constructor. }
      { constructor.
        apply Sn_le_Sm__n_le_m.
        assumption. } } }
Qed.

Theorem n_l_m__Sn_l_Sm : forall n m,
    n < m -> S n < S m.
Proof.
  induction n.
  { induction m.
    { intros.
      inversion H. }
    { intros.
      inversion H.
      { constructor. }
      { constructor.
        apply n_le_m__Sn_le_Sm.
        assumption. } } }
  { induction m.
    { intros.
      inversion H. }
    { intros.
      inversion H.
      { constructor. }
      { constructor.
        apply n_le_m__Sn_le_Sm.
        assumption. } } }
Qed.

Theorem plus_S_l : forall n1 n2 m,
    S n1 + S n2 < S m -> n1 + n2 < m.
Proof.
  induction n1.
  { induction n2.
    { intros m H.
      simpl in H.
      simpl.
      induction m.
      { inversion H.
        inversion H1. }
      { apply O_l_Sn. } }
    { induction m.
      { intros.
        inversion H.
        inversion H1. }
      { intros.
        simpl.
        simpl in H.
        simpl in IHm.
        simpl in IHn2.
        inversion H.
        { constructor.
          constructor. }
        { apply n_l_m__Sn_l_Sm.
          apply IHn2.
          apply Sn_l_Sm__n_l_m.
          assumption. } } } }
  { induction n2.
    { induction m.
      { intros.
        inversion H.
        inversion H1. }
      { intros.
        simpl.
        apply n_l_m__Sn_l_Sm.
        apply IHn1.
        apply Sn_l_Sm__n_l_m.
        simpl in H.
        simpl.
        assumption. } }
    { induction m.
      { intros.
        inversion H.
        inversion H1. }
      { intros.
        simpl.
        rewrite plus_comm.
        simpl.
        rewrite plus_comm.
        apply n_l_m__Sn_l_Sm.
        simpl in IHn2.
        apply IHn2.
        simpl in H.
        apply Sn_l_Sm__n_l_m in H.
        apply Sn_l_Sm__n_l_m in H.
        apply n_l_m__Sn_l_Sm.
        rewrite plus_comm.
        simpl.
        rewrite plus_comm in H.
        simpl in H.
        assumption. } } }
Qed.

Theorem n_le_m__Sn_l_m : forall n m,
    n < m -> S n <= m.
Proof.
  induction n.
  { induction m.
    { intros.
      inversion H. }
    { intros.
      inversion H.
      { constructor. }
      { constructor.
        assumption. } } }
  { induction m.
    { intros.
      inversion H. }
    { intros.
      apply n_le_m__Sn_le_Sm.
      inversion H.
      { constructor. }
      { apply IHn.
        apply Sn_l_Sm__n_l_m.
        assumption. } } }
Qed.

Theorem plus_lt : forall n1 n2 m,
    n1 + n2 < m -> n1 < m /\ n2 < m.
Proof.
  induction n1.
  { induction n2.
    { intros m H.
      simpl in H.
      split.
      { assumption. }
      { assumption. } }
    { induction m.
      { intros.
        inversion H. }
      { intros.
        inversion H.
        { split.
          { apply O_l_Sn. }
          { constructor. } }
        { split.
          { apply O_l_Sn. }
          { simpl in H.
            assumption. } } } } }
  { induction n2.
    { induction m.
      { intros.
        inversion H. }
      { intros.
        split.
        { rewrite plus_comm in H.
          simpl in H.
          assumption. }
        { apply O_l_Sn. } } }
    { induction m.
      { intros.
        inversion H. }
      { intros.
        rewrite plus_comm in H.
        simpl in H.
        apply Sn_l_Sm__n_l_m in H.
        rewrite plus_comm in H.
        apply IHn2 in H.
        inversion H.
        split.
        { constructor.
          apply n_le_m__Sn_l_m.
          assumption. }
        { apply n_l_m__Sn_l_Sm.
          assumption. } } } }
Qed.

Theorem lt_S : forall n m,
    n < m -> n < S m.
Proof.
  induction n.
  { intros m H.
    apply O_l_Sn. }
  { induction m.
    { intros.
      inversion H. }
    { intros.
      apply n_l_m__Sn_l_Sm.
      apply IHn.
      apply Sn_l_Sm__n_l_m.
      assumption. } }
Qed.

Theorem ble_nat_true : forall n m,
    ble_nat n m = true -> n <= m.
Proof.
  induction n.
  { intros m H.
    apply O_le_n. }
  { induction m.
    { intros.
      inversion H. }
    { intros.
      apply n_le_m__Sn_le_Sm.
      apply IHn.
      inversion H.
      reflexivity. } }
Qed.

Theorem ble_nat_n_m_false__Sn_Sm_false : forall n m,
    ble_nat n m = false -> ble_nat (S n) (S m) = false.
Proof.
  induction n.
  { intros.
    inversion H. }
  { induction m.
    { intros.
      unfold ble_nat.
      reflexivity. }
    { intros.
      simpl.
      inversion H.
      reflexivity. } }
Qed.

Theorem ble_nat_n_Sn_false : forall n m,
    ble_nat n (S m) = false -> ble_nat n m = false.
Proof.
  induction n.
  { intros m H.
    inversion H. }
  { induction m.
    { intros.
      unfold ble_nat.
      reflexivity. }
    { intros.
      simpl.
      apply IHn.
      inversion H.
      reflexivity. } }
Qed.

Theorem ble_nat_false : forall n m,
    ble_nat n m = false -> ~(n <= m).
Proof.
  induction n.
  { intros m H.
    inversion H. }
  { induction m.
    { intros.
      unfold not.
      intros.
      inversion H0. }
    { intros.
      unfold not.
      intros.
      unfold not in IHn.
      simpl in H.
      apply IHn in H.
      { assumption. }
      { apply Sn_le_Sm__n_le_m.
        assumption. } } }
Qed.

Inductive nostutter: list nat -> Prop :=
| nos_nil : nostutter []
| nos_one : forall n, nostutter [n]
| nos_cons : forall n m l, n <> m -> nostutter (m :: l) -> nostutter (n :: m :: l).

Example test_nostutter_1: nostutter [3, 1, 4, 1, 5, 6].
Proof.
  constructor; unfold not; intros. discriminate.
  constructor; unfold not; intros. discriminate.
  constructor; unfold not; intros. discriminate.
  constructor; unfold not; intros. discriminate.
  constructor; unfold not; intros. discriminate.
  constructor.
Qed.

Example test_nostutter_2: nostutter [].
Proof. constructor. Qed.

Example test_nostutter_3: nostutter [5].
Proof. constructor. Qed.

Example test_nostutter_4: not (nostutter [3, 1, 1, 4]).
Proof.
  unfold not.
  intros.
  inversion H.
  inversion H4.
  unfold not in H7.
  apply H7.
  reflexivity.
Qed.

Theorem n_eq_m__Sn_eq_Sm: forall n m,
    n = m -> S n = S m.
Proof.
  induction n.
  { intros m H.
    rewrite H.
    reflexivity. }
  { intros m H.
    rewrite H.
    reflexivity. }
Qed.

Lemma app_length: forall {X : Type} (l1 l2 : list X),
    length (l1 ++ l2) = length l1 + length l2.
Proof.
  induction l1.
  { induction l2.
    { simpl.
      reflexivity. }
    { simpl.
      reflexivity. } }
  { induction l2.
    { simpl.
      rewrite app_nil_end.
      rewrite plus_0_r.
      reflexivity. }
    { simpl.
      rewrite plus_comm.
      apply n_eq_m__Sn_eq_Sm.
      apply app_length_cons_2.
      simpl.
      apply n_eq_m__Sn_eq_Sm.
      rewrite plus_comm.
      apply IHl1. } }
Qed.

Lemma appears_in_app_split: forall {X : Type} (x : X) (l : list X),
    appears_in x l -> exists l1, exists l2, l = l1 ++ (x :: l2).
Proof.
  intros X x l H.
  induction H.
  { exists [].
    exists l.
    simpl.
    reflexivity. }
  { destruct IHappears_in.
    destruct H0.
    exists (b :: x0).
    exists x1.
    simpl.
    rewrite H0.
    reflexivity. }
Qed.

Inductive repeats {X : Type}: list X -> Prop :=
| rep_1: forall n l, appears_in n l -> repeats (n :: l)
| rep_2: forall n l, repeats l -> repeats (n :: l).

Theorem len_0__nil: forall {X : Type} (l : list X),
    length l = 0 -> l = [].
Proof.
  induction l.
  { simpl.
    intros.
    reflexivity. }
  { intros.
    inversion H. }
Qed.

Theorem repeats_cons: forall {X : Type} (x : X) (l : list X),
    repeats l -> repeats (x :: l).
Proof.
  induction l.
  { intros.
    inversion H. }
  { intros.
    apply rep_2 with (n := x) in H.
    assumption. }
Qed.

Theorem not_repeats: forall {X : Type} (x : X) (l : list X),
    ~ repeats (x :: l) -> ~ repeats l.
Proof.
  induction l.
  { intros.
    unfold not.
    intros.
    inversion H0. }
  { intros.
    unfold not in H.
    unfold not.
    unfold not in IHl.
    intros.
    apply H.
    apply repeats_cons.
    assumption. }
Qed.

Theorem pigeonhole_principle: forall {X : Type} (l1 l2 : list X),
    excluded_middle ->
    (forall x, appears_in x l1 -> appears_in x l2) ->
    length l2 < length l1 ->
    repeats l1.
Proof.
  induction l1.
  { intros.
    inversion H1. }
  { induction l2.
    { intros EX.
      intros.
Admitted.

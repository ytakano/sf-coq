Require Export poly_j.

Check (2 + 2 = 4).

Check (ble_nat 3 2 = false).

Check (2 + 2 = 5).

Theorem plus_2_2_is_4 : 2 + 2 = 4.
Proof. reflexivity. Qed.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity. Qed.

Definition strange_prop1: Prop :=
  (2 + 2 = 5) -> (99 + 26 = 42).

Definition strange_prop2 :=
  forall n, (ble_nat n 17 = true) -> (ble_nat n 99 = true).

Definition even (n : nat) : Prop :=
  evenb n = true.

Check even.
Check (even 4).
Check (even 3).

Definition even_n__even_SSn (n : nat) : Prop :=
  (even n) -> (even (S (S n))).

Definition between (n m o : nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

Definition true_for_zero (P : nat -> Prop) : Prop :=
  P 0.

Definition true_for_n__true_for_Sn (P : nat -> Prop) (n : nat) : Prop :=
  P n -> P (S n).

Definition preserved_by_S (P : nat -> Prop) : Prop :=
  forall n', P n' -> P (S n').

Definition true_for_all_numbers (P : nat -> Prop) : Prop :=
  forall n, P n.

Definition our_nat_induction (P : nat -> Prop) : Prop :=
  (true_for_zero P) ->
  (preserved_by_S P) ->
  (true_for_all_numbers P).

Inductive good_day : day -> Prop :=
| gd_sat : good_day saturday
| gd_sun : good_day sunday.

Theorem gds : good_day sunday.
Proof. apply gd_sun. Qed.

Inductive day_before : day -> day -> Prop :=
| db_tue : day_before tuesday monday
| db_wed : day_before wednesday tuesday
| db_thu : day_before thursday wednesday
| db_fri : day_before friday thursday
| db_sat : day_before saturday friday
| db_sun : day_before sunday saturday
| db_mon : day_before monday sunday.

Inductive fine_day_for_singing : day -> Prop :=
| fdfs_any : forall d:day, fine_day_for_singing d.

Theorem fdfs_wed : fine_day_for_singing wednesday.
Proof. apply fdfs_any. Qed.

Definition fdfs_wed' : fine_day_for_singing wednesday :=
  fdfs_any wednesday.

Check fdfs_wed.
Check fdfs_wed'.
Check fdfs_any.

Inductive ok_day : day -> Prop :=
| okd_gd : forall d, good_day d -> ok_day d
| okd_before : forall d1 d2,
    ok_day d2 -> day_before d2 d1 -> ok_day d1.

Definition okdw : ok_day wednesday :=
  okd_before wednesday thursday
             (okd_before thursday friday
                         (okd_before friday saturday
                                     (okd_gd saturday gd_sat)
                                     db_sat)
                         db_fri)
             db_thu.

Theorem okdw' : ok_day wednesday.
Proof.
  apply okd_before with (d2 := thursday).
  apply okd_before with (d2 := friday).
  apply okd_before with (d2 := saturday).
  apply okd_gd.
  apply gd_sat.
  apply db_sat.
  apply db_fri.
  apply db_thu.
Qed.

Print okdw'.

Definition okd_before2 := forall d1 d2 d3,
    ok_day d3 ->
    day_before d2 d1 ->
    day_before d3 d2 ->
    ok_day d1.

Theorem okd_before2_valid : okd_before2.
Proof.
  intros d1 d2 d3.
  intros H1 H2 H3.
  apply okd_before with (d2 := d2).
  apply okd_before with (d2 := d3).
  apply H1.
  apply H3.
  apply H2.
Qed.

Definition okd_before2_valid' : okd_before2 :=
  fun (d1 d2 d3 : day) =>
    fun (H : ok_day d3) =>
      fun (H0 : day_before d2 d1) =>
        fun (H1 : day_before d3 d2) =>
          okd_before d1 d2 (okd_before d2 d3 H H1) H0.

Print okd_before2_valid.

Check nat_ind.

Theorem mult_0_r' : forall n : nat,
    n * 0 = 0.
Proof.
  apply nat_ind.
  { reflexivity. }
  { intros n IHn.
    simpl.
    apply IHn. }
Qed.

Theorem plus_one_r' : forall n : nat,
    n + 1 = S n.
Proof.
  apply nat_ind.
  { reflexivity. }
  { intros n IHn.
    simpl.
    rewrite -> IHn.
    reflexivity. }
Qed.

Inductive yesno : Type :=
| yes : yesno
| no : yesno.

Check yesno_ind.

Inductive rgb : Type :=
| red : rgb
| green : rgb
| blue : rgb.

Check rgb_ind.

Inductive natlist : Type :=
| nnil : natlist
| ncons : nat -> natlist -> natlist.

Check natlist_ind.

Inductive natlist1 : Type :=
| nnil1 : natlist1
| nsnoc1 : natlist1 -> nat -> natlist1.

Check natlist1_ind.

Inductive ExSet : Type :=
| con1 : bool -> ExSet
| con2 : nat -> ExSet -> ExSet.

Check ExSet_ind.

Check list_ind.

Inductive tree (X : Type) : Type :=
| leaf : X -> tree X
| node : tree X -> tree X -> tree X.

Check tree_ind.

Inductive mytype (X : Type) : Type :=
| constr1 : X -> mytype X
| constr2 : nat -> mytype X
| constr3 : mytype X -> nat -> mytype X.

Check mytype_ind.

Inductive foo (X Y : Type) : Type :=
| bar : X -> foo X Y
| baz : Y -> foo X Y
| quux : (nat -> foo X Y) -> foo X Y.

Check foo_ind.

Definition P_m0r (n : nat) : Prop :=
  n * 0 = 0.

Definition P_m0r' : nat -> Prop :=
  fun n => n * 0 = 0.

Theorem mult_0_r'' : forall n:nat,
    P_m0r n.
Proof.
  apply nat_ind.
  { reflexivity. }
  { unfold P_m0r.
    intros n' IHn'.
    simpl.
    rewrite -> IHn'.
    reflexivity. }
Qed.

Inductive ev : nat -> Prop :=
| ev_O : ev O
| ev_SS : forall n:nat, ev n -> ev (S (S n)).

Theorem four_ev' :
  ev 4.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_O.
Qed.

Check ev_O.
Check ev_SS.

Definition four_ev : ev 4 :=
  ev_SS 2 (ev_SS 0 (ev_O)).

Definition ev_plus4 : forall n, ev n -> ev (4 + n) :=
  fun n =>
    fun (e : ev n) =>
      ev_SS (2 + n) (ev_SS n e).

Theorem ev_plus4' : forall n,
    ev n -> ev (4 + n).
Proof.
  intros n H.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Theorem double_even : forall n,
    ev (double n).
Proof.
  apply nat_ind.
  { simpl.
    apply ev_O. }
  { intros n H.
    simpl.
    apply ev_SS.
    apply H. }
Qed.

Theorem ev_minus2 : forall n,
    ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  { simpl.
    apply ev_O. }
  { simpl.
    apply E'. }
Qed.

Theorem ev_even : forall n,
    ev n -> even n.
Proof.
  intros n E.
  induction E as [| n' E'].
  { unfold even.
    reflexivity. }
  { unfold even.
    simpl.
    unfold even in IHE'.
    apply IHE'. }
Qed.

Theorem ev_sum : forall n m,
    ev n -> ev m -> ev (n + m).
Proof.
  intros n m H1.
  induction H1.
  { simpl.
    intros H2.
    induction H2.
    { apply ev_O. }
    { apply ev_SS.
      apply H2. } }
  { intros H2.
    simpl.
    induction H2.
    { apply ev_SS.
      apply IHev.
      apply ev_O. }
    { apply ev_SS.
      apply IHev.
      apply ev_SS.
      apply H2. } }
Qed.

Theorem SSev_even : forall n,
    ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  apply E'.
Qed.

Theorem SSSSev_even : forall n,
    ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  inversion E' as [| n'' E''].
  apply E''.
Qed.

Theorem ev_minus2' : forall n,
    ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [|n' E'].
  { simpl.
    apply ev_O. }
  { simpl.
    apply E'. }
Qed.

Theorem zero_eq_plus : forall n m,
    0 = n + m -> n = 0.
Proof.
  intros n m eq.
  induction n.
  { reflexivity. }
  { induction m.
    { rewrite <- plus_comm in eq.
      simpl in eq.
      destruct eq.
      reflexivity. }
    { simpl in eq.
      inversion eq. } }
Qed.

Theorem ev_ev_even : forall n m,
    ev (n + m) -> ev n -> ev m.
Proof.
  intros n m E1 E2.
  induction E2.
  { simpl in E1.
    apply E1. }
  { inversion E1.
    apply IHE2 in H0.
    apply H0. }
Qed.

Theorem ev_plus_plus : forall n m p,
    ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
  intros n m p E1 E2.
  inversion E2.
  { apply zero_eq_plus in H0.
    rewrite -> H0 in E1. simpl in E1.
    rewrite -> H0 in E2. simpl in E2.
    apply ev_sum.
    { apply E1. }
    { apply E2. } }
  { inversion E1.
    { apply zero_eq_plus in H2.
      rewrite -> H2 in E1. simpl in E1.
      rewrite -> H2 in E2. simpl in E2.
      apply ev_sum.
      { apply E1. }
      { apply E2. } }
    { apply ev_SS in H0.
      apply ev_SS in H2.
      apply ev_sum with (n := S (S n1)) in H0.
      rewrite -> H in H0.
      rewrite -> H1 in H0.
      rewrite plus_assoc in H0.
      replace (n + m + n + p) with (n + n + m + p) in H0.
      { replace (n + n) with (double n).
        { replace (n + n) with (double n) in H0.
          { rewrite <- plus_assoc in H0. (* ev (m + p) *)
            apply ev_ev_even with (n := double n) in H0.
            { apply H0. }
            { apply double_even. } } (* ev (double n) *)
          { apply double_plus. } } (* n + n = double n *)
        { apply double_plus. } } (* n + n = double n *)
      { replace (n + n + m) with (n + m + n). (* n + n + m + p = n + m + n + p *)
        { reflexivity. } (* n + m + n + p = n + m + n + p *)
        { rewrite <- plus_assoc. (* n + m + n = n + n + n *)
          replace (m + n) with (n + m).
          { rewrite plus_assoc. (* n + (n + m) = n + n + m *)
            reflexivity. }
          { rewrite plus_comm. (* n + m = m + n *)
            reflexivity. } } }
      { apply H2. } } } (* ev (S (S n1)) *)
Qed.

Inductive MyProp : nat -> Prop :=
| MyProp1 : MyProp 4
| MyProp2 : forall n:nat, MyProp n -> MyProp (4 + n)
| MyProp3 : forall n:nat, MyProp (2 + n) -> MyProp n.

Theorem MyProp_ten : MyProp 10.
Proof.
  apply MyProp3. simpl.
  apply MyProp2.
  apply MyProp2.
  apply MyProp1.
Qed.

Theorem MyProp_0 : MyProp 0.
Proof.
  apply MyProp3. simpl.
  apply MyProp3. simpl.
  apply MyProp1.
Qed.

Theorem MyProp_plustwo : forall n:nat, MyProp n -> MyProp (S (S n)).
Proof.
  intros n H.
  apply MyProp3.
  apply MyProp2 in H.
  simpl.
  simpl in H.
  apply H.
Qed.

Theorem MyProp_ev : forall n:nat,
    ev n -> MyProp n.
Proof.
  intros n E.
  induction E as [| n' E'].
  { apply MyProp_0. }
  { apply MyProp_plustwo.
    apply IHE'. }
Qed.

Theorem plus_assoc' : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n'].
  { reflexivity. }
  { simpl.
    rewrite -> IHn'.
    reflexivity. }
Qed.

Theorem plus_comm' : forall n m : nat,
    n + m = m + n.
Proof.
  induction n as [| n'].
  { intros m.
    rewrite -> plus_0_r.
    reflexivity. }
  { intros m.
    rewrite <- plus_n_Sm.
    simpl.
    rewrite <- IHn'.
    reflexivity. }
Qed.

Theorem plus_comm'' : forall n m : nat,
    n + m = m + n.
Proof.
  induction m as [| m'].
  { simpl.
    rewrite -> plus_0_r.
    reflexivity. }
  { simpl.
    rewrite <- plus_n_Sm.
    rewrite <- IHm'.
    reflexivity. }
Qed.

Fixpoint true_upto_n__true_everywhere (n : nat) (f : nat -> Prop) : Prop :=
  match n with
  | O    => forall m, f m
  | S n' => f n -> true_upto_n__true_everywhere n' f
  end.

Eval simpl in true_upto_n__true_everywhere 3 (fun n => even n).
Eval simpl in even 3 -> even 2 -> even 1 -> forall m : nat, even m.

Example true_upto_n_example :
  (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
Proof. reflexivity. Qed.

Theorem ev_MyProp' : forall n : nat,
    MyProp n -> ev n.
Proof.
  apply MyProp_ind.
  { apply ev_SS.
    apply ev_SS.
    apply ev_O. }
  { intros n H1 H2.
    apply ev_plus4.
    apply H2. }
  { intros n H1 H2.
    apply SSev_even.
    simpl in H2.
    apply H2. }
Qed.

(*
Fixpoint MyProp_ev_const (n : nat) (x : ev n) : MyProp n :=
  match x with
  | ev_O => MyProp3 0 (MyProp3 2 MyProp1)
  | ev_SS n' x' =>
    let plus2 := (ev_SS (S (S n')) (ev_SS n' x')) in
    MyProp3 (S (S n')) (MyProp_ev_const (2 + (S (S n')))
                                        plus2)
  end.
*)

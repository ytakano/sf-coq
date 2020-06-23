Require Export lists_j.

Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Check nil.
Check cons.

Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
  | nil _ => 0
  | cons _ h t => S (length X t)
  end.

Example test_length1 :
  length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity. Qed.

Example test_length2 :
  length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity. Qed.

Fixpoint app (X:Type) (l1 l2 : list X) : (list X) :=
  match l1 with
  | nil _ => l2
  | cons _ h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
  | nil _ => cons X v (nil X)
  | cons _ h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : (list X) :=
  match l with
  | nil _ => nil X
  | cons _ h t => snoc X (rev X t) h
  end.

Example test_rev1:
  rev nat (cons nat 1 (cons nat 2 (nil nat)))
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity. Qed.


Example test_rev2: rev bool (nil bool) = nil bool.
Proof. reflexivity. Qed.


Fixpoint app' (X:_) l1 l2 : list X :=
  match l1 with
  | nil _ => l2
  | cons _ h t => cons X h (app' X t l2)
  end.

Check app'.
Check app.

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments length {X} _.
Arguments app {X} _ _.
Arguments rev {X} _.
Arguments snoc {X} _ _.

Definition list123'' :=
  cons 1 (cons 2 (cons 3 nil)).

Fixpoint length'' {X:Type} (l:list X) : nat :=
  match l with
  | nil => 0
  | cons h t => S (length'' t)
  end.

Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

Definition list123''' := [1, 2, 3].

Fixpoint repeat (X:Type) (n:X) (count:nat) : list X :=
  match count with
  | O => nil
  | S c => cons n (repeat X n c)
  end.

Example test_repeat1:
  repeat bool true 2 = cons true (cons true nil).
Proof. reflexivity. Qed.

Theorem nil_app: forall X:Type, forall l:list X,
      app [] l = l.
Proof.
  reflexivity.
Qed.

Theorem rev_snoc: forall X:Type, forall v:X, forall s:list X,
        rev (snoc s v) = v :: (rev s).
Proof.
  intros X v s.
  induction s.
  { reflexivity. }
  { simpl.
    rewrite -> IHs.
    reflexivity. }
Qed.

Theorem snoc_with_append: forall X: Type, forall l1 l2: list X, forall v: X,
        snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  intros X l1 l2 v.
  induction l1.
  { reflexivity. }
  { simpl.
    rewrite -> IHl1.
    reflexivity. }
Qed.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match (lx, ly) with
  | ([], _) => []
  | (_, []) => []
  | (x::tx, y::ty) => (x, y) :: (combine tx ty)
  end.

Check @combine.

Eval simpl in (combine [1, 2] [false, false, true, true]).

Fixpoint split {X Y : Type} (l:list (X * Y)) : list X * list Y :=
  match l with
  | nil => (nil, nil)
  | (x, y) :: t => let s := split t in (cons x (fst s), (cons y (snd s)))
  end.

Example test_split: split [(1, false), (2, false)] = ([1, 2], [false, false]).
Proof. reflexivity. Qed.

Inductive option (X:Type) : Type :=
| Some : X -> option X
| None : option X.

Arguments Some {X}.
Arguments None {X}.

Fixpoint index {X:Type} (n:nat) (l:list X) : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

Example test_index1: index 0 [4,5,6,7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2: index 1 [[1], [2]] = Some [2].
Proof. reflexivity. Qed.
Example test_index3: index 2 [true] = None.
Proof. reflexivity. Qed.

Definition hd_opt {X:Type} (l:list X) : option X :=
  match l with
  | nil => None
  | h :: _ => Some h
  end.

Check @hd_opt.

Example test_hd_opt1: hd_opt [1, 2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_opt2: hd_opt [[1], [2]] = Some [1].
Proof. reflexivity. Qed.

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).
Check @doit3times.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.
Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Check plus.

Definition prod_curry {X Y Z : Type} (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type} (f : X -> Y -> Z) (p : X * Y) : Z :=
  f (fst p) (snd p).

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
    prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type) (f : (X * Y) -> Z) (p : X * Y),
    prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.
  destruct p.
  reflexivity.
Qed.

Fixpoint filter {X:Type} (test: X -> bool) (l:list X) : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t) else filter test t
  end.

Example test_filter1: filter evenb [1, 2, 3, 4] = [2, 4].
Proof. reflexivity. Qed.

Definition length_is_1 {X:Type} (l:list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
  filter length_is_1 [[1, 2], [3], [4], [5, 6, 7], [], [8]] = [[3], [4], [8]].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1,0,3,1,4,5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0, 2, 4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
  filter (fun l => beq_nat (length l) 1)
         [ [1, 2], [3], [4], [5,6,7], [], [8] ] = [ [3], [4], [8] ].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun x => (andb (evenb x) (blt_nat 7 x))) l.

Example test_filter_even_gt7_1:
  filter_even_gt7 [1, 2, 6, 9, 10, 3, 12, 18] = [10, 12, 18].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2:
  filter_even_gt7 [5, 2, 6, 19, 129] = [].
Proof. reflexivity. Qed.

Definition partition {X:Type} (test:X -> bool) (l:list X) : list X * list X :=
  ((filter test l), (filter (fun x => negb (test x)) l)).

Example test_partition1: partition oddb [1, 2, 3, 4, 5] = ([1, 3, 5], [2, 4]).
Proof. reflexivity. Qed.

Example test_partition2: partition (fun x => false) [5, 9, 0] = ([], [5, 9, 0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y:Type} (f: X -> Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (plus 3) [2, 0, 2] = [5, 3, 5].
Proof. reflexivity. Qed.

Example test_map2: map oddb [2, 1, 2, 5] = [false, true, false, true].
Proof. reflexivity. Qed.

Example test_map3:
  map (fun n => [evenb n, oddb n]) [2, 1, 2, 5]
  = [[true, false], [false, true], [true, false], [false, true]].
Proof. reflexivity. Qed.

Theorem map_snoc: forall (X Y : Type) (f : X -> Y) (h:X) (t:list X),
    map f (snoc t h) = snoc (map f t) (f h).
Proof.
  intros X Y f h t.
  induction t.
  { reflexivity. }
  { simpl.
    rewrite -> IHt.
    reflexivity. }
Qed.

Theorem map_rev: forall (X Y : Type) (f : X -> Y) (l : list X),
    map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l.
  { reflexivity. }
  { simpl.
    rewrite -> map_snoc.
    rewrite -> IHl.
    reflexivity. }
Qed.

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => app (f h) (flat_map f t)
  end.

Example test_flat_map1:
  flat_map (fun n => [n, n, n]) [1, 5, 4] = [1, 1, 1, 5, 5, 5, 4, 4, 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

Fixpoint fold {X Y:Type} (f : X -> Y -> Y) (l:list X) (b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Check (fold plus).
Eval simpl in (fold plus [1,2,3,4] 0).

Definition constfun {X:Type} (x:X) : nat -> X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Definition override {X:Type} (f:nat -> X) (k:nat) (x:X) : nat -> X :=
  fun (k':nat) => if beq_nat k k' then x else f k'.

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.

Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.

Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.

Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.

Theorem override_example: forall (b:bool),
    (override (constfun b) 3  true) 2 = b.
Proof.
  intros b.
  reflexivity.
Qed.

Definition plus3 (n:nat) : nat := plus 3 n.

Theorem unfold_example: forall m n,
    3 + n = m -> plus3 (n + 1) = m + 1.
Proof.
  intros n m H.
  unfold plus3.
  rewrite -> plus_assoc.
  rewrite -> H.
  reflexivity.
Qed.

Theorem override_eq: forall {X:Type} x k (f : nat -> X),
    (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Theorem override_neq: forall {X:Type} x1 x2 k1 k2 (f:nat -> X),
    f k1 = x1 -> beq_nat k2 k1 = false -> (override f k2 x2) k1 = x1.
Proof.
  intros X x1 x2 k1 k2 f H1 H2.
  unfold override.
  rewrite -> H2.
  rewrite -> H1.
  reflexivity.
Qed.

Theorem eq_add_S: forall (n m : nat),
    S n = S m -> n = m.
Proof.
  intros n m eq.
  inversion eq.
  reflexivity.
Qed.

Theorem silly4: forall (n m : nat),
    [n] = [m] -> n = m.
Proof.
  intros n m H.
  inversion H.
  reflexivity.
Qed.

Theorem silly5: forall (n m o:nat),
    [n,m] = [o,o] -> [n] = [m].
Proof.
  intros n m o eq.
  inversion eq.
  reflexivity.
Qed.

Example sillyex1: forall (X:Type) (x y z : X) (l j : list X),
    x :: y :: l = z :: j ->
    y :: l = x :: j ->
    x = y.
Proof.
  intros X x y z l j H1 H2.
  inversion H1.
  inversion H2.
  symmetry.
  apply H0.
Qed.

Theorem silly6: forall (n:nat),
    S n = O -> 2 + 2 = 5.
Proof.
  intros n contra.
  inversion contra.
Qed.

Theorem silly7: forall (n m : nat),
    false = true -> [n] = [m].
Proof.
  intros n m contra.
  inversion contra.
Qed.

Example sillyex2: forall (X:Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    y :: l = z :: j ->
    x = z.
Proof.
  intros X x y z l j H1 H2.
  inversion H1.
Qed.

Lemma eq_remove_S: forall n m,
    n = m -> S n = S m.
Proof.
  intros n m eq.
  rewrite -> eq.
  reflexivity.
Qed.

Theorem beq_nat_eq: forall n m,
    true = beq_nat n m -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  { intros m H.
    destruct m.
    { reflexivity. }
    { inversion H. } }
  { destruct m as [| m'].
    { simpl.
      intros contra.
      inversion contra. }
    { simpl.
      intros H.
      apply eq_remove_S.
      apply IHn'.
      apply H. } }
Qed.

Theorem beq_nat_eq': forall m n,
    beq_nat n m = true -> n = m.
Proof.
  intros m.
  { induction m as [| m'].
    { intros n H.
      destruct n.
      { reflexivity. }
      { inversion H. } }
    { intros n H.
      destruct n.
      { inversion H. }
      { inversion H.
        apply eq_remove_S.
        apply IHm'.
        apply H1. } } }
Qed.

Theorem length_snoc': forall (X:Type) (v:X) (l:list X) (n:nat),
    length l = n -> length (snoc l v) = S n.
Proof.
  intros X v l.
  induction l.
  { simpl.
    destruct n.
    { intros H.
      reflexivity. }
    { intros H.
      inversion H. } }
  { intros n H.
    destruct n.
    { inversion H. }
    { inversion H.
      rewrite -> H1.
      simpl.
      apply eq_remove_S.
      apply IHl.
      apply H1. } }
Qed.

Theorem beq_nat_0_l: forall n,
    true = beq_nat 0 n -> 0 = n.
Proof.
  intros n H.
  destruct n.
  { reflexivity. }
  { inversion H. }
Qed.

Theorem beq_nat_0_r: forall n,
    true = beq_nat n 0 -> 0 = n.
Proof.
  destruct n.
  { intros H.
    reflexivity. }
  { intros H.
    inversion H. }
Qed.

Theorem double_injective: forall n m,
    double n = double m -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  { destruct m.
    { reflexivity. }
    { intros H.
      inversion H. } }
  { destruct m.
    { intros H.
      inversion H. }
    { intros H.
      inversion H.
      apply eq_remove_S.
      apply IHn'.
      apply H1. } }
Qed.

Theorem S_inj: forall (n m : nat) (b : bool),
    beq_nat (S n) (S m) = b -> beq_nat n m = b.
Proof.
  intros n m b H.
  simpl in H.
  apply H.
Qed.

Theorem silly3' : forall (n : nat),
    (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
    true = beq_nat n 5 ->
    true = beq_nat (S (S n)) 7.
Proof.
  intros n H1 H2.
  symmetry in H2.
  apply H1 in H2.
  symmetry.
  apply H2.
Qed.

Theorem plus_n_n_injective : forall n m,
    n + n = m + m -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  { destruct m.
    { reflexivity. }
    { intros H.
      simpl in H.
      inversion H. } }
  { destruct m.
    { intros H.
      inversion H. }
    { intros H.
      apply eq_remove_S.
      apply IHn'.
      simpl in H.
      inversion H.
      rewrite plus_comm in H1.
      replace (m + S m) with (S m + m) in H1.
      inversion H1.
      reflexivity.
      { rewrite plus_comm.
        reflexivity. } } }
Qed.

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
       else false.

Theorem sillyfun_false : forall (n : nat),
    sillyfun n = false.
Proof.
  intros n.
  unfold sillyfun.
  destruct (beq_nat n 3).
  { reflexivity. }
  { destruct (beq_nat n 5).
    { reflexivity. }
    { reflexivity. } }
Qed.

Theorem override_shadow : forall {X : Type} x1 x2 k1 k2 (f : nat -> X),
    (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f.
  unfold override.
  destruct (beq_nat k1 k2).
  { reflexivity. }
  { reflexivity. }
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
       else false.

Theorem sillyfun1_odd : forall (n : nat),
    sillyfun1 n = true -> oddb n = true.
Proof.
  intros n eq.
  unfold sillyfun1 in eq.
  remember (beq_nat n 3) as e3.
  destruct e3.
  { apply beq_nat_eq in Heqe3.
    rewrite -> Heqe3.
    reflexivity. }
  { remember (beq_nat n 5) as e5.
    destruct e5.
    { apply beq_nat_eq in Heqe5.
      rewrite -> Heqe5.
      reflexivity. }
    { inversion eq. } }
Qed.

Theorem override_same : forall {X : Type} x1 k1 k2 (f : nat -> X),
    f k1 = x1 -> (override f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f H.
  unfold override.
  remember (beq_nat k1 k2) as eq.
  destruct eq.
  { apply beq_nat_eq in Heqeq.
    rewrite <- Heqeq.
    symmetry.
    apply H. }
  { reflexivity. }
Qed.

Theorem filter_exercise : forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
    filter test l = x :: lf -> test x = true.
Proof.
  induction l.
  { intros lf H.
    inversion H. }
  { intros lf H.
    inversion H.
    remember (test x0) as t0.
    destruct t0.
    { simpl in H.
      inversion H1.
      rewrite <- H2.
      rewrite <- Heqt0.
      reflexivity. }
    { apply IHl in H1.
      apply H1. } }
Qed.

Theorem trans_eq : forall {X : Type} (n m o : X),
    n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
    [a, b] = [c, d] -> [c, d] = [e, f] -> [a, b] = [e, f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m := [c, d]).
  apply eq1.
  apply eq2.
Qed.

Theorem beq_refl : forall (X:Type) (a b : X),
    a = b -> b = a.
Proof.
  intros X a b H.
  symmetry.
  apply H.
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
    m = (minustwo o) ->
    (n + p) = m ->
    (n + p) = (minustwo o).
Proof.
  intros n m o p H1 H2.
  apply trans_eq with (m0 := m).
  apply H2.
  apply H1.
Qed.

Theorem eq_beq_nat : forall n m,
    n = m -> true = beq_nat n m.
Proof.
  intros n m H.
  rewrite -> H.
  apply beq_nat_refl.
Qed.

Theorem beq_nat_trans : forall n m p,
    true = beq_nat n m ->
    true = beq_nat m p ->
    true = beq_nat n p.
Proof.
  intros n m p H1 H2.
  apply beq_nat_eq in H1.
  apply beq_nat_eq in H2.
  apply eq_beq_nat.
  apply trans_eq with (m0 := m).
  apply H1.
  apply H2.
Qed.

Theorem override_permute : forall {X : Type} x1 x2 k1 k2 k3 (f : nat -> X),
    false = beq_nat k2 k1 ->
    (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  intros X x1 x2 k1 k2 k3 f H.
  remember (beq_nat k1 k3) as e13.
  destruct e13.
  { unfold override.
    rewrite <- Heqe13.
    remember (beq_nat k2 k3) as e23.
    destruct e23.
    { apply beq_nat_eq in Heqe13.
      apply beq_nat_eq in Heqe23.
      rewrite -> Heqe13 in H.
      rewrite -> Heqe23 in H.
      rewrite <- beq_nat_refl in H.
      inversion H. }
    { reflexivity. } }
  { unfold override.
    rewrite <- Heqe13.
    reflexivity. }
Qed.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.
Example test_fold_length1 : fold_length [4, 7, 0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X),
    fold_length l = length l.
Proof.
  intros X.
  induction l.
  { reflexivity. }
  { simpl.
    rewrite <- IHl.
    unfold fold_length.
    simpl.
    reflexivity. }
Qed.

Definition fold_map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun h lf => f h :: lf) l [].

Example test_fold_map1: fold_map (plus 3) [2, 0, 2] = [5, 3, 5].
Proof. reflexivity. Qed.

Example test_fold_map2: fold_map oddb [2, 1, 2, 5] = [false, true, false, true].
Proof. reflexivity. Qed.

Example test_fold_map3:
  fold_map (fun n => [evenb n, oddb n]) [2, 1, 2, 5]
  = [[true, false], [false, true], [true, false], [false, true]].
Proof. reflexivity. Qed.

Theorem fold_map_correct : forall (X Y : Type) (f : X -> Y) (l : list X),
    map f l = fold_map f l.
Proof.
  intros X Y f l.
  induction l.
  { reflexivity. }
  { simpl.
    rewrite -> IHl.
    unfold fold_map.
    simpl.
    reflexivity. }
Qed.

Fixpoint forallb {X : Type} (f : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | h :: t =>
    let b := f h in andb b (forallb f t)
  end.

Eval simpl in forallb oddb [1, 3, 5, 7, 9].

Fixpoint existb {X : Type} (f : X -> bool) (l : list X) : bool :=
  match l with
  | [] => false
  | h :: t =>
    match f h with
    | true => true
    | false => existb f t
    end
  end.

Definition existb' {X : Type} (f : X -> bool) (l : list X) : bool :=
  negb (forallb (fun x => negb (f x)) l).

Theorem existb_existb' : forall (X : Type) (f : X -> bool) (l : list X),
    existb f l = existb' f l.
Proof.
  intros X f l.
  induction l.
  { reflexivity. }
  { simpl.
    rewrite -> IHl.
    unfold existb'.
    simpl.
    destruct (f x).
    { reflexivity. }
    { reflexivity. } }
Qed.

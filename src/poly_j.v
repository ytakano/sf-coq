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


Require Export basic_j.

Module NatList.
  Inductive natprod : Type :=
    pair : nat -> nat -> natprod.

  Definition fst (p : natprod) : nat :=
    match p with
    | pair x y => x
    end.

  Definition snd (p: natprod) : nat :=
    match p with
    | pair x y => y
    end.

  Notation "( x , y )" := (pair x y).

  Eval simpl in (fst (3, 4)).

  Definition swap_pair (p : natprod) : natprod :=
    match p with
    | (x, y) => (y, x)
    end.

  Theorem surjective_pairing' : forall (n m : nat),
      (n, m) = (fst (n, m), snd (n, m)).
  Proof.
    reflexivity.
  Qed.

  Theorem surjective_pairing_stuck : forall (p : natprod),
      p = (fst p, snd p).
  Proof.
    intros p.
    destruct p.
    reflexivity.
  Qed.

  Theorem snd_fst_is_swap : forall (p : natprod),
      (snd p, fst p) = swap_pair p.
  Proof.
    intros p.
    destruct p.
    reflexivity.
  Qed.

  Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

  Eval simpl in cons 1 (cons 2 (cons 3 nil)).

  Notation "x :: l" := (cons x l) (at level 60, right associativity).
  Notation "[ ]" := nil.
  Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

  Eval simpl in 1 :: 2 :: 3 :: [].
  Eval simpl in [1, 2, 3].
  
  Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | O => nil
    | S count' => n :: (repeat n count')
    end.

  Fixpoint length (l:natlist) : nat :=
    match l with
    | nil => O
    | h :: t => S (length t)
    end.

  Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
    end.

  Notation "x ++ y" := (app x y)
                         (right associativity, at level 60).

  Definition hd (default:nat) (l:natlist) : nat :=
    match l with
    | nil => default
    | h :: t => h
    end.

  Definition tail (l:natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => t
    end.

  Fixpoint nonzeros (l:natlist) : natlist :=
    match l with
    | nil => nil
    | O :: t => nonzeros t
    | h :: t => h :: nonzeros t
    end.

  Example test_nonzeros: nonzeros [0, 1, 0, 2, 3, 0, 0] = [1, 2, 3].
  Proof.
    reflexivity.
  Qed.

  Fixpoint oddmembers (l:natlist) : natlist :=
    match l with
    | nil => nil
    | n :: t =>
      match oddb n with
      | true  => n :: oddmembers t
      | false => oddmembers t
      end
    end.

  Example test_oddmembers: oddmembers [0, 1, 0, 2, 3, 0, 0] = [1, 3].
  Proof.
    reflexivity.
  Qed.

  Fixpoint countoddmembers (l:natlist) : nat :=
    length (oddmembers l).

  Example test_countoddmembers1: countoddmembers [1, 0, 3, 1, 4, 5] = 4.
  Proof.
    reflexivity.
  Qed.

  Example test_countoddmembers2: countoddmembers [0, 2, 4] = 0.
  Proof.
    reflexivity.
  Qed.

  Example test_countoddmembers3: countoddmembers nil = 0.
  Proof.
    reflexivity.
  Qed.

  Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | h1 :: t1 =>
      match l2 with
      | nil => l1
      | h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
      end
    end.

  Example test_alternate1: alternate [1, 2, 3] [4, 5, 6] = [1, 4, 2, 5, 3, 6].
  Proof.
    reflexivity.
  Qed.

  Example test_alternate2: alternate [1] [4, 5, 6] = [1, 4, 5, 6].
  Proof.
    reflexivity.
  Qed.

  Example test_alternate3: alternate [1, 2, 3] [4] = [1, 4, 2, 3].
  Proof.
    reflexivity.
  Qed.

  Example test_alternate4: alternate [] [20, 30] = [20, 30].
  Proof.
    reflexivity.
  Qed.


  Definition bag := natlist.

  Fixpoint count (v:nat) (s:bag) : nat :=
    match s with
    | nil => 0
    | v' :: t =>
      match beq_nat v v' with
      | true => 1 + count v t
      | false => count v t
      end
    end.

  Example test_count1: count 1 [1, 2, 3, 1, 4, 1] = 3.
  Proof.
    reflexivity.
  Qed.

  Example test_count2: count 6 [1, 2, 3, 1, 4, 1] = 0.
  Proof.
    reflexivity.
  Qed.

  Definition sum : bag -> bag -> bag := app.

  Example test_sum1: count 1 (sum [1, 2, 3] [1, 4, 1]) = 3.
  Proof.
    reflexivity.
  Qed.

  Definition add (v:nat) (s:bag) : bag := v :: s.

  Example test_add1: count 1 (add 1 [1, 4, 1]) = 3.
  Proof.
    reflexivity.
  Qed.

  Example test_add2: count 5 (add 1 [1, 4, 1]) = 0.
  Proof.
    reflexivity.
  Qed.

  Definition member (v:nat) (s:bag) : bool := negb (beq_nat (count v s) 0).

  Example test_member1: member 1 [1, 4, 1] = true.
  Proof.
    reflexivity.
  Qed.

  Example test_member2: member 2 [1, 4, 1] = false.
  Proof.
    reflexivity.
  Qed.

  Fixpoint remove_one (v:nat) (s:bag) : bag :=
    match s with
    | nil => nil
    | h :: t =>
      match beq_nat v h with
      | true => t
      | false => h :: (remove_one v t)
      end
    end.

  Example test_remove_one1: count 5 (remove_one 5 [2, 1, 5, 4, 1]) = 0.
  Proof.
    reflexivity.
  Qed.

  Example test_remove_one2: count 5 (remove_one 5 [2, 1, 4, 1]) = 0.
  Proof.
    reflexivity.
  Qed.

  Example test_remove_one3: count 4 (remove_one 5 [2, 1, 4, 5, 1, 4]) = 2.
  Proof.
    reflexivity.
  Qed.

  Example test_remove_one4: count 5 (remove_one 5 [2, 1, 5, 4, 5, 1, 4]) = 1.
  Proof.
    reflexivity.
  Qed.

  Fixpoint remove_all (v:nat) (s:bag) : bag :=
    match s with
    | nil => nil
    | h :: t =>
      match beq_nat v h with
      | true => remove_all v t
      | false => h :: remove_all v t
      end
    end.

  Example test_remove_all1: count 5 (remove_all 5 [2, 1, 5, 4, 1]) = 0.
  Proof.
    reflexivity.
  Qed.

  Example test_remove_all2: count 5 (remove_all 5 [2, 1, 4, 1]) = 0.
  Proof.
    reflexivity.
  Qed.

  Example test_remove_all3: count 4 (remove_all 5 [2, 1, 4, 5, 1, 4]) = 2.
  Proof.
    reflexivity.
  Qed.

  Example test_remove_all4: count 5 (remove_all 5 [2, 1, 5, 4, 1, 5, 1, 4]) = 0.
  Proof.
    reflexivity.
  Qed.

  Fixpoint subset (s1:bag) (s2:bag) : bool :=
    match s1 with
    | nil => true
    | h :: t =>
      match member h s2 with
      | true => subset t (remove_one h s2)
      | false => false
      end
    end.

  Example test_subset1: subset [1, 2] [2, 1, 4, 1] = true.
  Proof.
    reflexivity.
  Qed.

  Example test_subset2: subset [1, 2, 2] [2, 1, 4, 1] = false.
  Proof.
    reflexivity.
  Qed.

  Example test_subset3: subset [] [] = true.
  Proof.
    reflexivity.
  Qed.

  Theorem sum_nil_l : forall a:bag,
      sum a [] = a.
  Proof.
    intros a.
    induction a.
    { reflexivity. }
    { simpl.
      rewrite -> IHa.
      reflexivity. }
  Qed.

  Theorem nil_app : forall l:natlist,
      [] ++ l = l.
  Proof.
    reflexivity.
  Qed.

  Theorem tl_length_pred : forall l:natlist,
      pred (length l) = length (tail l).
  Proof.
    intros l.
    destruct l as [| n l'].
    { reflexivity. }
    { reflexivity. }
  Qed.

  Theorem app_ass : forall l1 l2 l3 : natlist,
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros l1 l2 l3.
    induction l1 as [| n l1'].
    { reflexivity. }
    { simpl.
      rewrite -> IHl1'.
      reflexivity. }
  Qed.

  Theorem app_length : forall l1 l2 : natlist,
      length (l1 ++ l2) = (length l1) + (length l2).
  Proof.
    intros l1 l2.
    induction l1 as [| n l1'].
    { reflexivity. }
    { simpl.
      rewrite -> IHl1'.
      reflexivity. }
  Qed.

  Fixpoint snoc (l:natlist) (v:nat) : natlist :=
    match l with
    | nil => [v]
    | h :: t => h :: (snoc t v)
    end.

  Fixpoint rev (l:natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => snoc (rev t) h
    end.

  Example test_rev1: rev [1, 2, 3] = [3, 2, 1].
  Proof. reflexivity. Qed.
  Example test_rev2: rev nil = nil.
  Proof. reflexivity. Qed.

  Theorem length_snoc : forall n:nat, forall l:natlist,
        length (snoc l n) = S (length l).
  Proof.
    intros n l.
    induction l as [| n' l'].
    { reflexivity. }
    { simpl.
      rewrite -> IHl'.
      reflexivity. }
  Qed.
  
  Theorem rev_length : forall l : natlist,
      length (rev l) = length l.
  Proof.
    intros l.
    induction l as [| n l'].
    { reflexivity. }
    { simpl.
      rewrite -> length_snoc.
      rewrite -> IHl'.
      reflexivity. }
  Qed.

  Theorem app_nil_end : forall l : natlist,
      l ++ [] = l.
  Proof.
    intros l.
    induction l.
    { reflexivity. }
    { simpl.
      rewrite -> IHl.
      reflexivity. }
  Qed.

  Theorem rev_snoc_n : forall l:natlist, forall n:nat,
        rev (snoc l n) = n :: rev l.
  Proof.
    intros l n.
    induction l.
    { reflexivity. }
    { simpl.
      rewrite -> IHl.
      reflexivity. }
  Qed.

  Theorem rev_involutive : forall l : natlist,
      rev (rev l) = l.
  Proof.
    intros l.
    induction l.
    { reflexivity. }
    { simpl.
      rewrite -> rev_snoc_n.
      rewrite -> IHl.
      reflexivity. }
  Qed.

  Theorem snoc_dist : forall l1 l2 : natlist, forall n,
        snoc (l1 ++ l2) n = l1 ++ snoc (l2) n.
  Proof.
    intros l1 l2 n.
    induction l1 as [| n1' l1'].
    { reflexivity. }
    { simpl.
      rewrite -> IHl1'.
      reflexivity. }
  Qed.

  Theorem distr_rev : forall l1 l2 : natlist,
      rev (l1 ++ l2) = (rev l2) ++ (rev l1).
  Proof.
    intros l1 l2.
    induction l1 as [| n1 l1'].
    { simpl.
      rewrite -> app_nil_end.
      reflexivity. }
    { simpl.
      rewrite -> IHl1'.
      rewrite -> snoc_dist.
      reflexivity. }
  Qed.

  Theorem app_ass4 : forall l1 l2 l3 l4 : natlist,
      l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof.
    intros l1 l2 l3 l4.
    rewrite -> app_ass.
    rewrite -> app_ass.
    reflexivity.
  Qed.

  Theorem snoc_append : forall (l:natlist) (n:nat),
      snoc l n = l ++ [n].
  Proof.
    intros l n.
    induction l.
    { simpl.
      reflexivity. }
    { simpl.
      rewrite -> IHl.
      reflexivity. }
  Qed.

  Theorem app_n : forall (l1 l2:natlist) (n:nat),
      (n :: l1) ++ l2 = n :: l1 ++ l2.
  Proof.
    intros l1 l2 n.
    simpl.
    reflexivity.
  Qed.

  Theorem nonzeros_n : forall (l:natlist) (n:nat),
    nonzeros (n :: l) = nonzeros [n] ++ nonzeros l.
  Proof.
    intros n l.
    induction l.
    { reflexivity. }
    { simpl.
      reflexivity. }
  Qed.

  Theorem nonzeros_nil : nonzeros [] = [].
  Proof.
    reflexivity.
  Qed.

  Theorem nonzeros_length : forall l1 l2 : natlist,
      nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
  Proof.
    intros l1 l2.
    induction l1.
    { reflexivity. }
    { rewrite -> app_n.
      rewrite -> nonzeros_n.
      rewrite -> nonzeros_n.
      rewrite -> nonzeros_nil.
      rewrite -> app_nil_end.
      rewrite -> IHl1.
      replace (nonzeros (n :: l1)) with (nonzeros [n] ++ nonzeros l1).
      rewrite -> app_ass.
      reflexivity.
      { rewrite <- nonzeros_n.
        reflexivity. } }
  Qed.

  Theorem count_member_nonzero : forall (s:bag),
      ble_nat 1 (count 1 (1 :: s)) = true.
  Proof.
    intros n.
    reflexivity.
  Qed.

  Theorem rev_injective_p: forall (l1 l2 : natlist),
      l1 = l2 -> rev l1 = rev l2.
  Proof.
    intros l1 l2 H.
    { induction l1.
      { rewrite <- H.
        reflexivity. }
      { rewrite -> H.
        reflexivity. } }
  Qed.

  Theorem rev_nil : rev [] = [].
  Proof.
    reflexivity.
  Qed.

  Theorem rev_injective: forall (l1 l2 : natlist),
      rev l1 = rev l2 -> l1 = l2.
  Proof.
    intros l1 l2 H.
    induction l1.
    { apply rev_injective_p in H.
      rewrite <- rev_involutive.
      replace ([]) with (rev (rev [])).
      apply H.
      { rewrite -> rev_involutive.
        reflexivity. } }
    { rewrite <- rev_involutive.
      replace (n :: l1) with (rev (rev (n :: l1))).
      rewrite -> H.
      reflexivity.
      { rewrite -> rev_involutive.
        reflexivity. } }
  Qed.

  Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

  Fixpoint index (n:nat) (l:natlist) : natoption :=
    match l with
    | nil => None
    | a :: l' => match beq_nat n O with
                 | true => Some a
                 | false => index (pred n) l'
                 end
    end.

  Fixpoint index' (n:nat) (l:natlist) : natoption :=
    match l with
    | nil => None
    | a :: l' => if beq_nat n O then Some a else index (pred n) l'
    end.

  Definition option_elim (o:natoption) (d:nat) :=
    match o with
    | Some n' => n'
    | None => d
    end.

  Definition hd_opt (l:natlist) : natoption :=
    match l with
    | nil => None
    | h :: t => Some h
    end.

  Theorem option_elim_hd: forall (l:natlist) (default:nat),
      hd default l = option_elim (hd_opt l) default.
  Proof.
    intros l default.
    induction l.
    { reflexivity. }
    { simpl.
      reflexivity. }
  Qed.

  Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
    match l1, l2 with
    | nil, nil => true
    | nil, _ => false
    | _ , nil => false
    | h1 :: t1, h2 :: t2 =>
      if beq_nat h1 h2 then beq_natlist t1 t2 else false
    end.

  Example test_beq_natlist1: (beq_natlist nil nil = true).
  Proof. reflexivity. Qed.
  Example test_beq_natlist2: (beq_natlist [1, 2, 3] [1, 2, 3] = true).
  Proof. reflexivity. Qed.
  Example test_beq_natlist3: (beq_natlist [1, 2, 3] [1, 2, 4] = false).
  Proof. reflexivity. Qed.

  Theorem beq_natlist_refl: forall l:natlist,
      true = beq_natlist l l.
  Proof.
    intros l.
    induction l.
    { reflexivity. }
    { simpl.
      rewrite <- IHl.
      rewrite <- beq_nat_refl.
      reflexivity. }
  Qed.

  Theorem silly1 : forall (n m o p : nat),
      n = m ->
      [n, o] = [n, p] ->
      [n, o] = [m, p].
  Proof.
    intros n m o p eq1 eq2.
    rewrite <- eq1.
    apply eq2.
  Qed.

  Theorem silly2 : forall (n m o p : nat),
      n = m ->
      (forall (q r : nat), q = r -> [q, o] = [r, p]) ->
      [n, o] = [m, p].
  Proof.
    intros n m o p eq1 eq2.
    apply eq2.
    apply eq1.
  Qed.

  Theorem silly2a: forall (n m : nat),
      (n, n) = (m, m) ->
      (forall (q r : nat), (q, q) = (r, r) -> [q] = [r]) ->
      [n] = [m].
  Proof.
    intros n m eq1 eq2.
    apply eq2.
    apply eq1.
  Qed.

  Theorem silly3: forall (n : nat),
      true = beq_nat n 5 ->
      beq_nat (S (S n)) 7 = true.
  Proof.
    intros n H.
    symmetry.
    simpl.
    apply H.
  Qed.

  Theorem rev_exercise1 : forall (l l' : natlist),
      l = rev l' -> l' = rev l.
  Proof.
    intros l l' H.
    rewrite -> H.
    rewrite -> rev_involutive.
    reflexivity.
  Qed.

  Theorem app_ass' : forall l1 l2 l3 : natlist,
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros l1.
    induction l1 as [| n l1'].
    { intros l2 l3.
      reflexivity. }
    { intros l2 l3.
      simpl.
      rewrite -> IHl1'.
      reflexivity. }
  Qed.

  Theorem beq_nat_sym : forall (n m : nat),
      beq_nat n m = beq_nat m n.
  Proof.
    intros n.
    induction n as [| n'].
    { intros m.
      induction m.
      { reflexivity. }
      { reflexivity. } }
    { intros m.
      induction m.
      { reflexivity. }
      { apply IHn'. } }
  Qed.

End NatList.



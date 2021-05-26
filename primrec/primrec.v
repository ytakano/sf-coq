Require Import List.
Import ListNotations.

Definition succ (n:nat) : nat :=
  S n.

Definition proj (n:nat) (l:list nat) : nat :=
  nth n l O.

Fixpoint app_gs (gs:list ((list nat) -> nat)) (args:list nat) (l:list nat): (list nat) :=
  match gs with
  | h::t => app_gs t args ((h args)::l)
  | [] => rev l
  end.

Definition compose
           (f:(list nat) -> nat)
           (gs:list ((list nat) -> nat))
           (args:list nat)
  : nat :=
  f (app_gs gs args []).

Definition shift (n:nat): list nat :=
  [n].

Fixpoint recurse'
         (f:(list nat) -> nat) (* f(x1, ..., xn) *)
         (g:(list nat) -> nat) (* g(n, h(n, x1, ..., xn), x1, ..., xn) *)
         (x0:nat)
         (args:list nat) (* x1 ... xn *)
  : nat :=
  match x0 with
  | O => f args
  | S(n) => g (n :: (recurse' f g n args) :: args)
  end.

Definition recurse
           (f:(list nat) -> nat) (* f(x1, ..., xn) *)
           (g:(list nat) -> nat) (* g(n, h(n, x1, ..., xn), x1, ..., xn) *)
           (args:list nat) (* x0 ... xn *)
  : nat :=
  match args with
  | h::t => recurse' f g h t
  | [] => O
  end.

(* Sort: Insertion sort *)

(** The insertion-sort program **)

Require Import Lists.List Bool OrdType.

Module InsertionSort (O : OrdType.OrdType).

  Import ListNotations.

  Fixpoint le_list x (l : list O.t) :=
    match l with
    | [] => true
    | y :: l' => (O.leb x y) && le_list x l'
    end.

  Fixpoint is_sorted (l : list O.t) :=
    match l with
    | [] => true
    | h :: l' => le_list h l' && is_sorted l'
    end.

  Fixpoint insert (x:O.t) (l: list O.t) :=
    match l with
    | nil => x::nil
    | h::l' => if O.leb x h then x::h::l' else h :: insert x l'
    end.

  Fixpoint sort (l: list O.t) : list O.t :=
    match l with
    | nil => nil
    | h::l' => insert h (sort l')
    end.

  (** Specification of correctness **)
  Inductive sorted: list O.t -> Prop :=
  | sorted_nil : sorted nil
  | sorted_1   : forall x,  sorted (x::nil)
  | sorted_cons: forall x y l, O.le x y -> sorted (y::l) -> sorted (x::y::l).

  Hint Constructors sorted.

  Axiom sorted_is_sorted : forall l, is_sorted l = true <-> sorted l.

  Definition is_a_sorting_algorithm (f: list O.t -> list O.t) :=
    forall al, (forall x, count_occ x al = count_occ x (f al)) /\ sorted (f al).

(** Proof of correctness **)

  Lemma insert_sorted: forall a l, sorted l -> sorted (insert a l).
  Proof.
    intros.
    induction H.
    simpl. auto.

    simpl. destruct (O.leb a x) eqn:e. constructor. apply O.leb_le. exact e.
    constructor.
    constructor. apply O.le_lteq. left. apply O.not_le_to_lt. apply O.leb_false_not_le. exact e.

    constructor.

    simpl. destruct (O.leb a x) eqn:e; intuition.
    constructor. apply O.leb_le. exact e. intuition.
    destruct (O.leb a y) eqn:e0; intuition.

    constructor. apply O.le_lteq. left. apply O.not_le_to_lt. apply O.leb_false_not_le. exact e.
    constructor. apply O.leb_le. exact e0.
    exact H0.

    constructor. exact H.

    simpl in IHsorted. destruct (O.leb a y) eqn:e1; intuition. discriminate e0.
  Qed.

  Theorem sort_sorted: forall l, sorted (sort l).
  Proof.
    intros.
    induction l; auto.
    simpl. apply insert_sorted. assumption.
  Qed.

  Axiom sort_is_sorted : forall l, is_sorted (sort l) = true.

  Axiom insertion_sort_correct:  is_a_sorting_algorithm sort.
(*
  Proof.
    split. apply sort_perm. apply sort_sorted.
  Qed.
 *)

End InsertionSort.
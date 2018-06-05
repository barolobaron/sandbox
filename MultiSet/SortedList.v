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

  Definition is_a_sorting_algorithm (f: list O.t -> list O.t) :=
    forall al, (forall x, count_occ O.eq_dec al x = count_occ O.eq_dec (f al) x) /\ sorted (f al).

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

  Lemma le_le_list a t l : O.leb a t = true -> le_list t l = true -> le_list a l = true.
  Proof.
    intro. elim l; intuition.
    simpl. simpl in H1. apply andb_true_iff; split.
    + apply O.leb_le. apply (O.le_trans _ t). apply O.leb_le. exact H.
      apply O.leb_le. destruct (O.leb t a0); intuition.
    + apply H0. rewrite andb_comm in H1. destruct (le_list t l0); intuition.
  Qed.

  Lemma sorted_is_sorted : forall l, is_sorted l = true <-> sorted l.
  Proof.
    intros. elim l.
    + intuition.
    + intros. simpl. destruct l0.
      - intuition.
      - split.
        * intro. constructor.
          ++ simpl in H0. apply O.leb_le. destruct (O.leb a t); intuition.
          ++ apply H. rewrite andb_comm in H0. destruct (is_sorted (t::l0)); intuition.
        * intro. simpl. inversion H0. subst. apply andb_true_iff. split.
          ++ apply andb_true_iff. split.
            -- apply O.leb_le. exact H3.
            -- apply (le_le_list _ t). apply O.leb_le. exact H3.
               simpl in H. destruct (le_list t l0); intuition.
          ++ apply H. exact H5.
  Qed.

  Lemma sort_is_sorted : forall l, is_sorted (sort l) = true.
  Proof.
    intros. apply sorted_is_sorted. apply sort_sorted.
  Qed.

  Lemma count_occ_insert_eq x bl :
    count_occ O.eq_dec (insert x bl) x = S (count_occ O.eq_dec bl x).
  Proof.
    elim bl; intuition.
    + simpl. destruct (O.eq_dec x x); intuition.
    + simpl. destruct (O.leb x a); simpl; intuition.
      - destruct (O.eq_dec x x); intuition.
      - destruct (O.eq_dec a x); intuition.
  Qed.

  Lemma count_occ_insert_neq x y bl : x <> y ->
    count_occ O.eq_dec (insert x bl) y = count_occ O.eq_dec bl y.
  Proof.
    intro. elim bl; intuition.
    + simpl. destruct (O.eq_dec x y); intuition.
    + simpl. destruct (O.leb x a); simpl; intuition.
      - destruct (O.eq_dec x y); intuition.
      - destruct (O.eq_dec a y); intuition.
  Qed.

  Lemma count_occ_insert : forall al bl x y, 
    count_occ O.eq_dec al x = count_occ O.eq_dec bl x ->
    count_occ O.eq_dec (y::al) x = count_occ O.eq_dec (insert y bl) x.
  Proof.
    intros. simpl. destruct (O.eq_dec y x).
    - rewrite e. rewrite count_occ_insert_eq. rewrite H. reflexivity.
    - erewrite count_occ_insert_neq; auto.
  Qed.

  Lemma count_occ_sort : forall al x, count_occ O.eq_dec al x = count_occ O.eq_dec (sort al) x.
  Proof.
    intros. elim al; intuition.
    simpl (sort (a::l)). apply count_occ_insert. apply H.
  Qed.

  Theorem insertion_sort_correct:  is_a_sorting_algorithm sort.
  Proof.
    split.
    + intro. apply count_occ_sort.
    + apply sort_sorted.
  Qed.

  Lemma lt_sorted_count_occ_O a b l:
    O.lt a b -> sorted (b::l) -> count_occ O.eq_dec (b::l) a = O.
  Proof.
    intros. generalize b H H0. clear b H H0. induction l; intros.
    + simpl. destruct (O.eq_dec b a); intuition. 
      rewrite e in H. destruct (O.lt_norefl _ H).
    + inversion H0; intuition. simpl.
      destruct (O.eq_dec b a); intuition.
      - rewrite e in H. destruct (O.lt_norefl _ H).
      - eapply (IHl a0).
        * destruct (proj1 (O.le_lteq b a0) H3).
          ++ apply (O.lt_trans _ _ _ H). exact H6.
          ++ rewrite <- H6. exact H.
        * exact H5.
  Qed.

  Theorem ext_eq al bl : 
    sorted al -> sorted bl -> 
    (forall x, count_occ O.eq_dec al x = count_occ O.eq_dec bl x) ->
    al = bl.
  Proof.
    intros. generalize bl H0 H1. clear bl H0 H1. induction al; intros.

    destruct bl; intuition. absurd (count_occ O.eq_dec [] t = count_occ O.eq_dec (t::bl) t).
    simpl. destruct (O.eq_dec t t); intuition. discriminate H2.
    apply H1.

    destruct bl; intuition. absurd (count_occ O.eq_dec (a::al) a = count_occ O.eq_dec [] a).
    simpl. destruct (O.eq_dec a a); intuition. discriminate H2.
    apply H1.

    destruct (O.linearity a t).
    + subst. f_equal. assert (sorted al). inversion H; intuition.
      assert (sorted bl). inversion H0; intuition.
      apply IHal; intuition.
      pose (H1' := H1 x); clearbody H1'. simpl in H1'. destruct (O.eq_dec t x); intuition.
    + destruct H2.
      - absurd (count_occ O.eq_dec (a::al) a = count_occ O.eq_dec (t::bl) a).
        * rewrite (lt_sorted_count_occ_O _ _ _ H2 H0). simpl.
          destruct (O.eq_dec a a); intuition. discriminate H3.
        * apply H1.
      - absurd (count_occ O.eq_dec (a::al) t = count_occ O.eq_dec (t::bl) t).
        * rewrite (lt_sorted_count_occ_O _ _ _ H2 H). simpl.
          destruct (O.eq_dec t t); intuition. discriminate H3.
        * apply H1.
  Qed.

End InsertionSort.

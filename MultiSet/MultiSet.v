Require Import Lists.List OrdType Bool SortedList JMeq Omega.

Notation " x ~= y " := (@JMeq _ x _ y) (at level 70, no associativity).

Lemma eq_JMeq {A} {x y : A} (H : x = y) : x ~= y.
Proof.
  rewrite H. reflexivity.
Qed.


Module MultiSet (O : OrdType.OrdType).
  Module S := InsertionSort O.
  Import S.

  (* the type of sets *)
  Definition t := { l : list O.t & is_sorted l = true }.

  (* some basic list operations *)
  Definition list_minus : list O.t -> list O.t -> list O.t
    := fun l1 l2 => 
      let l := nodup O.eq_dec (l1 ++ l2) in
      fold_left (fun acc x => acc ++ repeat x (count_occ O.eq_dec l1 x - count_occ O.eq_dec l2 x)) l List.nil.
  Definition list_inter : list O.t -> list O.t -> list O.t
    := fun l1 l2 => 
      let l := nodup O.eq_dec (l1 ++ l2) in
      fold_left (fun acc x => acc ++ repeat x (min (count_occ O.eq_dec l1 x) (count_occ O.eq_dec l2 x))) l List.nil.

  (* multiset operations *)
  Definition memb   : O.t -> t -> nat
    := fun x A => List.count_occ O.eq_dec (projT1 A) x.
  Definition plus   : t -> t -> t
    := fun A B => existT _ (sort (projT1 A ++ projT1 B)) (sort_is_sorted _).
  Definition minus   : t -> t -> t
    := fun A B => 
      let l := nodup O.eq_dec (projT1 A ++ projT1 B) in
      let l' := fold_left (fun acc x => acc ++ repeat x (min (memb x A) (memb x B))) l List.nil in
      existT _ (sort (list_minus (projT1 A) (projT1 B))) (sort_is_sorted _).
  Definition inter   : t -> t -> t
    := fun A B => 
      let l := nodup O.eq_dec (projT1 A ++ projT1 B) in
      let l' := fold_left (fun acc x => acc ++ repeat x (min (memb x A) (memb x B))) l List.nil in
      existT _ (sort (list_inter (projT1 A) (projT1 B))) (sort_is_sorted _).
  Definition set_of  : t -> t
    := fun A => existT _ (sort (nodup O.eq_dec (projT1 A))) (sort_is_sorted _).
  Definition of_list : list O.t -> t
    := fun l => existT _ (sort l) (sort_is_sorted _).

  (* auxiliary lemma *)
  Lemma existT_eq A (f : A -> Type) x x' e e' : x ~= x' -> e ~= e' -> existT f x e ~= existT f x' e'.
  Proof.
    intro. generalize e; clear e. rewrite H. intros. rewrite H0. reflexivity.
  Qed.

  (***********************************************************************************************)
  (* PROPERTIES *)

  (* extensional equality *)
  Lemma p_ext : forall A B, (forall t, memb t A = memb t B) -> A = B.
  Proof.
    intros. destruct A. destruct B. unfold memb in H. simpl in H.

    assert (x = x0). 
    apply ext_eq. apply sorted_is_sorted; assumption. apply sorted_is_sorted; assumption. exact H.

    generalize e; clear e. rewrite H0. intros. f_equal.
    destruct e. apply JMeq_eq. destruct e0. reflexivity.
  Qed.

  (* some basic properties of count_occ *)
  Lemma count_occ_repeat x n : count_occ O.eq_dec (repeat x n) x = n.
  Proof.
    induction n; simpl; intuition. destruct (O.eq_dec x x); intuition.
  Qed.

  Lemma count_occ_repeat_neq x y n : x <> y -> count_occ O.eq_dec (repeat x n) y = 0.
  Proof.
    intro. induction n; simpl; intuition. destruct (O.eq_dec x y); intuition.
  Qed.

  Lemma count_occ_app l1 l2 x :
    count_occ O.eq_dec (l1 ++ l2) x = count_occ O.eq_dec l1 x + count_occ O.eq_dec l2 x.
  Proof.
    induction l1; intuition.
    simpl. destruct (O.eq_dec a x); intuition.
  Qed.

  Lemma count_occ_fold l1 l2 f l:
    forall acc, NoDup l -> 
    (forall x, (0 < count_occ O.eq_dec l1 x \/ 0 < count_occ O.eq_dec l2 x) -> count_occ O.eq_dec l x = 0 -> count_occ O.eq_dec acc x = f x) ->
    (forall x, (0 < count_occ O.eq_dec l1 x \/ 0 < count_occ O.eq_dec l2 x) -> 0 < count_occ O.eq_dec l x -> count_occ O.eq_dec acc x = 0) ->
    forall x, (0 < count_occ O.eq_dec l1 x \/ 0 < count_occ O.eq_dec l2 x) ->
              count_occ O.eq_dec (fold_left (fun acc' y => acc' ++ repeat y (f y)) l acc) x = f x.
  Proof.
    induction l; intuition.
    + simpl. apply IHl.
      - inversion H; assumption.
      - intros. destruct (O.eq_dec a x0). 
        rewrite e. rewrite count_occ_app. rewrite H1. simpl. rewrite count_occ_repeat. reflexivity.
        exact H2. rewrite e. simpl. destruct (O.eq_dec x0 x0); intuition.
        rewrite count_occ_app. rewrite H0. rewrite count_occ_repeat_neq. omega. exact n.
        exact H2. simpl. destruct (O.eq_dec a x0); intuition.
      - intros. enough (a <> x0).
        rewrite count_occ_app. rewrite H1. rewrite count_occ_repeat_neq. reflexivity. exact H5.
        exact H2. simpl. destruct (O.eq_dec a x0); intuition.
        inversion H. intro. apply H7. rewrite H9. eapply count_occ_In. exact H4.
      - left. exact H3.
    + simpl. apply IHl.
      - inversion H; assumption.
      - intros. destruct (O.eq_dec a x0). 
        rewrite e. rewrite count_occ_app. rewrite H1. simpl. rewrite count_occ_repeat. reflexivity.
        exact H2. rewrite e. simpl. destruct (O.eq_dec x0 x0); intuition.
        rewrite count_occ_app. rewrite H0. rewrite count_occ_repeat_neq. omega. exact n.
        exact H2. simpl. destruct (O.eq_dec a x0); intuition.
      - intros. enough (a <> x0).
        rewrite count_occ_app. rewrite H1. rewrite count_occ_repeat_neq. reflexivity. exact H5.
        exact H2. simpl. destruct (O.eq_dec a x0); intuition.
        inversion H. intro. apply H7. rewrite H9. eapply count_occ_In. exact H4.
      - right. exact H3.
  Qed.

  Lemma count_occ_fold' f l:
    forall acc,
    forall x, count_occ O.eq_dec l x = 0 -> count_occ O.eq_dec acc x = 0 ->
              count_occ O.eq_dec (fold_left (fun acc' y => acc' ++ repeat y (f y)) l acc) x = 0.
  Proof.
    induction l; intuition. simpl.
    apply IHl. simpl in H. destruct (O.eq_dec a x); intuition.
    rewrite count_occ_app. rewrite H0. rewrite count_occ_repeat_neq. reflexivity.
    simpl in H. destruct (O.eq_dec a x); intuition.
  Qed.

  Lemma or_eq_lt_n_O n : n = 0 \/ 0 < n.
  Proof.
    destruct (Nat.eq_dec n 0); intuition.
  Qed.

  Lemma count_occ_nodup l x : count_occ O.eq_dec (nodup O.eq_dec l) x = 1 <-> 0 < count_occ O.eq_dec l x.
  Proof.
    induction l; intuition.
    + simpl in H. discriminate H.
    + simpl in H1. destruct (in_dec O.eq_dec a l); intuition.
      simpl. destruct (O.eq_dec a x); intuition.
      simpl in H1. simpl. destruct (O.eq_dec a x); intuition.
    + simpl. destruct (in_dec O.eq_dec a l); intuition.
      apply H0. simpl in H1. destruct (O.eq_dec a x); intuition.
      rewrite <- e. apply count_occ_In. exact i.
      simpl. simpl in H1. destruct (O.eq_dec a x); intuition.
      f_equal. apply count_occ_not_In. intro. apply n.
      rewrite e. eapply nodup_In. exact H2.
  Qed.

  Lemma count_occ_nodup_O l x : count_occ O.eq_dec (nodup O.eq_dec l) x = 0 <-> count_occ O.eq_dec l x = 0.
  Proof.
    induction l; intuition.
    + simpl in H1. destruct (in_dec O.eq_dec a l); intuition.
      enough (count_occ O.eq_dec (nodup O.eq_dec l) a = 1).
      simpl. destruct (O.eq_dec a x); intuition. rewrite e in H0. rewrite H0 in H. discriminate H.
      apply NoDup_count_occ'. apply NoDup_nodup. apply nodup_In. exact i.
      simpl in H1. simpl. destruct (O.eq_dec a x); intuition.
    + simpl. destruct (in_dec O.eq_dec a l); intuition.
      simpl in H1. destruct (O.eq_dec a x); intuition.
      simpl. simpl in H1. destruct (O.eq_dec a x); intuition.
  Qed.

  (* properties of list_minus and list_inter *)
  Lemma count_occ_list_minus l1 l2 :
    forall x, count_occ O.eq_dec (list_minus l1 l2) x
      = count_occ O.eq_dec l1 x - count_occ O.eq_dec l2 x.
  Proof.
    intro. unfold list_minus. 
    destruct (or_eq_lt_n_O (count_occ O.eq_dec l1 x)).
    destruct (or_eq_lt_n_O (count_occ O.eq_dec l2 x)).
    rewrite H, H0. apply count_occ_fold'. apply count_occ_nodup_O.
    rewrite count_occ_app. rewrite H, H0. reflexivity.
    reflexivity.

    eapply (count_occ_fold l1 l2 (fun y => count_occ O.eq_dec l1 y - count_occ O.eq_dec l2 y)).
    apply NoDup_nodup. intros.
    pose (H3 := proj1 (count_occ_nodup_O _ _) H2); clearbody H3.
    rewrite count_occ_app in H3. destruct (count_occ O.eq_dec l1 x0); intuition.
    intros. reflexivity.
    right. exact H0.

    eapply (count_occ_fold l1 l2 (fun y => count_occ O.eq_dec l1 y - count_occ O.eq_dec l2 y)).
    apply NoDup_nodup. intros.
    pose (H2 := proj1 (count_occ_nodup_O _ _) H1); clearbody H2.
    rewrite count_occ_app in H2. destruct (count_occ O.eq_dec l1 x0); intuition.
    intros. reflexivity.
    left. exact H.
  Qed.

  Lemma count_occ_list_inter l1 l2 :
    forall x, count_occ O.eq_dec (list_inter l1 l2) x
      = min (count_occ O.eq_dec l1 x) (count_occ O.eq_dec l2 x).
  Proof.
    intro. unfold list_inter. 
    destruct (or_eq_lt_n_O (count_occ O.eq_dec l1 x)).
    destruct (or_eq_lt_n_O (count_occ O.eq_dec l2 x)).
    rewrite H, H0. apply count_occ_fold'. apply count_occ_nodup_O.
    rewrite count_occ_app. rewrite H, H0. reflexivity.
    reflexivity.

    eapply (count_occ_fold l1 l2 (fun y => min (count_occ O.eq_dec l1 y) (count_occ O.eq_dec l2 y))).
    apply NoDup_nodup. intros.
    pose (H3 := proj1 (count_occ_nodup_O _ _) H2); clearbody H3.
    rewrite count_occ_app in H3. destruct (count_occ O.eq_dec l1 x0); intuition.
    intros. reflexivity.
    right. exact H0.

    eapply (count_occ_fold l1 l2 (fun y => min (count_occ O.eq_dec l1 y) (count_occ O.eq_dec l2 y))).
    apply NoDup_nodup. intros.
    pose (H2 := proj1 (count_occ_nodup_O _ _) H1); clearbody H2.
    rewrite count_occ_app in H2. destruct (count_occ O.eq_dec l1 x0); intuition.
    intros. reflexivity.
    left. exact H.
  Qed.

  (* property of disjoint union multisets *)
  Lemma p_plus : forall A B, forall t, memb t (plus A B) = memb t A + memb t B.
  Proof.
    intros. destruct A. destruct B. unfold memb. simpl.
    rewrite <- count_occ_sort. apply count_occ_app.
  Qed.

  (* property of difference multisets *)
  Lemma p_minus : forall A B, forall t, memb t (minus A B) = memb t A - memb t B.
  Proof.
    intros A B x. destruct A. destruct B. unfold memb; simpl.
    rewrite <- count_occ_sort. apply count_occ_list_minus.
  Qed.

  (* property of intersection multisets *)
  Lemma p_inter : forall A B, forall t, memb t (inter A B) = min (memb t A) (memb t B).
  Proof.
    intros A B x. destruct A. destruct B. unfold memb; simpl.
    rewrite <- count_occ_sort. apply count_occ_list_inter.
  Qed.

  (* property of multiset flattening *)
  Lemma p_set_of : forall A, forall t, 0 < memb t A <-> memb t (set_of A) = 1.
  Proof.
    intros A x. destruct A. unfold memb. unfold set_of. simpl. split; intro.
    rewrite <- count_occ_sort. apply NoDup_count_occ'. apply NoDup_nodup.
    apply nodup_In. eapply count_occ_In. exact H.
    rewrite <- count_occ_sort in H. apply count_occ_nodup. exact H.
  Qed.

End MultiSet.

Require Import Lists.List OrdType Bool SortedList.

Module MultiSet (O : OrdType.OrdType).
  Module S := InsertionSort O.
  Import S.

  Definition t := { l : list O.t & is_sorted l = true }.

  Print Orders.OrderedTypeFull.

  (* multiset operations *)
  Definition memb   : O.t -> t -> nat
    := fun x A => List.count_occ O.eq_dec (projT1 A) x.
  Definition plus   : t -> t -> t
    := fun A B => existT _ (sort (projT1 A ++ projT1 B)) (sort_is_sorted _).
  Parameter minus   : t -> t -> t.
  Parameter inter   : t -> t -> t.
  Parameter set_of  : t -> t.
  Parameter of_list : list O.t -> t.


  (* properties *)
  Parameter p_ext : forall A B, (forall t, memb t A = memb t B) -> A = B.
  Parameter p_plus : forall A B, forall t, memb t (plus A B) = memb t A + memb t B.
  Parameter p_minus : forall A B, forall t, memb t (minus A B) = memb t A - memb t B.
  Parameter p_inter : forall A B, forall t, memb t (inter A B) = min (memb t A) (memb t B).
  Parameter p_set_of : forall A, forall t, 0 < memb t A <-> memb t (set_of A) = 1.

End MultiSet.
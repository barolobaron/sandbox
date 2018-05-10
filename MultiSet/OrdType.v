Require Import Lists.List Sorted Bool.

Module Type OrdType.

  Parameter t : Type.
  Parameter le : t -> t -> Prop.
  Parameter lt : t -> t -> Prop.
  Parameter leb : t -> t -> bool.
  Parameter ltb : t -> t -> bool.

  Parameter eq_dec : forall (x y:t), {x = y} + {x <> y}.

  Parameter le_refl : forall x, le x x.
  Parameter le_antisym : forall x y, le x y -> le y x -> x = y.
  Parameter le_trans : forall x y z, le x y -> le y z -> le x z.

  Parameter lt_norefl : forall x, ~ lt x x.
  Parameter lt_antisym : forall x y, lt x y -> lt y x -> False.
  Parameter lt_trans : forall x y z, lt x y -> lt y z -> lt x z.

  Parameter not_le_to_lt : forall x y, ~ le x y -> lt y x.
  Parameter not_lt_to_le : forall x y, ~ lt x y -> le y x.

  Parameter leb_le : forall x y, leb x y = true <-> le x y.
  Parameter le_lteq : forall x y, le x y <-> lt x y \/ x = y.

  Parameter leb_false_not_le : forall x y, leb x y = false <-> ~ le x y.
  (*
  Proof.
    intuition.
    * assert (leb x y = true). apply leb_le. exact H0. rewrite H1 in H. discriminate H.
    * destruct (leb x y) eqn:e; intuition. contradiction H. apply leb_le. exact e.
  Qed.
  *)

End OrdType.
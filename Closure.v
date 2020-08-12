Set Implicit Arguments.

Section TRC.
  Variable A : Type.
  Variable R : A -> A -> Prop.

  Inductive trc : A -> A -> Prop :=
  | TrcRefl : forall a, trc a a
  | TrcFront : forall a b c, R a b -> trc b c -> trc a c.
  Hint Constructors trc : trc.

  Lemma trc_trans : forall a a' a'',
      trc a a' -> trc a' a'' -> trc a a''.
  Proof with eauto with trc.
    induction 1...
  Qed.
End TRC.

Global Hint Constructors trc : trc.
Global Hint Resolve trc_trans : trc.

Require Import Arith Bool Strings.String.

Require Import Lib.

Set Default Goal Selector "!".
Set Implicit Arguments.

Open Scope list_scope.

Module Type VMAP.
  Parameter t : Set.

  Parameter empty : t.
  Parameter get_var : t -> string -> option nat.
  Parameter set_var : t -> string -> nat -> t.
  Parameter list_defs : t -> list string.

  Axiom get_empty : forall v, get_var empty v = None.
  Axiom get_set_same : forall v n t, get_var (set_var t v n) v = Some n.
  Axiom get_set_other : forall v1 v2 n t, v1 <> v2 -> get_var (set_var t v1 n) v2 = get_var t v2.
  Axiom list_defs_ok : forall v t, List.In v (list_defs t) -> exists n, get_var t v = Some n.
  Axiom list_defs_complete : forall v t n, get_var t v = Some n -> List.In v (list_defs t).
  Axiom list_defs_set : forall v t n, List.In v (list_defs (set_var t v n)).
  Axiom list_defs_set_preserve : forall v t s n, List.In v (list_defs t) -> List.In v (list_defs (set_var t s n)).
End VMAP.

Module VMAP_Notation(vmap : VMAP).
  Notation "∅" := vmap.empty (at level 0) : vmap_scope.
  Notation "M [ v ↦ n ]" := (vmap.set_var M v n) (at level 50, left associativity) : vmap_scope.
  Notation "M [ v ]" := (vmap.get_var M v) (at level 50, left associativity) : vmap_scope.
End VMAP_Notation.

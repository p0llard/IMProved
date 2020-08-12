Require Import Arith String.

Require Import Lib VMAPs.

Set Default Goal Selector "!".
Set Implicit Arguments.

Module Type EXPR_DSL(vmap : VMAP).
  Parameter arith : Set.
  Parameter denote_arith : arith -> vmap.t -> option nat.
  (* Parameter check_arith : list string -> arith -> bool. *)
  (* Axiom check_arith_ok : forall m l, *)
  (*    l = vmap.list_defs m -> *)
  (*    (forall e, check_arith l e = true -> exists n, denote_arith e m = Some n). *)
  (* Axiom check_arith_monotone : forall e l l', *)
  (*    (forall s, List.In s l -> List.In s l') -> *)
  (*    check_arith l e = true -> check_arith l' e = true. *)

  Parameter bool' : Set.
  Parameter denote_bool' : bool' -> vmap.t -> option bool.
  (* Parameter check_bool' : list string -> bool' -> bool. *)
  (* Axiom check_bool'_ok : forall m l, *)
  (*    l = vmap.list_defs m -> *)
  (*    (forall e, check_bool' l e = true -> exists n, denote_bool' e m = Some n). *)
  (* Axiom check_bool'_monotone : forall b l l', *)
  (*    (forall s, List.In s l -> List.In s l') -> *)
  (*    check_bool' l b = true -> check_bool' l' b = true. *)

  Module Coercions. End Coercions.
End EXPR_DSL.

Module EXPR_DSL_Notation(vmap : VMAP) (expr_dsl : EXPR_DSL(vmap)).
  Notation "A⟦ e ⟧ ( m )" := (expr_dsl.denote_arith e m) (at level 50, left associativity) : dsl_scope.
  Notation "B⟦ e ⟧ ( m )" := (expr_dsl.denote_bool' e m) (at level 50, left associativity) : dsl_scope.
End EXPR_DSL_Notation.


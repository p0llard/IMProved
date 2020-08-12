Require Import Arith Bool String.

Infix "==s" := string_dec (no associativity, at level 50).
Infix "==nat" := eq_nat_dec (no associativity, at level 50).
Infix "<nat" := le_gt_dec (no associativity, at level 50).

Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).

Ltac invert x := inversion x; subst; clear x.

(* This tactic due to Clement Pit-Claudel with some minor additions by JDP to
   allow the result to be named: https://pit-claudel.fr/clement/MSc/#org96a1b5f *)
Inductive Learnt {A: Type} (a: A) :=
| AlreadyKnown : Learnt a.

Ltac learn_tac fact name :=
  lazymatch goal with
  | [ H: Learnt fact |- _ ] =>
    fail 0 "fact" fact "has already been learnt"
  | _ => let type := type of fact in
        lazymatch goal with
        | [ H: @Learnt type _ |- _ ] =>
          fail 0 "fact" fact "of type" type "was already learnt through" H
        | _ => let learnt := fresh "Learn" in
              pose proof (AlreadyKnown fact) as learnt; pose proof fact as name
        end
  end.

Tactic Notation "learn" constr(fact) := let name := fresh "H" in learn_tac fact name.
Tactic Notation "learn" constr(fact) "as" simple_intropattern(name) := learn_tac fact name.

Ltac nicify_hypotheses :=
  repeat match goal with
         | [ H : ex _ |- _ ] => invert H
         | [ H : Some _ = Some _ |- _ ] => invert H
         | [ H : ?x = ?x |- _ ] => clear H
         | [ H : ?x = ?x -> _ |- _ ] => assert (x = x) as ?EQ by reflexivity; apply H in EQ; clear H
         | [ H : _ /\ _ |- _ ] => invert H
         end.

Ltac nicify_goals :=
  repeat match goal with
         | [ |- _ /\ _ ] => split
         | [ |- Some _ = Some _ ] => f_equal
         | [ |- S _ = S _ ] => f_equal
         end.

Ltac kill_bools :=
  repeat match goal with
         | [ H : _ && _ = true |- _ ] => apply andb_prop in H
         | [ H : _ || _ = false |- _ ] => apply orb_false_elim in H
         end.

Ltac substpp :=
  repeat match goal with
         | [ H1 : ?x = Some _, H2 : ?x = Some _ |- _ ] =>
           let EQ := fresh "EQ" in
           learn H1 as EQ; rewrite H2 in EQ; invert EQ
         | _ => idtac
         end.

Ltac simplify := intros; simpl in *;
                 repeat (nicify_hypotheses; nicify_goals; kill_bools; substpp);
                 simpl in *.

Ltac restrict x := destruct x; simplify; try discriminate; try congruence; eauto.

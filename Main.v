Require Import Arith Bool Strings.String.

Require Import IMProved Lib.

Set Default Goal Selector "!".
Set Implicit Arguments.

Open Scope list_scope.
Open Scope string_scope.

Import VeryInefficientListMap.

Module Import ImpExpr_Inefficient := ImpExpr(VeryInefficientListMap).
Import ImpExpr_Inefficient.Notation.

Module Import Imp_Inefficient := Imp(VeryInefficientListMap) (ImpExpr_Inefficient).
Import Imp_Inefficient.Notation.

Module Import expr_dsl_notation := EXPR_DSL_Notation(VeryInefficientListMap) (ImpExpr_Inefficient).
Module Import vmap_notation := VMAP_Notation(VeryInefficientListMap).

Open Scope dsl_scope.
Open Scope vmap_scope.

Module DenoteExamples.
  Example map := ∅["foo" ↦ 10]["bar" ↦ 20]["baz" ↦ 0].
  Compute A⟦"foo"⟧(map).
  Compute A⟦"bar"⟧(map).
  Compute A⟦"baz"⟧(map).
  Compute A⟦"bar" ⊕ "foo"⟧(map).
  Compute A⟦"bar" ⊖ "foo"⟧(map).
  Compute A⟦"bar" ⊗ "foo"⟧(map).
  Compute A⟦"bar" ⨸ "foo"⟧(map).

  Compute B⟦"foo"⟧(map).
  Compute B⟦"bar"⟧(map).
  Compute B⟦"baz"⟧(map).
  Compute B⟦"foo" == "bar"⟧(map).
  Compute B⟦"foo" == "foo"⟧(map).
End DenoteExamples.

Module StepExamples.
  Ltac stepper :=
    lazymatch goal with
    | |- {_, ?x} ⇝ {_, ?x} => eapply TrcRefl
    | |- {_, _} ⇝ {_, _} => eapply TrcFront; [> eapply Step |]
    end.

  Ltac strategy0 := eapply PlugPar1 || eapply PlugPar2 || eapply PlugSeq || eapply PlugHole.

  Ltac strategy :=
    repeat match goal with
           | |- plug _ _ (Skip; _) => eapply PlugHole
           | |- plug _ _ (Skip || _) => eapply PlugHole
           | |- plug _ _ _ => strategy0
           end.

  Ltac step0 :=
    match goal with
    | |- {_, _} ⤑ {_, _} => econstructor; reflexivity
    end.

  Ltac step := (solve stepper) || (stepper; [> strategy | step0 | strategy |]).

  Ltac run :=
    lazymatch goal with
    | |- sig (fun v => {_, _} ⇝ {v, Skip}) => eexists; [> repeat step]
    end.

  Example par_start_map := ∅["n" ↦ 1].
  Example par_prog :=
    ("a" ← "n"; "n" ← "a" ⊗ 2) || ("b" ← "n"; "n" ← "b" ⊗ 2).
  Example par_exec : ⟪par_prog | par_start_map⟫. run. Defined.
  (* Compute check_prog (VeryInefficientListMap.list_defs par_start_map) par_prog. *)
  Compute (proj1_sig par_exec)["a"].
  Compute (proj1_sig par_exec)["b"].

  Example factorial_start_map := ∅["input" ↦ 5].
  Example factorial_prog :=
    "output" ← 1;
    while "input" loop
        "output" ← "output" ⊗ "input";
        "input" ← "input" ⊖ 1
    done.
  (* Compute check_prog (VeryInefficientListMap.list_defs factorial_start_map) factorial_prog. *)
  Example factorial_exec : ⟪factorial_prog | factorial_start_map⟫. run. Defined.
  Compute (proj1_sig factorial_exec)["output"].

  Example test_start_map := ∅["input" ↦ 4].
  Example test_prog :=
    when "input" == 5 then
        "output" ← 1
    else
        "output" ← 0
    done.
  (* Compute check_prog (VeryInefficientListMap.list_defs test_start_map) test_prog. *)
  Example test_exec : ⟪test_prog | test_start_map⟫. run. Defined.
  Compute (proj1_sig test_exec)["output"].

  Example simple := "output" ← "input".
  Example simple_exec : ⟪simple | ∅⟫. run. Fail Defined. Abort.

  Lemma simple_exec_fails : ⟪simple | ∅⟫ -> False.
  Proof.
    intros.
    invert H. invert H0. invert H. invert H3.
    unfold simple in H4.
    invert H4.
    simplify. discriminate.
  Qed.
End StepExamples.

Section Analysis.
  Fixpoint check_arith (predef : list string) (a : arith) : bool :=
    match a with
    | Lit _ => true
    | Var s => if (List.in_dec string_dec s predef) then true else false
    | Plus a1 a2 => andb (check_arith predef a1) (check_arith predef a2)
    | Minus a1 a2 => andb (check_arith predef a1) (check_arith predef a2)
    | Mult a1 a2 => andb (check_arith predef a1) (check_arith predef a2)
    | Div a1 a2 => andb (check_arith predef a1) (check_arith predef a2)
    end.

  Lemma check_arith_ok : forall m l,
     l = list_defs m ->
     (forall e, check_arith l e = true -> exists n, denote_arith e m = Some n).
  Proof.
    intros. induction e; simplify; eauto.
    - destruct (List.in_dec string_dec s l); try congruence.
      apply list_defs_ok. congruence.
    - destruct (check_arith (list_defs m) e1);
        destruct (check_arith (list_defs m) e2);
        simplify; try congruence.
      rewrite H, H0. eauto.
    - apply IHe1 in H1. apply IHe2 in H2. simplify.
      rewrite H, H0. eauto.
    - apply IHe1 in H1. apply IHe2 in H2. simplify.
      rewrite H, H0. eauto.
    - apply IHe1 in H1. apply IHe2 in H2. simplify.
      rewrite H, H0. eauto.
  Qed.

  Lemma check_arith_monotone : forall e l l',
     (forall s, List.In s l -> List.In s l') ->
     check_arith l e = true -> check_arith l' e = true.
  Proof.
    induction e; simplify; eauto using andb_true_intro.
    restrict (List.in_dec string_dec s l).
    apply H in i.
    restrict (List.in_dec string_dec s l').
  Qed.

  Fixpoint check_bool' (predef : list string) (b : bool') : bool :=
    match b with
    | False' => true
    | True' => true
    | Arith a => check_arith predef a
    | Neg b => check_bool' predef b
    | Conj b1 b2 => andb (check_bool' predef b1) (check_bool' predef b2)
    | Disj b1 b2 => andb (check_bool' predef b1) (check_bool' predef b2)
    | Eq a1 a2 => andb (check_arith predef a1) (check_arith predef a2)
    | Lt a1 a2 => andb (check_arith predef a1) (check_arith predef a2)
    | Lte a1 a2 => andb (check_arith predef a1) (check_arith predef a2)
    | Gt a1 a2 => andb (check_arith predef a1) (check_arith predef a2)
    | Gte a1 a2 => andb (check_arith predef a1) (check_arith predef a2)
    end.

  Lemma check_bool'_ok : forall m l,
     l = list_defs m ->
     (forall e, check_bool' l e = true -> exists n, denote_bool' e m = Some n).
  Proof.
    intros. induction e; simplify; eauto.
    - eapply check_arith_ok in H0; [> simplify | exact H].
      rewrite H1. destruct (x <nat 0); eauto.
    - apply IHe in H0. simplify.
      rewrite H1. eauto.
    - apply IHe1 in H1. apply IHe2 in H2. simplify.
      rewrite H, H0. eauto.
    - apply IHe1 in H1. apply IHe2 in H2. simplify.
      rewrite H, H0. eauto.
    - eapply check_arith_ok in H1; [> simplify | reflexivity].
      eapply check_arith_ok in H2; [> simplify | reflexivity].
      rewrite H, H0. eauto.
    - eapply check_arith_ok in H1; [> simplify | reflexivity].
      eapply check_arith_ok in H2; [> simplify | reflexivity].
      rewrite H, H0. eauto.
    - eapply check_arith_ok in H1; [> simplify | reflexivity].
      eapply check_arith_ok in H2; [> simplify | reflexivity].
      rewrite H, H0. eauto.
    - eapply check_arith_ok in H1; [> simplify | reflexivity].
      eapply check_arith_ok in H2; [> simplify | reflexivity].
      rewrite H, H0. eauto.
    - eapply check_arith_ok in H1; [> simplify | reflexivity].
      eapply check_arith_ok in H2; [> simplify | reflexivity].
      rewrite H, H0. eauto.
  Qed.

  Lemma check_bool'_monotone : forall b l l',
     (forall s, List.In s l -> List.In s l') ->
     check_bool' l b = true -> check_bool' l' b = true.
  Proof.
    induction b; simplify; eauto using check_arith_monotone, andb_true_intro.
  Qed.

  Lemma step0_monotone : forall c1 c2 m1 m2,
     step0 (m1, c1) (m2, c2) ->
     (forall s, List.In s (list_defs m1) -> List.In s (list_defs m2)).
  Proof.
    induction c1; simplify; invert H; simplify; eauto using list_defs_set_preserve.
  Qed.

  Definition list_intersect (l1 l2 : list string) : list string :=
    (** if _ then true else false is OK in Coq, since if is more general *)
    List.filter (fun s => if List.in_dec (string_dec) s l2 then true else false) l1.

  Lemma list_intersect_sound : forall l1 l2 s,
      List.In s (list_intersect l1 l2) -> List.In s l1 /\ List.In s l2.
  Proof.
    intros. unfold list_intersect in H. split; intros.
    - eapply List.filter_In; eauto.
    - apply List.filter_In in H.
      invert H. restrict (List.in_dec string_dec s l2).
  Qed.

  Lemma list_intersect_intro : forall l1 l2 s,
      List.In s l1 /\ List.In s l2 -> List.In s (list_intersect l1 l2).
  Proof.
    intros. unfold list_intersect. invert H.
    apply List.filter_In. split; eauto.
    restrict (List.in_dec string_dec s l2).
  Qed.

  Fixpoint check_prog' (predef : list string) (p : cmd) : bool * list string :=
    match p with
    | Skip => (true, predef)
    | Assign dst src => (check_arith predef src, dst :: predef)
    | If cond then_ else_ => match (check_bool' predef cond,
                                   check_prog' predef then_,
                                   check_prog' predef else_) with
                            | (true, (true, predef'1), (true, predef'2)) =>
                              (true, list_intersect predef'1 predef'2)
                            | _ => (false, nil) (* no need to return anything useful *)
                            end
    | While cond body => match check_prog' predef body with
                        | (true, _) => (check_bool' predef cond, predef)
                        | _ => (false, nil) (* no need to return anything useful *)
                        end
    | Par p1 p2 => match (check_prog' predef p1) with
                  | (true, _) => check_prog' predef p2
                  | _ => (false, nil) (* no need to return anything useful *)
                  end
    | Seq c1 c2 => match (check_prog' predef c1) with
                  | (true, predef') => check_prog' predef' c2
                  | _ => (false, nil) (* no need to return anything useful *)
                  end
    end.

  Ltac squash := repeat match goal with
                        | [ H : context[if (check_bool' ?a ?b) then _ else _] |- _ ] =>
                          destruct (check_bool' a b) eqn:EQ; simplify; try discriminate
                        | [ H : context[let (_, _) := ?x in _] |- _ ] => destruct x
                        end.

  Lemma check_prog'_monotone : forall p l L,
     check_prog' l p = (true, L) ->
     forall l',
      (forall s, List.In s l -> List.In s l') ->
      forall L',
       check_prog' l' p = (true, L') ->
       (forall s, List.In s L -> List.In s L').
  Proof.
    induction p; simplify; invert H; invert H1; simplify; eauto.
    - invert H2; eauto.
    - destruct (check_bool' l' b) eqn:?EQ; simplify; try discriminate.
      destruct (check_prog' l' p1) eqn:?EQ. restrict b0.
      destruct (check_prog' l' p2) eqn:?EQ. restrict b0.
      invert H3.
      destruct (check_bool' l b) eqn:?EQ; simplify; try discriminate.
      destruct (check_prog' l p1) eqn:?EQ. restrict b0.
      destruct (check_prog' l p2) eqn:?EQ. restrict b0.
      invert H4.
      apply list_intersect_sound in H2.
      apply list_intersect_intro.
      simplify; eauto.
    - destruct (check_prog' l p) eqn:?EQ; simplify; try discriminate.
      destruct (check_prog' l' p) eqn:?EQ; simplify; try discriminate.
      restrict b0. restrict b1.
      invert H3. invert H4.
      eauto.
    - destruct (check_prog' l p1) eqn:?EQ; simplify; try discriminate.
      destruct (check_prog' l' p1) eqn:?EQ; simplify; try discriminate.
      restrict b. restrict b0.
    - destruct (check_prog' l p1) eqn:?EQ; simplify; try discriminate.
      destruct (check_prog' l' p1) eqn:?EQ; simplify; try discriminate.
      restrict b. restrict b0.
  Qed.
  Hint Resolve check_prog'_monotone : crush.

  Lemma check_prog'_monotone_ex : forall p l l' L,
     (forall s, List.In s l -> List.In s l') ->
     check_prog' l p = (true, L) ->
       exists L', check_prog' l' p = (true, L').
  Proof.
    induction p; simplify; try congruence; invert H0; simplify; eauto.
    - eexists; eauto.
      apply pair_equal_spec; split; eauto.
      eauto using check_arith_monotone.
    - destruct (check_bool' l b) eqn:?EQ; simplify; try discriminate.
      destruct (check_prog' l p1) eqn:?EQ. restrict b0.
      destruct (check_prog' l p2) eqn:?EQ. restrict b0.
      invert H2.
      pose proof (IHp1 _ _ _ H EQ0). invert H0.
      pose proof (IHp2 _ _ _ H EQ1). invert H0.
      pose proof (check_bool'_monotone _ _ _ H EQ).
      rewrite H0, H1, H2.
      eauto.
    - destruct (check_prog' l p) eqn:?EQ.
      restrict b0. invert H2.
      destruct (check_prog' l' p) eqn:?EQ.
      pose proof (check_bool'_monotone _ _ _ H H1). rewrite H0.
      assert (exists L, check_prog' l' p = (true, L)) by eauto.
      simplify. rewrite EQ0 in H3. invert H3. rewrite H1.
      eauto.
    - destruct (check_prog' l p1) eqn:?EQ; simplify.
      restrict b.
      pose proof (IHp1 _ _ _ H EQ). simplify.
      rewrite H1.
      eauto using check_prog'_monotone.
    - destruct (check_prog' l p1) eqn:?EQ; simplify.
      restrict b.
      pose proof (IHp1 _ _ _ H EQ). simplify.
      rewrite H1.
      eauto using check_prog'_monotone.
  Qed.
  Hint Resolve check_prog'_monotone_ex : crush.

  Lemma check_prog'_increasing : forall p l l',
     check_prog' l p = (true, l') ->
      (forall s, List.In s l -> List.In s l').
  Proof.
    induction p; simplify; invert H; eauto using check_arith_monotone, List.in_cons.
    - destruct (check_bool' l b) eqn:?EQ; simplify; try discriminate.
      destruct (check_prog' l p1) eqn:?EQ. restrict b0.
      destruct (check_prog' l p2) eqn:?EQ. restrict b0.
      invert H2. eapply list_intersect_intro.
      split; eauto.
    - destruct (check_prog' l p) eqn:?EQ.
      restrict b0.
    - destruct (check_prog' l p1) eqn:?EQ.
      restrict b.
    - destruct (check_prog' l p1) eqn:?EQ.
      restrict b.
  Qed.
  Hint Resolve check_prog'_increasing : crush.

  Lemma check_prog'_idem : forall p l l',
     check_prog' l p = (true, l') -> exists l'', check_prog' l' p = (true, l'').
  Proof.
    simplify.
    eauto using check_prog'_monotone_ex, check_prog'_increasing.
  Qed.

  Lemma check_prog_nest : forall p l,
     (exists l', check_prog' l p = (true, l')) ->
     forall C p', plug C p' p -> exists l'', check_prog' l p' = (true, l'').
  Proof.
    induction 2; simplify; eauto.
    - apply IHplug.
      destruct (check_prog' l c').
      restrict b.
    - apply IHplug.
      destruct (check_prog' l c').
      destruct (check_prog' l c2).
      restrict b.
    - apply IHplug.
      destruct (check_prog' l c1).
      destruct (check_prog' l c').
      restrict b.
  Qed.
  Hint Resolve check_prog_nest : crush.

  Definition check_compatible (l1 l2 : list string) (c1 c2 : cmd) : Prop :=
    (forall s, List.In s l1 -> List.In s l2) ->
    forall l1' l2', check_prog' l1 c1 = (true, l1') ->
               check_prog' l2 c2 = (true, l2') ->
               (forall s, List.In s l1' -> List.In s l2').

  Lemma check_compatible_plug : forall c1 c1' C,
     plug C c1 c1' -> forall c2 c2',
       plug C c2 c2' -> forall l1 l2,
         check_compatible l1 l2 c1 c2 ->
         check_compatible l1 l2 c1' c2'.
  Proof.
    induction 1; simplify.
    - invert H. assumption.
    - invert H0.
      unfold check_compatible in *.
      intros. simplify.
      destruct (check_prog' l1 c') eqn:?EQ.
      destruct (check_prog' l2 c'0) eqn:?EQ.
      restrict b. restrict b0.
      eauto using check_prog'_monotone.
    - invert H0.
      unfold check_compatible.
      intros. simplify.
      destruct (check_prog' l1 c') eqn:?EQ.
      destruct (check_prog' l2 c'0) eqn:?EQ.
      restrict b. restrict b0.
      eauto using check_prog'_monotone.
    - invert H0.
      unfold check_compatible in *.
      intros. simplify.
      destruct (check_prog' l1 c1) eqn:?EQ.
      destruct (check_prog' l2 c1) eqn:?EQ.
      destruct (check_prog' l2 c'0) eqn:?EQ.
      restrict b. restrict b0.
      invert H3.
      eauto using check_prog'_monotone.
  Qed.
  Hint Resolve check_compatible_plug : crush.

  Lemma check_prog_plug : forall C c1 c1',
     plug C c1 c1' -> forall l1,
       (exists l', check_prog' l1 c1' = (true, l')) ->
       (forall c2 c2', plug C c2 c2' -> forall l2,
            (forall s, List.In s l1 -> List.In s l2) ->
            check_compatible l1 l2 c1 c2 ->
            (exists l', check_prog' l2 c2 = (true, l')) ->
            (exists l', check_prog' l2 c2' = (true, l'))).
  Proof.
    induction 1; simplify.
    - invert H0. eauto.

    - invert H1. simplify.

      destruct (check_prog' l1 c') eqn:?EQ.
      restrict b.

      assert (exists L'' : list string, check_prog' l2 c'0 = (true, L'')).
      { eapply IHplug; eauto. }
      simplify. rewrite H1.

      pose proof (check_compatible_plug H H9 H3).
      unfold check_compatible in H0.
      epose proof (H0 _ _ _ EQ H1).
      eauto using check_prog'_monotone_ex.

    - invert H1.

      destruct (check_prog' l1 c') eqn:?EQ.
      destruct (check_prog' l1 c2) eqn:?EQ.
      restrict b. invert H4.

      destruct (check_prog' l2 c'0) eqn:?EQ.

      assert (check_prog' l2 c'0 = (true, l0)).
      { cut (exists L' : list string, check_prog' l2 c'0 = (true, L')).
        - intros. simplify. rewrite EQ1 in H1. invert H1. assumption.
        - eapply IHplug; eauto. }
      rewrite EQ1 in H0. invert H0.
      eauto using check_prog'_monotone_ex.

    - invert H1.
      destruct (check_prog' l1 c1) eqn:?EQ.
      destruct (check_prog' l1 c') eqn:?EQ.
      restrict b. invert H4.

      destruct (check_prog' l2 c1) eqn:?EQ.
      assert (exists l0, check_prog' l2 c1 = (true, l0)).
      { eauto using check_prog'_monotone_ex. }
      simplify. rewrite EQ1 in H1. invert H1.

      assert (exists L'' : list string, check_prog' l2 c'0 = (true, L'')).
      { eapply IHplug; eauto. }
      simplify. rewrite H1. eauto.

    Unshelve.
    assumption.
  Qed.
  Hint Resolve check_prog_plug : crush.

  Definition not_stuck (s : t * cmd) : Prop := snd s = Skip \/ exists s', step s s'.
  Definition check_prog (predef : list string) (p : cmd) : bool := fst $ check_prog' predef p.

  Lemma check_prog_preservation' : forall p l m,
     l = list_defs m ->
     check_prog l p = true ->
     forall p' m', step0 (m, p) (m', p') -> forall l',
        l' = list_defs m' ->
        check_prog l' p' = true.
  Proof.
    destruct p; simplify; invert H1; try reflexivity.
    - unfold check_prog in *. simplify.
      squash.
      restrict b0.

    - unfold check_prog in *. simplify.
      squash.
      restrict b0. restrict b1.

    - unfold check_prog in *. simplify.
      destruct (check_prog' (list_defs m') p) eqn:?EQ.
      restrict b0.
      destruct (check_prog' l p) eqn:?EQ.
      pose proof (check_prog'_increasing _ _ EQ).
      pose proof (check_bool'_monotone _ _ _ H H0).
      pose proof (check_prog'_monotone_ex _ _ _ H EQ).
      simplify. rewrite H3 in EQ0. invert EQ0.
      rewrite H1. reflexivity.

    - unfold check_prog in *; simplify; auto.
    - unfold check_prog in *; simplify; auto.
  Qed.
  Hint Resolve check_prog_preservation' : crush.

  Lemma check_prog_invert : forall l c,
     check_prog l c = true -> exists l', check_prog' l c = (true, l').
  Proof.
    simplify.
    destruct (check_prog' l c) eqn:?EQ.
    unfold check_prog in H. rewrite EQ in H. simplify.
    rewrite H. eauto.
  Qed.
  Hint Resolve check_prog_invert : crush.

  Hint Constructors step : imp.
  Hint Constructors step0 : imp.
  Hint Constructors plug : imp.

  Lemma check_prog_progress : forall p l m,
     l = list_defs m ->
     check_prog l p = true -> not_stuck (m, p).
  Proof.
    induction p; unfold not_stuck in *; simplify; auto; right.
    - unfold check_prog in H0. unfold check_prog' in H0. simplify.
      pose proof (check_arith_ok _ H _ H0). simplify.
      eauto with imp.
    - unfold check_prog in H0. simplify.
      destruct (check_bool' l b) eqn:?EQ; simplify; try discriminate.
      epose proof (check_bool'_ok _ _ _ EQ). simplify.
      destruct x; eauto with imp.
    - unfold check_prog in H0. simplify.
      destruct (check_prog' l p) eqn:?EQ.
      restrict b0.
      pose proof (check_bool'_ok _ H _ H0). simplify.
      destruct x; eauto with imp.
    - unfold check_prog in H0. simplify.
      assert (check_prog l p1 = true).
      { destruct (check_prog l p1) eqn:?EQ; try congruence.
        unfold check_prog in EQ.
        destruct (check_prog' l p1).
        simplify. subst. discriminate. }

      eapply IHp1 in H1; [> | eassumption].
      destruct H1; subst.
      + eauto with imp.
      + invert H1. invert H.
        eauto with imp.
    - unfold check_prog in H0. simplify.
      assert (check_prog l p1 = true).
      { destruct (check_prog l p1) eqn:?EQ; try congruence.
        unfold check_prog in EQ.
        destruct (check_prog' l p1).
        simplify. subst. discriminate. }

      eapply IHp1 in H1; [> | eassumption].
      destruct H1; subst.
      + eauto with imp.
      + invert H1. invert H.
        eauto with imp.

    Unshelve.
    assumption.
  Qed.

  Lemma step0_compat : forall c c' m m',
     step0 (m, c) (m', c') ->
     check_compatible (list_defs m) (list_defs m') c c'.
  Proof.
    induction c; simplify; invert H; simplify.
    - unfold check_compatible. simplify.
      invert H0. invert H2.
      destruct (s0 ==s s).
      + rewrite e in *.
        eapply list_defs_set.
      + apply List.in_inv in H3. inversion H3; try congruence.
        eapply list_defs_set_preserve. assumption.
    - unfold check_compatible. simplify.
      squash. restrict b0. restrict b1.
      invert H0. invert H2.
      apply list_intersect_sound in H3.
      invert H3.
      eauto with crush.
    - unfold check_compatible. simplify.
      squash. restrict b0. restrict b1.
      invert H0. invert H2.
      apply list_intersect_sound in H3.
      invert H3.
      eauto with crush.
    - unfold check_compatible. simplify.
      destruct (check_prog' (list_defs m') c) eqn:?EQ.
      restrict b0.
      destruct (check_bool' (list_defs m') b) eqn:?EQ; simplify; try discriminate.
      destruct (check_prog' l c).
      restrict b0. invert H2. invert H0.
      eauto with crush.
    - unfold check_compatible. simplify.
      destruct (check_prog' (list_defs m')).
      restrict b0.
    - unfold check_compatible. simplify.
      eauto with crush.
    - unfold check_compatible. simplify.
      eauto with crush.

      Unshelve.
      + constructor.
      + constructor.
  Qed.

  Lemma check_prog_preservation : forall p l m,
     l = list_defs m ->
     check_prog l p = true ->
     forall p' m', step (m, p) (m', p') -> forall l',
        l' = list_defs m' ->
        check_prog l' p' = true.
  Proof.
    destruct p; simplify; invert H1.
    - invert H7.
      invert H9.
      eapply check_prog_preservation'; eauto.
    - invert H7.
      invert H9.
      eapply check_prog_preservation'; eauto.
    - invert H7.
      invert H9.
      eapply check_prog_preservation'; eauto.
    - invert H7.
      invert H9.
      eapply check_prog_preservation'; eauto.
    - invert H7.
      + invert H9.
        eapply check_prog_preservation'; eauto.
      + invert H9.
        pose proof (step0_monotone H8).

        unfold check_prog in H0. simplify.
        destruct (check_prog' (list_defs m) p1) eqn:?EQ.
        restrict b. apply check_prog_invert in H0. simplify.

        unfold check_prog. simplify.
        destruct (check_prog' (list_defs m') c'0) eqn:?EQ.

        assert (exists l', check_prog' (list_defs m') c'0 = (true, l')).
        { assert (exists l, check_prog' (list_defs m) c = (true, l)) by eauto with crush.
          simplify.
          assert (check_prog (list_defs m) c = true).
          { unfold check_prog. rewrite H2. auto. }
          epose proof (check_prog_preservation' _ H0 H8).
          specialize (H4 (list_defs m')). intuition.
          eapply (check_prog_plug).
          6: { apply check_prog_invert in H6. exact H6. }
          3: { exact H5. }
          1: { exact H3. }
          1: { exists l. exact EQ. }
          1: { exact H. }
          apply step0_compat. assumption. }
        simplify. rewrite EQ0 in H2. invert H2.

        pose proof (check_compatible_plug H3 H5).
        unfold check_compatible in H0.

        cut (exists l', check_prog' x0 p2 = (true, l')).
        1: { intros. simplify. rewrite H4. reflexivity. }

        eapply check_prog'_monotone_ex.
        2: { exact H1. }

        eapply H0; eauto.
        simplify.
        pose proof (step0_compat H8). eauto.

        Unshelve.
        reflexivity.

    - invert H7; invert H9.
      + eapply check_prog_preservation'; eauto.
      + pose proof (step0_monotone H8).

        unfold check_prog in H0. simplify.
        destruct (check_prog' (list_defs m) p1) eqn:?EQ.
        restrict b.
        apply check_prog_invert in H0. simplify.

        unfold check_prog. simplify.
        destruct (check_prog' (list_defs m') c'0) eqn:?EQ.

        assert (exists l, check_prog' (list_defs m') c'0 = (true, l)).
        { assert (exists l, check_prog' (list_defs m) c = (true, l)) by eauto with crush.
          simplify.
          assert (check_prog (list_defs m) c = true).
          { unfold check_prog. rewrite H2. auto. }
          epose proof (check_prog_preservation' _ H0 H8).
          specialize (H4 (list_defs m')). intuition.
          eapply (check_prog_plug).
          6: { apply check_prog_invert in H6. exact H6. }
          3: { exact H5. }
          2: { exists l. exact EQ. }
          2: { exact H. }
          1: { exact H3. }
          apply step0_compat. assumption. }
        simplify. rewrite EQ0 in H2. invert H2.

        cut (exists l', check_prog' (list_defs m') p2 = (true, l')).
        1: { intros. simplify. rewrite H2. reflexivity. }
        eapply check_prog'_monotone_ex.
        * eapply step0_monotone. exact H8.
        * exact H1.

      + pose proof (step0_monotone H8).

        unfold check_prog in H0. simplify.
        destruct (check_prog' (list_defs m) p1) eqn:?EQ.
        restrict b.
        apply check_prog_invert in H0. simplify.

        unfold check_prog. simplify.
        destruct (check_prog' (list_defs m') p1) eqn:?EQ.

        assert (exists l, check_prog' (list_defs m') p1 = (true, l)).
        { assert (exists l, check_prog' (list_defs m) p1 = (true, l)) by eauto with crush.
          eapply check_prog'_monotone_ex.
          - eapply step0_monotone. exact H8.
          - exact EQ. }
        simplify. rewrite EQ0 in H2. invert H2.

        cut (exists l', check_prog' (list_defs m') c'0 = (true, l')).
        1: { intros. simplify. rewrite H2. reflexivity. }
        assert (exists l, check_prog' (list_defs m) c = (true, l)) by eauto with crush.
        simplify.
        assert (check_prog (list_defs m) c = true).
        { unfold check_prog. rewrite H2. auto. }
        epose proof (check_prog_preservation' _ H0 H8).
        specialize (H4 (list_defs m')). intuition.
        eapply (check_prog_plug).
        6: { apply check_prog_invert in H6. exact H6. }
        3: { exact H5. }
        1: { exact H3. }
        2: { exact H. }
        1: {exists x. exact H1. }
        apply step0_compat. assumption.

        Unshelve.
        * reflexivity.
        * reflexivity.
  Qed.

  Definition invariantFor (s : t * cmd) (invariant : t * cmd -> Prop) :=
    forall s', (trc step) s s' -> invariant s'.

  Theorem invariant_weaken : forall (s : t * cmd)
                               (invariant1 invariant2 : t * cmd -> Prop),
   invariantFor s invariant1
   -> (forall s, invariant1 s -> invariant2 s)
   -> invariantFor s invariant2.
  Proof.
    unfold invariantFor; intuition eauto.
  Qed.

  Theorem invariant_induction : forall (s : t * cmd) (invariant : t * cmd -> Prop),
     invariant s
     -> (forall s, invariant s -> forall s', step s s' -> invariant s')
     -> invariantFor s invariant.
  Proof.
    unfold invariantFor; intros.
    assert (invariant s) by eauto.
    induction H1; eauto.
  Qed.

  Definition safe (s : t * cmd) : Prop := invariantFor s not_stuck.

  Lemma check_prog_sound : forall p m,
     check_prog (list_defs m) p = true -> safe (m, p).
  Proof with eauto using check_prog_progress, check_prog_preservation.
    unfold safe. intros.

    eapply invariant_weaken with (invariant1 :=
                                    fun x => match x with
                                          | (m, p) => check_prog (list_defs m) p = true
                                          end).
    2: { destruct s... }

    eapply invariant_induction...
    intros. destruct s, s'...
  Qed.
End Analysis.

Module ProgramChecks.
  Example par_start_map := ∅["n" ↦ 1].
  Example par_prog :=
    ("a" ← "n"; "n" ← "a" ⊗ 2) || ("b" ← "n"; "n" ← "b" ⊗ 2).
  Compute check_prog (VeryInefficientListMap.list_defs par_start_map) par_prog.

  Example factorial_start_map := ∅["input" ↦ 5].
  Example factorial_prog :=
    "output" ← 1;
    while "input" loop
        "output" ← "output" ⊗ "input";
        "input" ← "input" ⊖ 1
    done.
  Compute check_prog (VeryInefficientListMap.list_defs factorial_start_map) factorial_prog.

  Example test_start_map := ∅["input" ↦ 4].
  Example test_prog :=
    when "input" == 5 then
        "output" ← 1
    else
        "output" ← 0
    done.
  Compute check_prog (VeryInefficientListMap.list_defs test_start_map) test_prog.

  Example simple_prog := "output" ← "input".
  Compute check_prog (VeryInefficientListMap.list_defs ∅) simple_prog.
End ProgramChecks.

Section Simulation.
  Definition state := VeryInefficientListMap.t * cmd : Set.
  Variable V__T : state -> nat. (** Some function for extracting terminal valuations from a state. *)

  Inductive Done : state -> Prop := | DoneIntro : forall v, Done (v, Skip).
  Hint Constructors Done : core.

  (** Formalisation differs slighly from presentation in from text:
      we have a predicate over *states* not programs since our
      language isn't deterministic, and the text defined this only
      for deterministic systems. *)
  Inductive M : state -> state -> Prop :=
  | MIntro : forall s1 s2, Done s1 -> Done s1 -> V__T s1 = V__T s2 -> M s1 s2.

  Variable S1 S2 : state.

  Variable R : state -> state -> Prop.

  (** Pre-simulation *)
  Hypothesis R__start : R S1 S2.
  Hypothesis R__end : forall s1,
     Done s1 ->
     forall s2, R s1 s2 -> Done s2.

  (** Suitability *)
  Hypothesis R__suitable : forall s1 s2,
     R s1 s2 -> M s1 s2.

  Section LockStep.
    Hypothesis lockstep_diagram : forall s1 s2,
     R s1 s2 ->
     forall s1', step s1 s1'
            -> exists s2', step s2 s2' /\ R s1' s2'.

    Lemma lockstep_sound' : forall S1 S1',
       trc step S1 S1' ->
       forall S2, R S1 S2 -> exists S2', trc step S2 S2' /\ R S1' S2'.
    Proof with eauto with trc.
      intros until S1'.
      induction 1; intros.
      - eexists. simplify...
      - eapply lockstep_diagram in H1.
        2: { eassumption. }
        invert H1. simplify.
        apply IHtrc in H3.
        invert H3. simplify...
    Qed.
    Hint Resolve lockstep_sound' : core.

    Lemma lockstep_sound : forall S1',
       trc step S1 S1' ->
       exists S2', trc step S2 S2' /\ R S1' S2'.
    Proof. eauto. Qed.

    Lemma lockstep_finish : forall S1',
       trc step S1 S1' -> Done S1' ->
       exists S2', Done S2' /\ trc step S2 S2' /\ R S1' S2'.
    Proof.
      intros. invert H0.
      pose proof (lockstep_sound H).
      simplify. eexists. simplify; eauto.
      eauto using DoneIntro.
    Qed.

    Theorem lockstep_complete : forall S1',
       trc step S1 S1' -> Done S1' ->
       exists S2', trc step S2 S2' /\ M S1' S2'.
    Proof with eauto.
      intros.
      pose proof (lockstep_finish H H0).
      simplify...
    Qed.
  End LockStep.

  Section Star.
    Hypothesis star_diagram : forall s1 s2,
     R s1 s2 ->
     forall s1', step s1 s1'
            -> exists s2', trc step s2 s2' /\ R s1' s2'.

    Lemma star_sound' : forall S1 S1',
       trc step S1 S1' ->
       forall S2, R S1 S2 -> exists S2', trc step S2 S2' /\ R S1' S2'.
    Proof with eauto with trc.
      intros until S1'.
      induction 1; intros.
      - eexists. simplify...
      - eapply star_diagram in H1.
        2: { eassumption. }
        invert H1. simplify.
        apply IHtrc in H3.
        invert H3. simplify...
    Qed.
    Hint Resolve star_sound' : core.

    Lemma star_sound : forall S1',
       trc step S1 S1' ->
       exists S2', trc step S2 S2' /\ R S1' S2'.
    Proof. eauto. Qed.

    Lemma star_finish : forall S1',
       trc step S1 S1' -> Done S1' ->
       exists S2', Done S2' /\ trc step S2 S2' /\ R S1' S2'.
    Proof.
      intros. invert H0.
      pose proof (star_sound H).
      simplify. eexists. simplify; eauto.
      eauto using DoneIntro.
    Qed.

    Theorem star_complete : forall S1',
       trc step S1 S1' -> Done S1' ->
       exists S2', trc step S2 S2' /\ M S1' S2'.
    Proof with eauto.
      intros.
      pose proof (star_finish H H0).
      simplify...
    Qed.
  End Star.
End Simulation.

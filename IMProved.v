Require Import Arith Bool Strings.String.

Require Import Lib.
Require Export EXPRs VMAPs Closure.

Set Default Goal Selector "!".
Set Implicit Arguments.

Open Scope list_scope.
Open Scope string_scope.

Module VeryInefficientListMap <: VMAP.
  Definition t : Set := list (string * nat).

  Definition empty : t := nil.

  Fixpoint get_var (m : t) (v : string) :=
    match m with
    | nil => None
    | (v', n) :: m' => if (v ==s v') then Some n else get_var m' v
    end.

  Definition set_var (m : t) (v : string) (n : nat) := (v, n) :: m.

  Definition list_defs (m : t) := List.map fst m.

  Lemma get_empty : forall v, get_var empty v = None. simpl. congruence. Qed.

  Lemma get_set_same : forall v n t, get_var (set_var t v n) v = Some n.
    intros. simpl. destruct (v ==s v); congruence.
  Qed.

  Lemma get_set_other : forall v1 v2 n t, v1 <> v2 -> get_var (set_var t v1 n) v2 = get_var t v2.
    intros. simpl. destruct (v2 ==s v1); congruence.
  Qed.

  Lemma list_defs_ok : forall v t, List.In v (list_defs t) -> exists n, get_var t v = Some n.
  Proof.
    induction t0; simplify; try contradiction.
    destruct a. invert H; simplify.
    - destruct (s ==s s); eexists; try reflexivity; congruence.
    - apply IHt0 in H0. invert H0.
      destruct (v ==s s); eexists; try reflexivity; eassumption.

    Unshelve.
    constructor.
  Qed.

  Lemma list_defs_complete : forall v t n, get_var t v = Some n -> List.In v (list_defs t).
  Proof.
    induction t0; simplify; try discriminate.
    destruct a.
    destruct (v ==s s); simplify; eauto.
  Qed.

  Lemma list_defs_set : forall v t n, List.In v (list_defs (set_var t v n)).
  Proof.
    induction t0; simplify; auto.
  Qed.

  Lemma list_defs_set_preserve : forall v t s n, List.In v (list_defs t) -> List.In v (list_defs (set_var t s n)).
  Proof.
    induction t0; simplify; try contradiction.
    invert H; auto.
  Qed.
End VeryInefficientListMap.

Module Imp(vmap : VMAP) (expr_dsl : EXPR_DSL(vmap)).
  Import expr_dsl.
  Export expr_dsl.Coercions.

  Module Import expr_dsl_notation := EXPR_DSL_Notation(vmap) (expr_dsl).
  Module Import vmap_notation := VMAP_Notation(vmap).

  Open Scope dsl_scope.
  Open Scope nat_scope.
  Open Scope vmap_scope.

  (* Evaluation Context Implementation due to Adam Chlipala *)
  Inductive cmd :=
  | Skip : cmd
  | Assign : string -> arith -> cmd
  | If : bool' -> cmd -> cmd -> cmd
  | While : bool' -> cmd -> cmd
  | Seq : cmd -> cmd -> cmd
  | Par : cmd -> cmd -> cmd.

  Inductive context :=
  | Hole
  | CSeq : context -> cmd -> context
  | CPar1 : context -> cmd -> context
  | CPar2 : cmd -> context -> context.

  Inductive plug : context -> cmd -> cmd -> Prop :=
  | PlugHole : forall c, plug Hole c c
  | PlugSeq : forall c C c' c2,
     plug C c c' ->
     plug (CSeq C c2) c (Seq c' c2)
  | PlugPar1 : forall c C c' c2,
     plug C c c' ->
     plug (CPar1 C c2) c (Par c' c2)
  | PlugPar2 : forall c C c' c1,
     plug C c c' ->
     plug (CPar2 c1 C) c (Par c1 c').

  Inductive step0 : vmap.t * cmd -> vmap.t * cmd -> Prop :=
  | Step0Assign : forall v x e n,
     A⟦e⟧(v) = Some n ->
     step0 (v, Assign x e) (v[x ↦ n], Skip)
  | Step0Seq : forall v c2,
     step0 (v, Seq Skip c2) (v, c2)
  | Step0IfTrue : forall v b then_ else_,
     B⟦b⟧(v) = Some true ->
     step0 (v, If b then_ else_) (v, then_)
  | Step0IfFalse : forall v b then_ else_,
     B⟦b⟧(v) = Some false ->
     step0 (v, If b then_ else_) (v, else_)
  | Step0WhileTrue : forall v b body,
     B⟦b⟧(v) = Some true ->
     step0 (v, While b body) (v, Seq body (While b body))
  | Step0WhileFalse : forall v b body,
     B⟦b⟧(v) = Some false ->
     step0 (v, While b body) (v, Skip)
  | Step0Par1 : forall v c,
     step0 (v, Par Skip c) (v, c).

  Inductive step : vmap.t * cmd -> vmap.t * cmd -> Prop :=
  | Step : forall C v c v' c' c1 c2,
     plug C c c1
     -> step0 (v, c) (v', c')
     -> plug C c' c2
     -> step (v, c1) (v', c2).

  Module Notation.
    Notation "x ← e" := (Assign x e) (at level 75).
    Notation "'when' e 'then' then_ 'else' else_ 'done'" := (If e then_ else_) (at level 75, e at level 0).
    Notation "'while' e 'loop' body 'done'" := (While e body) (at level 75).
    Infix ";" := Seq (at level 76).
    Infix "||" := Par.

    Notation "{ v , c }  ⤑ { v' , c' }" := (step0 (v, c) (v', c')) (at level 0).
    Notation "{ v , c }  → { v' , c' }" := (step (v, c) (v', c')) (at level 0).
    Notation "{ v , c }  ⇝ { v' , c' }" := ((trc step) (v, c) (v', c')) (at level 0).

    Notation "⟪ p | m ⟫" := (sig (fun v => {m, p} ⇝ {v, Skip})) (at level 0, no associativity).
  End Notation.
End Imp.

Module ImpExpr(vmap : VMAP) <: EXPR_DSL(vmap).
  Open Scope nat_scope.

  Inductive _arith :=
  | Lit : nat -> _arith
  | Var : string -> _arith

  | Plus : _arith -> _arith -> _arith
  | Minus : _arith -> _arith -> _arith
  | Mult : _arith -> _arith -> _arith
  | Div : _arith -> _arith -> _arith.

  Definition arith := _arith.

  Fixpoint denote_arith (e : arith) : vmap.t -> option nat :=
    match e with
    | Lit n => fun _ => Some n
    | Var s => fun m => vmap.get_var m s

    | Plus e1 e2 => fun m =>
                    match (denote_arith e1 m, denote_arith e2 m) with
                    | (Some n1, Some n2) => Some (n1 + n2)
                    | _ =>  None
                    end
    | Minus e1 e2 => fun m =>
                     match (denote_arith e1 m, denote_arith e2 m) with
                     | (Some n1, Some n2) => Some (n1 - n2)
                     | _ =>  None
                     end
    | Mult e1 e2 => fun m =>
                    match (denote_arith e1 m, denote_arith e2 m) with
                    | (Some n1, Some n2) => Some (n1 * n2)
                    | _ =>  None
                    end
    | Div e1 e2 => fun m =>
                   match (denote_arith e1 m, denote_arith e2 m) with
                   | (Some n1, Some n2) => Some (n1 / n2)
                   | _ =>  None
                   end
    end.

  Inductive _bool' :=
  | False' : _bool'
  | True' : _bool'

  | Arith : _arith -> _bool'

  | Neg : _bool' -> _bool'
  | Conj : _bool' -> _bool' -> _bool'
  | Disj : _bool' -> _bool' -> _bool'

  | Eq : _arith -> _arith -> _bool'

  | Lt : _arith -> _arith -> _bool'
  | Lte : _arith -> _arith -> _bool'
  | Gt : _arith -> _arith -> _bool'
  | Gte : _arith -> _arith -> _bool'.

  Definition bool' := _bool'.

  Fixpoint denote_bool' (b : bool') : vmap.t -> option bool :=
    match b with
    | False' => fun _ => Some false
    | True' => fun _ => Some false

    | Arith e => fun m => match denote_arith e m with
                      | Some n => if (n <nat 0) then Some false else Some true
                      | _ => None
                      end

    | Neg b => fun m => match denote_bool' b m with
                     | Some b => Some $ negb b
                     | _ => None
                     end

    | Conj b1 b2 => fun m =>
                    match (denote_bool' b1 m, denote_bool' b2 m) with
                    | (Some n1, Some n2) => Some (andb n1 n2)
                    | _ =>  None
                    end

    | Disj b1 b2 => fun m =>
                    match (denote_bool' b1 m, denote_bool' b2 m) with
                    | (Some n1, Some n2) => Some (orb n1 n2)
                    | _ =>  None
                    end

    | Eq e1 e2 => fun m =>
                  match (denote_arith e1 m, denote_arith e2 m) with
                  | (Some n1, Some n2) => Some (n1 =? n2)
                  | _ =>  None
                  end

    | Lt e1 e2 => fun m =>
                  match (denote_arith e1 m, denote_arith e2 m) with
                  | (Some n1, Some n2) => Some (n1 <? n2)
                  | _ =>  None
                  end
    | Lte e1 e2 => fun m =>
                   match (denote_arith e1 m, denote_arith e2 m) with
                   | (Some n1, Some n2) => Some (n1 <=? n2)
                   | _ =>  None
                   end
    | Gt e1 e2 => fun m =>
                  match (denote_arith e1 m, denote_arith e2 m) with
                  | (Some n1, Some n2) => Some (n2 <=? n1)
                  | _ =>  None
                  end
    | Gte e1 e2 => fun m =>
                   match (denote_arith e1 m, denote_arith e2 m) with
                   | (Some n1, Some n2) => Some (n2 <? n1)
                   | _ =>  None
                   end
    end.

  Module Coercions.
    Coercion Lit : nat >-> _arith.
    Coercion Var : string >-> _arith.

    Coercion Arith : _arith >-> _bool'.
  End Coercions.

  Module Notation.
    Infix "⊕" := Plus (left associativity, at level 50).
    Infix "⊖" := Minus (left associativity, at level 50).
    Infix "⊗" := Mult (left associativity, at level 40).
    Infix "⨸" := Div (left associativity, at level 40).

    Infix "⧀" := Lt (no associativity, at level 70).
    Infix "⧁" := Gt (no associativity, at level 70).
    Infix "==" := Eq (no associativity, at level 70).

    Infix "⊙" := Conj (left associativity, at level 50).
    Infix "⦹" := Disj (left associativity, at level 50).
  End Notation.
End ImpExpr.

Require Import SfLib.
Require Import partial_map.

Module STLC.

Hint Resolve beq_id_eq beq_id_false_not_eq.
  
(* types *)
Inductive type : Type :=
| TBool : type
| TNat : type
| TArrow : type -> type -> type.

Hint Constructors type.

(* terms *)
Inductive term : Type :=
| TVar : id -> term
| TApp : term -> term -> term
| TLambda : id -> type -> term -> term
| TTrue : term
| TFalse : term
| TIf : term -> term -> term -> term
| TNum : nat -> term
| TPlus : term -> term -> term
| TEqNat : term -> term -> term.

Notation "\ x : t1 . y" := (TLambda x t1 y) (at level 50).

Tactic Notation "term_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TVar"    | Case_aux c "TApp"
  | Case_aux c "TLambda" | Case_aux c "TTrue"
  | Case_aux c "TFalse"  | Case_aux c "TIf"
  | Case_aux c "TNum"    | Case_aux c "TPlus"
  | Case_aux c "TEqNat" ].

Hint Constructors term.

Inductive value : term -> Prop :=
| v_abs : forall x T t, value (TLambda x T t)
| v_true : value TTrue
| v_false : value TFalse
| v_nat : forall n, value (TNum n).

Hint Constructors value.

Fixpoint subst (x : id) (s : term) (t : term) : term :=
  match t with
    | TVar x' =>
      if beq_id x x' then s else t
    | TLambda x' T t1 =>
      TLambda x' T (if beq_id x x' then t1 else (subst x s t1))
    | TApp lambda arg =>
      TApp (subst x s lambda) (subst x s arg)
    | TTrue => TTrue
    | TFalse => TFalse
    | TIf c t e => TIf (subst x s c) (subst x s t) (subst x s e)
    | TNum n => TNum n
    | TPlus l r => TPlus (subst x s l) (subst x s r)
    | TEqNat l r => TEqNat (subst x s l) (subst x s r)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Reserved Notation "t1 '=>' t2" (at level 40).
Inductive step : term -> term -> Prop :=
| ST_AppLambda : forall x T t12 v2,
                   value v2 -> (TApp (TLambda x T t12) v2) => [x := v2]t12
| ST_App1 : forall t1 t1' t2, t1 => t1' -> TApp t1 t2 => TApp t1' t2
| ST_App2 : forall v1 t2 t2', value v1 -> t2 => t2' -> TApp v1 t2 => TApp v1 t2'
| ST_IfTrue : forall t1 t2, TIf TTrue t1 t2 => t1
| ST_IfFalse : forall t1 t2, TIf TFalse t1 t2 => t2
| ST_If : forall t1 t1' t2 t3, t1 => t1' -> TIf t1 t2 t3 => TIf t1' t2 t3
| ST_Plus : forall n m, TPlus (TNum n) (TNum m) => TNum (n + m)
| ST_PlusL : forall l l' r, l => l' -> TPlus l r => TPlus l' r
| ST_PlusR : forall l r r', value l -> r => r' -> TPlus l r => TPlus l r'
| ST_EqNatT : forall n m, beq_nat n m = true ->
                          TEqNat (TNum n) (TNum m) => TTrue
| ST_EqNatF : forall n m, beq_nat n m = false ->
                          TEqNat (TNum n) (TNum m) => TFalse
| ST_EqNatL : forall l l' r, l => l' -> TEqNat l r => TEqNat l' r
| ST_EqNatR : forall l r r', value l -> r => r' -> TEqNat l r => TEqNat l r'
    where "t1 '=>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppLambda" | Case_aux c "ST_App1"
  | Case_aux c "ST_App2"      | Case_aux c "ST_IfTrue"
  | Case_aux c "ST_IfFalse"   | Case_aux c "ST_If"
  | Case_aux c "ST_Plus"      | Case_aux c "ST_PlusL"
  | Case_aux c "ST_PlusR"     | Case_aux c "ST_EqNatT"
  | Case_aux c "ST_EqNatF"    | Case_aux c "ST_EqNatL"
  | Case_aux c "ST_EqNatR" ].

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '=>*' t2" := (multistep t1 t2) (at level 40).

Definition context := partial_map type.

Inductive has_type : context -> term -> type -> Prop :=
| T_Var : forall G x T,
            G x = Some T -> has_type G (TVar x) T
| T_Lambda : forall G x T11 T12 t12,
               has_type (extend G x T11) t12 T12 ->
               has_type G (TLambda x T11 t12) (TArrow T11 T12)
| T_App : forall T11 T12 G t1 t2,
            has_type G t1 (TArrow T11 T12) ->
            has_type G t2 T11 ->
            has_type G (TApp t1 t2) T12
| T_True : forall G, has_type G TTrue TBool
| T_False : forall G, has_type G TFalse TBool
| T_If : forall t1 t2 t3 T G,
           has_type G t1 TBool ->
           has_type G t2 T ->
           has_type G t3 T ->
           has_type G (TIf t1 t2 t3) T
| T_Nat : forall G n, has_type G (TNum n) TNat
| T_Plus : forall G l r, has_type G l TNat -> has_type G r TNat -> has_type G (TPlus l r) TNat
| T_EqNat : forall G l r, has_type G l TNat -> has_type G r TNat -> has_type G (TEqNat l r) TBool.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var"   | Case_aux c "T_Lambda"
  | Case_aux c "T_App"   | Case_aux c "T_True"
  | Case_aux c "T_False" | Case_aux c "T_If"
  | Case_aux c "T_Nat"   | Case_aux c "T_Plus"
  | Case_aux c "T_EqNat" ].

Hint Constructors has_type.
Hint Unfold beq_nat beq_id extend.

Theorem progress : forall t T, 
     has_type empty t T ->
     value t \/ exists t', t => t'.
Proof with eauto.
  intros t T Ht.
  remember empty as gamma.
  has_type_cases (induction Ht) Case; subst... 
  Case "T_Var". inversion H.
  Case "T_App". right. destruct IHHt1...
    SCase "t1 is a value". destruct IHHt2...
      SSCase "t2 is a value".
        inversion H; subst; try solve by inversion.
        exists ([x := t2] t). constructor...
      SSCase "t2 steps". inversion H0. exists (TApp t1 x). constructor...
    SCase "t1 steps". inversion H. exists (TApp x t2). constructor...
  Case "T_If". right. destruct IHHt1...
    SCase "t1 is a value". inversion H; subst; try solve by inversion.
      SSCase "if true". exists t2. constructor.
      SSCase "if false". exists t3. constructor.
    inversion H. exists (TIf x t2 t3). constructor...
  Case "T_Plus". right. destruct IHHt1... destruct IHHt2...
    inversion H; subst; try solve by inversion.
    inversion H0; subst; try solve by inversion.
    exists (TNum (n+n0))...
    inversion H0. exists (TPlus l x)...
    inversion H. exists (TPlus x r)...
  Case "T_EqNat". right. destruct IHHt1... destruct IHHt2...
    inversion H; subst; try solve by inversion.
    inversion H0; subst; try solve by inversion.
    remember (beq_nat n n0). destruct b. exists TTrue...
    exists TFalse...
    inversion H0. exists (TEqNat l x)...
    inversion H. exists (TEqNat x r)...
Qed.

Inductive appears_free_in : id -> term -> Prop :=
| AFI_Var : forall x,
              appears_free_in x (TVar x)
| AFI_App1 : forall x t1 t2,
               appears_free_in x t1 -> appears_free_in x (TApp t1 t2)
| AFI_App2 : forall x t1 t2,
               appears_free_in x t2 -> appears_free_in x (TApp t1 t2)
| AFI_Lambda : forall x y T11 t12,
                 y <> x ->
                 appears_free_in x t12 ->
                 appears_free_in x (TLambda y T11 t12)
| AFI_If1 : forall x t1 t2 t3,
              appears_free_in x t1 ->
              appears_free_in x (TIf t1 t2 t3)
| AFI_If2 : forall x t1 t2 t3,
              appears_free_in x t2 ->
              appears_free_in x (TIf t1 t2 t3)
| AFI_If3 : forall x t1 t2 t3,
              appears_free_in x t3 ->
              appears_free_in x (TIf t1 t2 t3)
| AFI_Plus1 : forall x l r,
                appears_free_in x l ->
                appears_free_in x (TPlus l r)
| AFI_Plus2 : forall x l r,
                appears_free_in x r ->
                appears_free_in x (TPlus l r)
| AFI_EqNat1 : forall x l r,
                appears_free_in x l ->
                appears_free_in x (TEqNat l r)
| AFI_EqNat2 : forall x l r,
                appears_free_in x r ->
                appears_free_in x (TEqNat l r).

Tactic Notation "afi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "AFI_Var"  | Case_aux c "AFI_App1"
  | Case_aux c "AFI_App2" | Case_aux c "AFI_Lambda"
  | Case_aux c "AFI_If1"  | Case_aux c "AFI_If2"
  | Case_aux c "AFI_If3"  | Case_aux c "AFI_Plus1"
  | Case_aux c "AFI_Plus2" | Case_aux c "AFI_EqNat1"
  | Case_aux c "AFI_EqNat2" ].

Hint Constructors appears_free_in.

Definition closed (t:term) := forall x, ~ appears_free_in x t.

Lemma free_in_context : forall x t T gamma,
                          appears_free_in x t ->
                          has_type gamma t T ->
                          exists T', gamma x = Some T'.
Proof.
  intros x t T gamma H H0. generalize dependent gamma.
  generalize dependent T.
  afi_cases (induction H) Case; intros; try solve [inversion H0; eauto].
    Case "AFI_Lambda". inversion H1. subst. apply IHappears_free_in in H7.
      apply not_eq_beq_id_false in H. rewrite extend_neq in H7; assumption.
Qed.

Lemma context_invariance : forall gamma gamma' t T,
                             has_type gamma t T ->
                             (forall x, appears_free_in x t -> gamma x = gamma' x) ->
                             has_type gamma' t T.
Proof with eauto.
  intros.
  generalize dependent gamma'.
  has_type_cases (induction H) Case; intros; auto.
  Case "T_Var". apply T_Var. rewrite <- H0...
  Case "T_Lambda". apply T_Lambda. apply IHhas_type. intros x0 Hafi.
    unfold extend. remember (beq_id x x0). destruct b...
  Case "T_App".
    eapply T_App...
Qed.

Lemma substitution_preserves_typing : forall gamma x U t t' T,
                                        has_type (extend gamma x U) t T ->
                                        has_type empty t' U ->
                                        has_type gamma ([x:=t']t) T.
Proof with eauto.
  intros gamma x U t t' T Ht Ht'.
  generalize dependent gamma. generalize dependent T.
  term_cases (induction t) Case; intros T gamma H; inversion H; subst; simpl...
  Case "TVar". rename i into y. remember (beq_id x y) as e. destruct e.
    SCase "x=y". apply beq_id_eq in Heqe. subst. rewrite extend_eq in H2.
      inversion H2. subst. eapply context_invariance... intros x Hcontra.
      destruct (free_in_context _ _ T empty Hcontra)... inversion H0.
    SCase "x<>y". constructor. rewrite extend_neq in H2...
  Case "TLambda". rename i into y. apply T_Lambda.
    remember (beq_id x y) as e. destruct e.
    SCase "x=y". eapply context_invariance... apply beq_id_eq in Heqe. subst.
      intros x Hafi. unfold extend. remember (beq_id y x) as e. destruct e...
    SCase "x<>y".
      apply IHt. eapply context_invariance... intros z Hafi. unfold extend.
      remember (beq_id y z) as e0. destruct e0...
      apply beq_id_eq in Heqe0. subst.
      rewrite <- Heqe...
Qed.

Theorem preservation : forall t t' T,
                         has_type empty t T ->
                         t => t' ->
                         has_type empty t' T.
Proof with eauto.
  remember empty as gamma.
  intros t t' T HT. generalize dependent t'.
  has_type_cases (induction HT) Case;
    intros t' HE; subst;  
       try solve [inversion HE; subst; auto].
  Case "T_App".
    inversion HE; subst...
    (* Most of the cases are immediate by induction, 
       and eauto takes care of them *)
    SCase "ST_AppAbs".
      apply substitution_preserves_typing with T11...
      inversion HT1...
Qed.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.
  
Definition stuck (t : term) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary soundness : forall t t' T,
  has_type empty t T -> 
  t =>* t' ->
  ~(stuck t').
Proof with auto.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  multi_cases (induction Hmulti) Case.
  Case "multi_refl".
    apply progress in Hhas_type. inversion Hhas_type...
  Case "multi_step".
    apply preservation with (t' := y) in Hhas_type...
Qed.
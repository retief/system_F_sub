Require Import SfLib.
Require Import partial_map.

Module STLC.

Hint Resolve beq_id_eq beq_id_false_not_eq.
  
(* types *)
Unset Elimination Schemes.
Inductive type : Type :=
| TBool : type
| TNat : type
| TArrow : type -> type -> type
| TRecord : list (id * type) -> type.
Set Elimination Schemes.
(* The issue with induction is that the automatic induction function
 generated does not provide an inductive hypotheses for TRecords.
 This lets us provide our own induction function that fixes the issue.
 *)
Definition type_rec := 
fun (P : type -> Prop) (type_rect_tbool : P TBool) (type_rect_tnat : P TNat)
  (type_rect_tarrow : forall t : type, P t -> forall t0 : type, P t0 -> P (TArrow t t0))
  (type_rect_trecord : forall l : list (id * type), Forall P (map (@snd id type) l) -> P (TRecord l)) =>
fix F (t : type) : P t :=
  match t as t0 return (P t0) with
  | TBool => type_rect_tbool
  | TNat => type_rect_tnat
  | TArrow t0 t1 => type_rect_tarrow t0 (F t0) t1 (F t1)
  | TRecord l =>
    type_rect_trecord l ((fix forall_rec (ls : list (id * type))
                          : Forall P (map (@snd id type) ls) :=
                            match ls with
                              | nil => Forall_nil P
                              | (_,t) :: rest =>
                                Forall_cons t (F t) (forall_rec rest)
                            end)
                           l)
  end.

Hint Constructors type.

(* terms *)
Unset Elimination Schemes.
Inductive term : Type :=
| TVar : id -> term
| TApp : term -> term -> term
| TLambda : id -> type -> term -> term
| TTrue : term
| TFalse : term
| TIf : term -> term -> term -> term
| TNum : nat -> term
| TPlus : term -> term -> term
| TEqNat : term -> term -> term
| TLiteral : list (id * term) -> term
| TAccess : term -> id -> term.
Set Elimination Schemes.
(* TODO: Fix inductive hypotheses for f8 (TLiteral's induction) *)
Definition term_rec := fun (P : term -> Prop) (f : forall i : id, P (TVar i))
  (f0 : forall t : term, P t -> forall t0 : term, P t0 -> P (TApp t t0))
  (f1 : forall (i : id) (t : type) (t0 : term), P t0 -> P (TLambda i t t0))
  (f2 : P TTrue) (f3 : P TFalse)
  (f4 : forall t : term,
        P t ->
        forall t0 : term, P t0 -> forall t1 : term, P t1 -> P (TIf t t0 t1))
  (f5 : forall n : nat, P (TNum n))
  (f6 : forall t : term, P t -> forall t0 : term, P t0 -> P (TPlus t t0))
  (f7 : forall t : term, P t -> forall t0 : term, P t0 -> P (TEqNat t t0))
  (f8 : forall l : list (id * term), Forall P (map (@snd id term) l) -> P (TLiteral l))
  (f9 : forall t : term, P t -> forall i : id, P (TAccess t i)) =>
fix F (t : term) : P t :=
  match t as t0 return (P t0) with
  | TVar i => f i
  | TApp t0 t1 => f0 t0 (F t0) t1 (F t1)
  | TLambda i t0 t1 => f1 i t0 t1 (F t1)
  | TTrue => f2
  | TFalse => f3
  | TIf t0 t1 t2 => f4 t0 (F t0) t1 (F t1) t2 (F t2)
  | TNum n => f5 n
  | TPlus t0 t1 => f6 t0 (F t0) t1 (F t1)
  | TEqNat t0 t1 => f7 t0 (F t0) t1 (F t1)
  | TLiteral l => f8 l ((fix forall_rec (ls : list (id * term))
                         : Forall P (map (@snd id term) ls) :=
                           match ls with
                             | nil => Forall_nil P
                             | (_,t) :: rest =>
                               Forall_cons t (F t) (forall_rec rest)
                           end)
                          l)
  | TAccess t0 i => f9 t0 (F t0) i
  end.

Notation "\ x : t1 . y" := (TLambda x t1 y) (at level 50).

Tactic Notation "term_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TVar"    | Case_aux c "TApp"
  | Case_aux c "TLambda" | Case_aux c "TTrue"
  | Case_aux c "TFalse"  | Case_aux c "TIf"
  | Case_aux c "TNum"    | Case_aux c "TPlus"
  | Case_aux c "TEqNat"  | Case_aux c "TLiteral"
  | Case_aux c "TAccess"].

Hint Constructors term.

Unset Elimination Schemes.
Inductive value : term -> Prop :=
| v_abs : forall x T t, value (TLambda x T t)
| v_true : value TTrue
| v_false : value TFalse
| v_nat : forall n, value (TNum n)
| v_literal : forall l, (Forall value (map (@snd id term) l)) -> value (TLiteral l).
Set Elimination Schemes.

Definition Admitted {T : Type} : T. admit. Qed.

Definition value_ind := fun (P : term -> Prop)
  (f : forall (x : id) (T : type) (t : term), P (TLambda x T t)) 
  (f0 : P TTrue)
  (f1 : P TFalse)
  (f2 : forall n : nat, P (TNum n))
  (f3 : forall l : list (id * term),
        Forall P (map (@snd id term) l) -> P (TLiteral l)) =>
  fix F (t : term) (v : value t) {struct v} : P t :=
  match v in (value t0) return (P t0) with
  | v_abs x T t0 => f x T t0
  | v_true => f0
  | v_false => f1
  | v_nat n => f2 n
  | v_literal l f5 => f3 l ((fix forallrec l (f5 : Forall value l) : Forall P l := 
     match f5 with
     | Forall_nil => Forall_nil P
     | Forall_cons t ts vt tvs => Forall_cons t (F t vt) (forallrec ts tvs)
     end) (map (@snd id term) l) f5)
  end.

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
    | TLiteral l => TLiteral (map (fun p => match p with (i,v) => (i, subst x s v) end) l)
    | TAccess r i => TAccess (subst x s r) i
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Fixpoint lookup (i : id) (l : list (id * term)) : option term :=
  match l with
    | nil => None
    | (i',v) :: l' => if beq_id i i'
                      then Some v
                      else lookup i l'
  end.

Reserved Notation "t1 '=>' t2" (at level 40).
(* Note: Induction should be fine here *)
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
| ST_Literal : forall l r i v v', value (TLiteral l) -> v => v' -> TLiteral (l ++ ((i,v) :: r)) => TLiteral (l ++ ((i,v') :: r))
| ST_Access : forall l i v, value (TLiteral l) -> lookup i l = Some v -> TAccess (TLiteral l) i => v
| ST_AccessS : forall r r' i, r => r' -> TAccess r i => TAccess r' i
    where "t1 '=>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppLambda" | Case_aux c "ST_App1"
  | Case_aux c "ST_App2"      | Case_aux c "ST_IfTrue"
  | Case_aux c "ST_IfFalse"   | Case_aux c "ST_If"
  | Case_aux c "ST_Plus"      | Case_aux c "ST_PlusL"
  | Case_aux c "ST_PlusR"     | Case_aux c "ST_EqNatT"
  | Case_aux c "ST_EqNatF"    | Case_aux c "ST_EqNatL"
  | Case_aux c "ST_EqNatR"    | Case_aux c "ST_Literal"
  | Case_aux c "ST_Access"    | Case_aux c "ST_AccessS"].

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '=>*' t2" := (multistep t1 t2) (at level 40).

Definition context := partial_map type.

(* TODO: Fix induction like type induction on has_type in the
 T_Literal case doesn't have that the Forall2's has_types
 imply anything *)
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
| T_EqNat : forall G l r, has_type G l TNat -> has_type G r TNat -> has_type G (TEqNat l r) TBool
| T_Literal : forall G lv lt,
                Forall2 (fun p1 p2 =>
                          fst p1 = fst p2 /\
                          has_type G (snd p1) (snd p2))
                        lv lt ->
                has_type G (TLiteral lv) (TRecord lt)
| T_Access : forall G lv lt i v T,
               has_type G (TLiteral lv) (TRecord lt) ->
               In (i,v) lv -> In (i,T) lt ->
               has_type G (TAccess (TLiteral lv) i) T.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var"   | Case_aux c "T_Lambda"
  | Case_aux c "T_App"   | Case_aux c "T_True"
  | Case_aux c "T_False" | Case_aux c "T_If"
  | Case_aux c "T_Nat"   | Case_aux c "T_Plus"
  | Case_aux c "T_EqNat" | Case_aux c "T_Literal"
  | Case_aux c "T_Access" ].

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
  Case "T_Literal".
    induction H; intros; subst.
    SCase "Base". left. constructor. intros.  contradict H.
    SCase "Inductive". destruct x. destruct y. simpl in *. inversion H. subst.
      
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
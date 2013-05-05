Require Import SfLib.
Require Import util.
Require Import STLC_types.

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
| TLiteral : list id -> list term -> term
| TAccess : term -> id -> term.
Set Elimination Schemes.
(* TODO: Fix inductive hypotheses for f8 (TLiteral's induction) *)
Definition term_ind := fun (P : term -> Prop) (f : forall i : id, P (TVar i))
  (f0 : forall t : term, P t -> forall t0 : term, P t0 -> P (TApp t t0))
  (f1 : forall (i : id) (t : type) (t0 : term), P t0 -> P (TLambda i t t0))
  (f2 : P TTrue) (f3 : P TFalse)
  (f4 : forall t : term,
        P t ->
        forall t0 : term, P t0 -> forall t1 : term, P t1 -> P (TIf t t0 t1))
  (f5 : forall n : nat, P (TNum n))
  (f6 : forall t : term, P t -> forall t0 : term, P t0 -> P (TPlus t t0))
  (f7 : forall t : term, P t -> forall t0 : term, P t0 -> P (TEqNat t t0))
  (f8 : forall li lv, Forall P lv -> P (TLiteral li lv))
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
  | TLiteral li lv => f8 li lv ((fix forall_rec (lv' : list term)
                                 : Forall P lv' :=
                                   match lv' with
                                     | nil => Forall_nil P
                                     | v :: rest =>
                                       Forall_cons v (F v) (forall_rec rest)
                                   end)
                                  lv)
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
| v_literal : forall li lv, (Forall value lv) -> value (TLiteral li lv).
Set Elimination Schemes.



Definition value_ind := fun (P : term -> Prop)
  (f : forall (x : id) (T : type) (t : term), P (TLambda x T t)) 
  (f0 : P TTrue)
  (f1 : P TFalse)
  (f2 : forall n : nat, P (TNum n))
  (f3 : forall li lv,
        Forall P lv -> P (TLiteral li lv)) =>
  fix F (t : term) (v : value t) {struct v} : P t :=
  match v in (value t0) return (P t0) with
  | v_abs x T t0 => f x T t0
  | v_true => f0
  | v_false => f1
  | v_nat n => f2 n
  | v_literal li lv f5 => f3 li lv ((fix forallrec l (f5 : Forall value l) : Forall P l := 
     match f5 with
     | Forall_nil => Forall_nil P
     | Forall_cons t ts vt tvs => Forall_cons t (F t vt) (forallrec ts tvs)
     end) lv f5)
  end.

Tactic Notation "value_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "v_abs" | Case_aux c "v_true"
  | Case_aux c "v_false" | Case_aux c "v_nat"
  | Case_aux c "v_literal" ].

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
    | TLiteral li lv => TLiteral li (map (subst x s) lv)
    | TAccess r i => TAccess (subst x s r) i
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Fixpoint lookup' (i : id) (l : list (id * term)) : option term :=
  match l with
    | nil => None
    | (i',v) :: l' => if beq_id i i'
                      then Some v
                      else lookup' i l'
  end.

Definition lookup i li lv :=
  lookup' i (combine li lv).

Lemma lookup_in_pair : forall i v li lv,
                    Uniq li -> lookup i li lv = Some v -> In (i,v) (combine li lv).
Proof with auto.
  intros i v li. generalize dependent i. generalize dependent v.
  induction li; intros; try solve by inversion.
    Case "inductive". destruct lv; try solve by inversion.  simpl in *.
      unfold lookup in H0. simpl in H0. remember (beq_id i a). destruct b.
      SCase "i = a". apply beq_id_eq in Heqb. inversion H0. subst...
      SCase "i != a". inversion H; subst. unfold lookup in IHli. right.
        apply (IHli v i lv H4 H0)...
Qed.

Lemma lookup_in : forall i v li lv,
                    Uniq li -> lookup i li lv = Some v -> In i li.
Proof with auto.
  intros. apply in_combine_l with (l' := lv) (y := v). apply lookup_in_pair...
Qed.

Lemma in_lookup : forall i v li lv, Uniq li -> In (i,v) (combine li lv) -> lookup i li lv = Some v.
Proof with auto. intros i v li. generalize dependent i. generalize dependent v.
  induction li; intros.
  Case "base". simpl in *. contradiction.
  Case "inductive". destruct lv. inversion H0. simpl in *. destruct H0.
    SCase "(a,t) = (i,v)". inversion H0. subst. unfold lookup. simpl. rewrite <- beq_id_refl...
    SCase "In (i,v) (combine li lv)". inversion H; subst. apply IHli in H0...
      unfold lookup in *. simpl in *. remember (beq_id i a). destruct b...
        SSCase "i=a". apply beq_id_eq in Heqb. subst. contradict H3.
          apply lookup_in in H0...
Qed.
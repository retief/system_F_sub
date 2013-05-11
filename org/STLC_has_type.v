Require Import List.
Require Import util.
Require Import SfLib.
Require Import STLC_terms.
Require Import STLC_types.

Definition context := partial_map type.

Unset Elimination Schemes.
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
| T_Literal : forall G li lv lt,
                Forall2 (has_type G) lv lt ->
                Uniq li ->
                length li = length lv ->
                length li = length lt ->
                has_type G (TLiteral li lv) (TRecord li lt)
| T_Access : forall G li lv lt i v T,
               has_type G (TLiteral li lv) (TRecord li lt) ->
               In (i,v) (combine li lv) -> In (i,T) (combine li lt) ->
               has_type G (TAccess (TLiteral li lv) i) T
| T_Subtype : forall G t T T',
                has_type G t T ->
                subtype T T' ->
                has_type G t T'.
Set Elimination Schemes.

Definition has_type_ind :=
fun (P : context -> term -> type -> Prop)
  (f : forall (G : id -> option type) (x : id) (T : type),
       G x = Some T -> P G (TVar x) T)
  (f0 : forall (G : partial_map type) (x : id) (T11 T12 : type) (t12 : term),
        has_type (extend G x T11) t12 T12 ->
        P (extend G x T11) t12 T12 -> P G (TLambda x T11 t12) (TArrow T11 T12))
  (f1 : forall (T11 T12 : type) (G : context) (t1 t2 : term),
        has_type G t1 (TArrow T11 T12) ->
        P G t1 (TArrow T11 T12) ->
        has_type G t2 T11 -> P G t2 T11 -> P G (TApp t1 t2) T12)
  (f2 : forall G : context, P G TTrue TBool)
  (f3 : forall G : context, P G TFalse TBool)
  (f4 : forall (t1 t2 t3 : term) (T : type) (G : context),
        has_type G t1 TBool ->
        P G t1 TBool ->
        has_type G t2 T ->
        P G t2 T -> has_type G t3 T -> P G t3 T -> P G (TIf t1 t2 t3) T)
  (f5 : forall (G : context) (n : nat), P G (TNum n) TNat)
  (f6 : forall (G : context) (l r : term),
        has_type G l TNat ->
        P G l TNat -> has_type G r TNat -> P G r TNat -> P G (TPlus l r) TNat)
  (f7 : forall (G : context) (l r : term),
        has_type G l TNat ->
        P G l TNat ->
        has_type G r TNat -> P G r TNat -> P G (TEqNat l r) TBool)
  (f8 : forall (G : context) li (lv : list term) (lt : list type),
          length li = length lv ->
          length li = length lt ->
          Uniq li ->
          Forall2 (P G) lv lt ->
          Forall2 (has_type G) lv lt ->
        P G (TLiteral li lv) (TRecord li lt))
  (f9 : forall (G : context) li (lv : list term)
          (lt : list type) (i : id) (v : term) 
          (T : type),
        has_type G (TLiteral li lv) (TRecord li lt ) ->
        P G (TLiteral li lv) (TRecord li lt ) ->
        In (i, v) (combine li lv) -> In (i, T) (combine li lt) ->
        P G (TAccess (TLiteral li lv) i) T)
  (f10 : forall G t T T', P G t T -> subtype T T' -> has_type G t T -> P G t T') =>
fix F (c : context) (t : term) (t0 : type) (h : has_type c t t0) {struct h} : P c t t0 :=
  match h in (has_type c0 t1 t2) return (P c0 t1 t2) with
    | T_Var G x T e => f G x T e
    | T_Lambda G x T11 T12 t12 h0 =>
      f0 G x T11 T12 t12 h0 (F (extend G x T11) t12 T12 h0)
    | T_App T11 T12 G t1 t2 h0 h1 =>
      f1 T11 T12 G t1 t2 h0 (F G t1 (TArrow T11 T12) h0) h1 (F G t2 T11 h1)
    | T_True G => f2 G
    | T_False G => f3 G
    | T_If t1 t2 t3 T G h0 h1 h2 =>
      f4 t1 t2 t3 T G h0 (F G t1 TBool h0) h1 (F G t2 T h1) h2 (F G t3 T h2)
    | T_Nat G n => f5 G n
    | T_Plus G l r h0 h1 => f6 G l r h0 (F G l TNat h0) h1 (F G r TNat h1)
    | T_EqNat G l r h0 h1 => f7 G l r h0 (F G l TNat h0) h1 (F G r TNat h1)
    | T_Literal G li lv lt f10 u llv llt =>
      f8 G li lv lt llv llt u
         ((fix forallrec term_list type_list
               (f5 : Forall2 (has_type G)
                             term_list type_list) :
             Forall2 (P G)
                     term_list type_list := 
             match f5 with
               | Forall2_nil => Forall2_nil (P G)
               | Forall2_cons term type terms types
                              ht forall2_rest =>
                 Forall2_cons term type
                              (F G term type ht)
                              (forallrec terms types forall2_rest)
             end) lv lt f10) f10
    | T_Access G li lv lt i v T h0 i0 i1 =>
      f9 G li lv lt i v T h0 (F G (TLiteral li lv) (TRecord li lt) h0) i0 i1
    | T_Subtype G t T T' ht st => f10 G t T T' (F G t T ht) st ht
  end.

Hint Constructors has_type.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var"   | Case_aux c "T_Lambda"
  | Case_aux c "T_App"   | Case_aux c "T_True"
  | Case_aux c "T_False" | Case_aux c "T_If"
  | Case_aux c "T_Nat"   | Case_aux c "T_Plus"
  | Case_aux c "T_EqNat" | Case_aux c "T_Literal"
  | Case_aux c "T_Access" | Case_aux c "T_Subtype" ].


Lemma canonical_forms_bool :
  forall (G : context) (t : term),
    has_type G t TBool -> value t -> t = TTrue \/ t = TFalse.
Proof with auto.
  intros.
  remember TBool as x.
  has_type_cases (induction H) Case; try solve by inversion...
  Case "T_Subtype".
    apply IHhas_type in H0... subst.
    apply no_subtypes_bool in H; exact H.
Qed.

Lemma canonical_forms_bool' :
  forall G t T,
    has_type G t T -> T = TBool -> value t -> t = TTrue \/ t = TFalse.
Proof with auto.
  intros.
  has_type_cases (induction H) Case; try solve by inversion...
  Case "T_Subtype". apply no_subtypes_bool' in H...
Qed.


Lemma canonical_forms_nat :
  forall (G : context) (t : term),
    has_type G t TNat -> value t -> exists (n : nat), t = TNum n.
Proof with auto.
  intros. remember TNat as TN.
  has_type_cases (induction H) Case; intros; try solve by inversion.
  Case "T_Nat". exists n...
  Case "T_Subtype".
    apply IHhas_type in H0... subst.
    apply no_subtypes_nat in H...
Qed.

Lemma canonical_forms_nat' :
  forall G t T,
    has_type G t T -> T = TNat -> value t -> exists n, t = TNum n.
Proof with auto.
  intros.
  has_type_cases (induction H) Case; try solve by inversion...
  Case "T_Nat". exists n...
  Case "T_Subtype". apply no_subtypes_nat' in H...
Qed.



Lemma canonical_forms_lambda :
  forall (G : context) (t : term) (T A R : type),
    has_type G t (TArrow A R) -> value t ->
      exists (i : id) (ty : type) (te : term), t = TLambda i ty te.
Proof with auto.
  intros. remember (TArrow A R) as TArr.
  generalize dependent A; generalize dependent R.
  has_type_cases (induction H) Case; intros; try solve by inversion.
  Case "T_Lambda".
    exists x. exists T11. exists t12...
  Case "T_Subtype".
    subst.
    apply consistent_subtypes_lambda with T0 A R in H.
    inversion H. inversion H2. inversion H3; subst.
    apply IHhas_type with x0 x in H0...
Qed.


Lemma canonical_forms_lambda' :
  forall G t T A R,
    has_type G t T -> T = (TArrow A R) -> value t -> exists i ty te, t = TLambda i ty te.
Proof with auto.
  intros. generalize dependent A. generalize dependent R.
  has_type_cases (induction H) Case; intros; try solve by inversion.
  Case "T_Lambda". exists x. exists T11. exists t12...
  Case "T_Subtype". apply consistent_subtypes_lambda' with (A := A) (R := R) in H...
    inversion H. inversion H3. apply IHhas_type with (R := x0) (A := x)...
Qed.

(*
Lemma record_type_info1 :
  forall (G : context) (li : list id) (lt : list term) (T : type),
    has_type G (TLiteral li lt) T ->
    exists (lT : list type),
      Forall2 (fun x xT => has_type G x xT) lt lT /\ T = (TRecord li lT).
Proof.
  intros.
  
  remember (TLiteral li lt) as rem. induction H; inversion Heqrem; subst...
  *)


(* needs to be extended, we will need something about the types of the stuff in the literal.
Note that we can't say Forall2 (has_type G) lv lt, since in the presence of subtyping,
ids can move around. *)
Lemma record_type_info :
  forall (G : context) (liv lit : list id) (lv : list term) (lt : list type),
    has_type G (TLiteral liv lv) (TRecord lit lt) -> Uniq liv /\ length liv = length lv.
Proof with auto.
  intros. remember (TLiteral liv lv) as TLit. remember (TRecord lit lt) as TRec.
  generalize dependent liv; generalize dependent lv.
  generalize dependent lit; generalize dependent lt.
  has_type_cases (induction H) Case; intros; subst; try solve by inversion...
  Case "T_Literal".
    inversion HeqTRec; subst. inversion HeqTLit; subst...
  Case "T_Subtype".
    apply consistent_subtypes_record in H.
    inversion H; subst. inversion H1; subst.
    apply IHhas_type with (lt := x0) (lit := x)...
Qed.

Lemma record_type_info' :
  forall G t T liv lit lv lt,
    has_type G t T -> t = (TLiteral liv lv) -> T = (TRecord lit lt) ->
    Uniq liv /\ length liv = length lv.
Proof with eauto.
  intros. generalize dependent liv. generalize dependent lv.
  generalize dependent lit. generalize dependent lt.
  has_type_cases (induction H) Case; intros; try solve by inversion...
  Case "T_Literal". inversion H4. inversion H5. subst. subst...
  Case "T_Subtype". subst.
    apply consistent_subtypes_record' with (li' := lit) (lt' := lt) in H...
    inversion H. inversion H1. 
    apply IHhas_type with (lt := x0) (lit := x) (lv0 := lv) (liv0 := liv)...
Qed.


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


(* various canonical form lemmas - for some types, if a term has that type,
   it must be a particular kind of term *)

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



(* if a literal has a record type, there are several inferences we can make about it *)
Lemma has_type_literal_info :
  forall G li lv li' lt,
    has_type G (TLiteral li lv) (TRecord li' lt) ->
    length li = length lv /\ length li' = length lt /\ Uniq li /\ Uniq li'.
Proof with eauto.
  intros.
  remember (TLiteral li lv). remember (TRecord li' lt).
  generalize dependent li'. generalize dependent lt.
  has_type_cases (induction H) Case; intros; inversion Heqt; inversion Heqt0; subst.
  Case "T_Literal". inversion Heqt0. subst...
  Case "T_Subtype". remember H. clear Heqs. apply consistent_subtypes_record in s.
    inversion s. inversion H3. clear s H3. subst. 
    apply IHhas_type with (lt := x0) (li' := x) in H1...
    inversion H1. clear H1.
    inversion H3. inversion H4. clear H4.
    clear H3. clear IHhas_type.
    remember (TRecord li' lt). remember (TRecord x x0). generalize dependent li'.
    generalize dependent lt. generalize dependent x. generalize x0.
    subtype_cases (induction H) SCase; intros; inversion Heqt; inversion Heqt0; subst...
      SCase "Sub_refl". inversion H. subst...
      SCase "Sub_trans". remember H1. clear Heqs.
        apply consistent_subtypes_record in s. inversion s. inversion H8. subst.
        clear s. clear H8.
        remember H0. clear Heqh.
        apply IHsubtype1 with (x0 := x1) (x4 := x) (lt := x3) (li' := x2) in h...
        inversion h. inversion H9. inversion H11. clear h. clear H9. clear H11.
        apply T_Subtype with (T' := TRecord x2 x3) in H0...
      SCase "Sub_r_width". split... split... split... inversion H7...
      SCase "Sub_r_depth". subst...
      SCase "Sub_r_perm". split... split... split... 
        inversion H8...
Qed.

(* this is a stronger form of the above lemma, which is used in the proof of this one *)
Lemma literal_info :
  forall G li lv li' lt,
    has_type G (TLiteral li lv) (TRecord li' lt) ->
    (forall i T, In (i,T) (combine li' lt) -> exists t, In (i,t) (combine li lv) /\
                                                        has_type G t T) /\
    Uniq li /\ Uniq li' /\
    length li = length lv /\
    length li' = length lt.
Proof with eauto.
  intros.
  remember H. clear Heqh.
  apply has_type_literal_info in h. inversion h. inversion H1. inversion H3.
  split... clear H3. clear H1. clear h. intros.
  remember (TLiteral li lv).
  remember (TRecord li' lt). generalize dependent lt. generalize dependent li'.
  generalize dependent T.
  has_type_cases (induction H) Case; intros; inversion Heqt; inversion Heqt0; subst...
  Case "T_Literal". inversion Heqt0. subst. clear H10. clear Heqt. clear H3.
    clear H. clear Heqt0. clear H7. clear H4. clear H6. remember H8. clear Heqi0.
    apply in_combine_r in i0. remember H8. clear Heqi1. apply in_combine_l in i1.
    rewrite H1 in H0. generalize dependent lv. generalize dependent li'.
    induction lt0; intros; try solve by inversion;
    destruct lv; destruct li'; try solve by inversion.
    inversion H8. subst. inversion H5. subst. inversion H. subst. exists t. split...
    unfold In. simpl...
    simpl in *. assert (i <> i2).
    SCase "Proof of assertion". intro. subst. apply in_combine_l in H. inversion H2.
      contradiction.
    unfold not in H3.
    assert (In (i,T) (combine li' lt0)). inversion H8...
    clear H8.
    apply IHlt0 with (lv := lv) in H4...
    inversion H4. exists x. inversion H6. split...
    apply in_combine_r in H4...
    inversion H2...
    apply in_combine_l in H4...
    inversion H5...
  Case "T_Subtype".
    remember H.
    clear Heqs.
    remember s.
    clear Heqs0.
    apply consistent_subtypes_record in s0.
    inversion s0. inversion H8. clear s0. clear H8. subst.
    apply has_type_literal_info in H1.
    inversion H1. inversion H9. inversion H11.
    clear H1. clear H9. clear H11.
    apply record_subtype_inversion in s...
    inversion s. inversion H1. inversion H9.
    clear s. clear H1. clear H9.
    apply H14 in H3. inversion H3. inversion H1.
    clear H3. clear H1.
    inversion H11. subst.
    apply IHhas_type with (li' := x1) (lt := x2) (T := x3) in H9...
    inversion H9. exists x. inversion H1. split...
Qed.


(* needs to be extended, we will need something about the types of the stuff in the literal.
Note that we can't say Forall2 (has_type G) lv lt, since in the presence of subtyping,
ids can move around. *)
(*
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
    inversion H. inversion H1.  inversion H2. inversion H4.  subst.
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

*)
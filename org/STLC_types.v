Require Import SfLib.
Require Import util.
Require Import Permutation.

Hint Resolve beq_id_eq beq_id_false_not_eq.

(* types *)
Unset Elimination Schemes.
Inductive type : Type :=
| TBool : type
| TNat : type
| TArrow : type -> type -> type
| TRecord : list id -> list type -> type
| TTop : type.
Set Elimination Schemes.
(* The issue with induction is that the automatic induction function
 generated does not provide an inductive hypotheses for TRecords.
 This lets us provide our own induction function that fixes the issue.
 *)
Definition type_ind := 
fun (P : type -> Prop) (type_rect_tbool : P TBool) (type_rect_tnat : P TNat)
  (type_rect_tarrow : forall t : type, P t -> forall t0 : type, P t0 -> P (TArrow t t0))
  (type_rect_trecord : forall li lt, Forall P lt -> P (TRecord li lt))
  (type_rect_ttop : P TTop) =>
fix F (t : type) : P t :=
  match t as t0 return (P t0) with
  | TBool => type_rect_tbool
  | TNat => type_rect_tnat
  | TArrow t0 t1 => type_rect_tarrow t0 (F t0) t1 (F t1)
  | TRecord li lt =>
    type_rect_trecord li lt
                      ((fix forall_rec (lt' : list type)
                          : Forall P lt' :=
                            match lt' with
                              | nil => Forall_nil P
                              | t :: rest =>
                                Forall_cons t (F t) (forall_rec rest)
                            end)
                           lt)
  | TTop => type_rect_ttop
  end.

Hint Constructors type.

Tactic Notation "type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TBool"  | Case_aux c "TNat"
  | Case_aux c "TArrow" | Case_aux c "T_Record"
  | Case_aux c "TTop"].
  
  

(* subtype a b <-> a <: b *)
Unset Elimination Schemes.
Inductive subtype : type -> type -> Prop :=
  | Sub_refl : forall t, subtype t t
  | Sub_trans : forall a b c, subtype a b -> subtype b c -> subtype a c
  | Sub_top : forall t, subtype t TTop
  | Sub_arrow : forall a a' r r', subtype a' a ->
                                  subtype r r' ->
                                  subtype (TArrow a r) (TArrow a' r')
  | Sub_r_width : forall li li' lt lt',
                    length li = length lt ->
                    length li' = length lt' ->
                    subtype (TRecord (li++li') (lt++lt')) (TRecord li lt)
  | Sub_r_depth : forall li lt lt',
                    length li = length lt ->
                    length li = length lt' ->
                    Forall2 subtype lt lt' ->
                    subtype (TRecord li lt) (TRecord li lt')
  | Sub_r_perm : forall li lt li' lt',
                   Permutation (combine li lt) (combine li' lt') ->
                   subtype (TRecord li lt) (TRecord li' lt').
Set Elimination Schemes.

Hint Constructors subtype.

Definition subtype_ind := fun (P : type -> type -> Prop)
                              (f_refl : forall t, P t t)
                              (f_trans : forall a b c, P a b -> P b c -> P a c)
                              (f_top : forall t, P t TTop)
                              (f_arrow : forall a a' r r', P a' a ->
                                                           P r r' ->
                                                           P (TArrow a r) (TArrow a' r'))
                              (f_width : forall li li' lt lt',
                                           length li = length lt ->
                                           length li' = length lt' ->
                                           P (TRecord (li ++ li') (lt++lt'))
                                             (TRecord li lt))
                              (f_depth : forall li lt lt',
                                           length li = length lt ->
                                           length li = length lt' ->
                                           Forall2 P lt lt' ->
                                           P (TRecord li lt) (TRecord li lt'))
                              (f_perm : forall li lt li' lt',
                                          Permutation (combine li lt) (combine li' lt') ->
                                          P (TRecord li lt) (TRecord li' lt')) =>
fix F (t1 t2 : type) (st : subtype t1 t2) : P t1 t2 :=
  match st with
    | Sub_refl t => f_refl t
    | Sub_trans a b c ab bc => f_trans a b c (F a b ab) (F b c bc)
    | Sub_top t => f_top t
    | Sub_arrow a a' r r' a'a rr' => f_arrow a a' r r' (F a' a a'a) (F r r' rr')
    | Sub_r_width li li' lt lt' lli lli' => f_width li li' lt lt' lli lli'
    | Sub_r_depth li lt lt' llt llt' fora => f_depth li lt lt' llt llt'
      ((fix G lt lt' (fora : Forall2 subtype lt lt') : Forall2 P lt lt' :=
          match fora with
            | Forall2_nil => Forall2_nil P
            | Forall2_cons t t' lt lt' Rc Rr => Forall2_cons t t' (F t t' Rc) (G lt lt' Rr)
          end) lt lt' fora) 
    | Sub_r_perm li lt li' lt' perm => f_perm li lt li' lt' perm
  end.

Tactic Notation "subtype_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Sub_refl"    | Case_aux c "Sub_trans"
  | Case_aux c "Sub_top"     | Case_aux c "Sub_arrow"
  | Case_aux c "Sub_r_width" | Case_aux c "Sub_r_depth"
  | Case_aux c "Sub_r_perm" ].


Lemma no_subtypes_bool :
  forall T, subtype T TBool -> T = TBool.
Proof.
  intros. remember TBool as x.
  subtype_cases (induction H) Case; try solve [auto; inversion Heqx].
  Case "Sub_trans".
    assert (TB : c = TBool).
    (* this seems weird but it is necessary so that we remember [c = TBool] *)
    exact Heqx.
    apply IHsubtype0 in Heqx; subst.
    assert (TBool = TBool). reflexivity.
    apply IHsubtype in H. exact H.
Qed.

Lemma no_subtypes_bool' :
  forall T T', subtype T T' -> T' = TBool -> T = TBool.
Proof with auto.
  intros. subtype_cases (induction H) Case; try solve by inversion...
Qed.

Lemma no_subtypes_nat :
  forall T, subtype T TNat -> T = TNat.
Proof with auto.
  intros. remember TNat as TN.
  subtype_cases (induction H) Case; try solve by inversion...
  Case "Sub_trans".
    assert (TN : c = TNat). exact HeqTN.
    apply IHsubtype0 in HeqTN; subst.
    apply IHsubtype...
Qed.

Lemma no_subtypes_nat' :
  forall T T', subtype T T' -> T' = TNat -> T = TNat.
Proof with auto.
  intros. induction H; try solve by inversion...
Qed.

Lemma consistent_subtypes_lambda :
  forall (T A R : type),
    subtype T (TArrow A R) -> exists (A' R' : type), T = TArrow A' R'.
Proof with eauto.
  intros. remember (TArrow A R) as x.
  generalize dependent A; generalize dependent R.
  subtype_cases (induction H) Case; intros; try solve by inversion.
  Case "Sub_refl".
    exists A. exists R. exact Heqx.
  Case "Sub_trans".
    apply IHsubtype0 in Heqx.
    inversion Heqx. inversion H.
    apply IHsubtype in H0. exact H0.
  Case "Sub_arrow".
    exists a. exists r...
Qed.

Lemma consistent_subtypes_lambda' :
  forall T T' A R,
    subtype T T' -> T' = (TArrow A R) -> exists A' R', T = TArrow A' R'.
Proof with eauto.
  intros. generalize dependent A. generalize dependent R.
  subtype_cases (induction H) Case; intros; try solve by inversion.
  Case "Sub_refl". exists A. exists R...
  Case "Sub_trans". apply IHsubtype0 in H0. inversion H0.
    inversion H. apply IHsubtype in H1...
  Case "Sub_arrow". exists a. exists r...
Qed.


Lemma consistent_subtypes_record :
  forall (T : type) (li : list id) (lt : list type),
    subtype T (TRecord li lt) -> exists li' lt', T = TRecord li' lt'.
Proof with eauto.
  intros. remember (TRecord li lt) as TRec.
  generalize dependent li; generalize dependent lt.
  subtype_cases (induction H) Case; intros; try solve by inversion...
  Case "Sub_trans".
    apply IHsubtype0 in HeqTRec.
    inversion HeqTRec. inversion H...
Qed.

Lemma consistent_subtypes_record' :
  forall T T' li' lt',
    subtype T T' -> T' = TRecord li' lt' -> exists li lv, T = TRecord li lv.
Proof with eauto.
  intros. generalize dependent li'. generalize dependent lt'.
  subtype_cases (induction H) Case; intros; try solve by inversion...
  Case "Sub_trans". apply IHsubtype0 in H0.
    inversion H0. inversion H...
Qed.
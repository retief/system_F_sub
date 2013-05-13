Require Import SfLib.
Require Import util.
Require Import Permutation.
Require Import Coq.Logic.ClassicalFacts.
Require Import Permutation.

Axiom prop_ext : forall (P Q : Prop), (P <-> Q) <-> P = Q.

Axiom func_ext2 : forall {A B C : Type} (f g : A -> B -> C),
  (forall x y, f x y = g x y) <-> f = g.

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
                    Uniq li -> Uniq (li ++ li') ->
                    subtype (TRecord (li++li') (lt++lt')) (TRecord li lt)
  | Sub_r_depth : forall li lt lt',
                    length li = length lt ->
                    length li = length lt' ->
                    Uniq li ->
                    Forall2 subtype lt lt' ->
                    subtype (TRecord li lt) (TRecord li lt')
  | Sub_r_perm : forall li lt li' lt',
                   Permutation (combine li lt) (combine li' lt') ->
                   length li = length lt -> length li' = length lt' ->
                   Uniq li -> Uniq li' ->
                   subtype (TRecord li lt) (TRecord li' lt').
Set Elimination Schemes.

Hint Constructors subtype.

Definition subtype_ind := fun (P : type -> type -> Prop)
                              (f_refl : forall t, P t t)
                              (f_trans : forall a b c, P a b -> P b c ->
                                                       subtype a b -> subtype b c ->
                                                       P a c)
                              (f_top : forall t, P t TTop)
                              (f_arrow : forall a a' r r', P a' a ->
                                                           P r r' ->
                                                           subtype a' a ->
                                                           subtype r r' ->
                                                           P (TArrow a r) (TArrow a' r'))
                              (f_width : forall li li' lt lt',
                                           length li = length lt ->
                                           length li' = length lt' ->
                                           Uniq li -> Uniq (li ++ li') ->
                                           P (TRecord (li ++ li') (lt++lt'))
                                             (TRecord li lt))
                              (f_depth : forall li lt lt',
                                           length li = length lt ->
                                           length li = length lt' ->
                                           Uniq li ->
                                           Forall2 subtype lt lt' ->
                                           Forall2 P lt lt' ->
                                           P (TRecord li lt) (TRecord li lt'))
                              (f_perm : forall li lt li' lt',
                                          Permutation (combine li lt) (combine li' lt') ->
                                          length li = length lt ->
                                          length li' = length lt' ->
                                          Uniq li -> Uniq li' ->
                                          P (TRecord li lt) (TRecord li' lt')) =>
fix F (t1 t2 : type) (st : subtype t1 t2) : P t1 t2 :=
  match st with
    | Sub_refl t => f_refl t
    | Sub_trans a b c ab bc => f_trans a b c (F a b ab) (F b c bc) ab bc
    | Sub_top t => f_top t
    | Sub_arrow a a' r r' a'a rr' => f_arrow a a' r r' (F a' a a'a) (F r r' rr') a'a rr'
    | Sub_r_width li li' lt lt' lli lli' uli uli' => f_width li li' lt lt' lli lli' uli uli'
    | Sub_r_depth li lt lt' llt llt' uli fora => f_depth li lt lt' llt llt' uli fora
      ((fix G lt lt' (fora : Forall2 subtype lt lt') : Forall2 P lt lt' :=
          match fora with
            | Forall2_nil => Forall2_nil P
            | Forall2_cons t t' lt lt' Rc Rr => Forall2_cons t t' (F t t' Rc) (G lt lt' Rr)
          end) lt lt' fora) 
    | Sub_r_perm li lt li' lt' perm lli lli' uli uli' => f_perm li lt li' lt' perm lli lli' uli uli'
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
    apply IHsubtype2 in Heqx; subst.
    assert (TBool = TBool). reflexivity.
    apply IHsubtype1 in H1. exact H1.
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
    apply IHsubtype2 in HeqTN; subst.
    apply IHsubtype1...
Qed.

Lemma no_subtypes_nat' :
  forall T T', subtype T T' -> T' = TNat -> T = TNat.
Proof with auto.
  intros. induction H; try solve by inversion...
Qed.

Lemma consistent_subtypes_lambda :
  forall (T A R : type),
    subtype T (TArrow A R) -> exists (A' R' : type),
                                ((T = TArrow A' R') /\ subtype A A' /\ subtype R' R).
Proof with eauto.
  intros. remember (TArrow A R) as x.
  generalize dependent A; generalize dependent R.
  subtype_cases (induction H) Case; intros; try solve by inversion.
  Case "Sub_refl".
    exists A. exists R. split; try split; auto.
  Case "Sub_trans".
    apply IHsubtype2 in Heqx.
    inversion Heqx. inversion H1.
    inversion H2. inversion H4.
    clear Heqx. clear H1. clear H2. clear H4.
    apply IHsubtype1 in H3.
    inversion H3. inversion H1.
    inversion H2. inversion H7.
    clear H1. clear H3. clear H2. clear H7.
    exists x1, x2.
    split; try split...
  Case "Sub_arrow".
    exists a. exists r. inversion Heqx. subst. split; try split...
Qed.

Lemma consistent_subtypes_lambda' :
  forall T T' A R,
    subtype T T' -> T' = (TArrow A R) -> exists A' R', T = TArrow A' R'.
Proof with eauto.
  intros. generalize dependent A. generalize dependent R.
  subtype_cases (induction H) Case; intros; try solve by inversion.
  Case "Sub_refl". exists A. exists R...
  Case "Sub_trans". apply IHsubtype2 in H1. inversion H1.
    inversion H2. apply IHsubtype1 in H3...
  Case "Sub_arrow". exists a. exists r...
Qed.

Lemma consistent_subtypes_record :
  forall (T : type) (li : list id) (lt : list type), 
    subtype T (TRecord li lt) ->
    (exists li' lt', T = TRecord li' lt').
Proof with eauto.
  intros T li lt Hsub. remember (TRecord li lt) as TRec.
  generalize dependent li; generalize dependent lt.
  subtype_cases (induction Hsub) Case; intros; try solve by inversion...
  Case "Sub_trans".
    apply IHHsub2 in HeqTRec...
    inversion HeqTRec. inversion H...
Qed.

Lemma consistent_subtypes_record_ex :
  forall (T : type) (li : list id) (lt : list type), length li = length lt -> Uniq li ->
    subtype T (TRecord li lt) ->
    (exists li' lt', T = TRecord li' lt' /\ length li' = length lt' /\ Uniq li').
Proof with eauto.
  intros T li lt Hlen Huniq Hsub. remember (TRecord li lt) as TRec.
  generalize dependent li; generalize dependent lt.
  subtype_cases (induction Hsub) Case; intros; try solve by inversion...
  Case "Sub_trans".
    apply IHHsub2 in HeqTRec...
    inversion HeqTRec. inversion H... inversion H0... inversion H2... subst.    
  Case "Sub_r_width".
    inversion HeqTRec; subst. clear HeqTRec.
    exists (li0 ++ li'). exists (lt0 ++ lt').
    split... split... repeat rewrite -> app_length. subst...
Qed.

Lemma consistent_subtypes_record' :
  forall T T' li' lt',
    subtype T T' -> T' = TRecord li' lt' -> exists li lv, T = TRecord li lv.
Proof with eauto.
  intros. generalize dependent li'. generalize dependent lt'.
  subtype_cases (induction H) Case; intros; try solve by inversion...
  Case "Sub_trans". apply IHsubtype2 in H1.
    inversion H1. inversion H2...
Qed.


Lemma record_subtype_inversion :
  forall (li : list id) (lT : list type) (S : type),
    length li = length lT -> Uniq li ->
    subtype S (TRecord li lT) -> exists li' lT',
      S = (TRecord li' lT') /\
      forall i T, In (i, T) (combine li lT) -> (exists T', In (i, T') (combine li' lT') /\ subtype T' T).

Proof with auto.
  intros li lT S Hlen Huniq Hsub.
  remember Hsub.
  clear Heqs.
  apply consistent_subtypes_record_ex in s...
  inversion s as [li' s']. inversion s' as [lT' s''].
  inversion s''. inversion H0. subst. clear s s' s'' H0.
  exists li'. exists lT'.
split...

remember (TRecord li' lT') as left_rec;
remember (TRecord li lT) as right_rec.
generalize dependent li.
generalize dependent lT.
generalize dependent li'.
generalize dependent lT'.
subtype_cases (induction Hsub) Case; subst; intros; subst;
  try solve by inversion...

Case "Sub_refl".
inversion Heqright_rec; subst. clear Heqright_rec.

exists T; split...


Case "Sub_trans".
apply consistent_subtypes_record_ex in Hsub2...
inversion Hsub2. inversion H0. inversion H3. inversion H5. clear H0 H3 H5 Hsub2.
subst. remember Huniq. clear Hequ.
apply IHHsub2 with (li' := x) (lT' := x0) (lT0 := lT) (li0 := li) (i := i) (T := T) in H...
inversion H. inversion H0. clear H. clear H0.
apply IHHsub1 with (lT'0 := lT') (li'0 := li') (li := x) (lT := x0) in H3...
inversion H3. inversion H. clear H. clear H3.
exists x2. split... apply Sub_trans with (b := x1)...
Case "Sub_r_width".
  inversion Heqleft_rec; subst. clear Heqleft_rec.
  inversion Heqright_rec; subst. clear Heqright_rec.
  exists T. split...
  rewrite <- combine_app...
  apply in_or_app. left...

Case "Sub_r_depth".
  inversion Heqleft_rec. inversion Heqright_rec.
  clear Heqleft_rec. clear Heqright_rec. subst. subst.
  clear H1 H3. clear H H5 H0. generalize dependent li0.
  induction H2; intros; destruct li0; try solve by inversion. simpl in *.
   remember (beq_id i i0). destruct b. apply beq_id_eq in Heqb. subst.
   inversion H6. inversion H0. subst. clear H0 H6.
   exists x...
   apply in_combine_l in H0. inversion Huniq. contradiction.
   symmetry in Heqb.
   apply beq_id_false_not_eq in Heqb.
   inversion H6.
   inversion H0. symmetry in H3. contradiction.
   inversion Hlen. inversion Huniq. apply IHForall2 in H3... subst.
   inversion H3. inversion H1. clear H1 H3. exists x0. split...
Case "Sub_r_perm".
  inversion Heqleft_rec; subst. clear Heqleft_rec.
  inversion Heqright_rec; subst. clear Heqright_rec.
  exists T. split...
  apply permutation_in with (i, T) (combine li'0 lT') (combine li0 lT) in H...
Qed.


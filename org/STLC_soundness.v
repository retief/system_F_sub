Require Import SfLib.
Require Import util.
Require Import List.
Require Import Permutation.
Require Import STLC_types.
Require Import STLC_terms.
Require Import STLC_has_type.
Require Import STLC_step.

Theorem progress : forall t T, 
     has_type empty t T ->
     value t \/ exists t', t ==> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as gamma.
  has_type_cases (induction Ht) Case; subst... 
  Case "T_Var". inversion H.
  Case "T_App". right. destruct IHHt1...
    SCase "t1 is a value". destruct IHHt2...
      SSCase "t2 is a value".
        apply canonical_forms_lambda with (A := T11) (R := T12) in Ht1...
        inversion Ht1. inversion H1. inversion H2. subst.
        exists ([x := t2] x1). constructor...
      SSCase "t2 steps". inversion H0. exists (TApp t1 x). constructor...
    SCase "t1 steps". inversion H. exists (TApp x t2). constructor...
  Case "T_If". right. destruct IHHt1...
    SCase "t1 is a value". apply canonical_forms_bool in Ht1...
      destruct Ht1; subst.
      SSCase "if true". exists t2. constructor.
      SSCase "if false". exists t3. constructor.
    inversion H. exists (TIf x t2 t3). constructor...
  Case "T_Plus". right. destruct IHHt1... destruct IHHt2...
    apply canonical_forms_nat in Ht1...
    apply canonical_forms_nat in Ht2...
    inversion Ht1... inversion Ht2... subst.
    exists (TNum (x+x0))...
    inversion H0. exists (TPlus l x)...
    inversion H. exists (TPlus x r)...
  Case "T_EqNat". right. destruct IHHt1... destruct IHHt2...
    apply canonical_forms_nat in Ht1...
    apply canonical_forms_nat in Ht2...
    inversion Ht1... inversion Ht2... subst.
    remember (beq_nat x x0). destruct b. exists TTrue...
    exists TFalse...
    inversion H0. exists (TEqNat l x)...
    inversion H. exists (TEqNat x r)...
  Case "T_Literal". generalize dependent li.
    induction H2; intros; subst...
    SCase "Inductive".
      destruct H...
      SSCase "value x".
        destruct li; simpl in *; try solve by inversion.
        inversion H3; subst.
        inversion H0. inversion H1. inversion H4.
        destruct (IHForall2 H10 li H6 H7 H12)...
        SSSCase "value TLiteral".
          left.
          apply v_literal; simpl.
          apply Forall_cons...
          inversion H13...
        SSSCase "exists t' : TLiteral ==> t'".
          right. inversion H13; subst. inversion H14; subst.
          exists (TLiteral (i :: li0 ++ i0 :: ri) (x :: lv ++ v' :: rv)).
          assert (Uniq (i :: li0)).
            SSSSCase "Proof of assertion".
              destruct (@uniq_app id (i :: li0) (i0 :: ri))...
          apply ST_Literal with (li := (i :: li0)) (lv := x :: lv)...
              apply v_literal. constructor...
              inversion H15... simpl. rewrite H16...
      SSCase "exists t' : x ==> t'".
        right. inversion H. destruct li; simpl in *; try solve by inversion.
        exists (TLiteral (i :: li) (x0 :: l)).
        apply ST_Literal with (lv := nil) (li := nil) (v := x) (v' := x0)...
  Case "T_Access".
    destruct IHHt...
    SCase "TLiteral is a value". right. eapply record_type_info in Ht...
      inversion Ht. apply in_lookup in H...
    SCase "TLiteral setps". right. inversion H1. exists (TAccess x i)...
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
                appears_free_in x (TEqNat l r)
| AFI_Record : forall x id t leftI rightI leftT rightT,
                 appears_free_in x t ->
                 appears_free_in x (TLiteral (leftI ++ id :: rightI) (leftT ++ t :: rightT))
| AFI_Access : forall x t id,
                 appears_free_in x t ->
                 appears_free_in x (TAccess t id).

Tactic Notation "afi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "AFI_Var"    | Case_aux c "AFI_App1"
  | Case_aux c "AFI_App2"   | Case_aux c "AFI_Lambda"
  | Case_aux c "AFI_If1"    | Case_aux c "AFI_If2"
  | Case_aux c "AFI_If3"    | Case_aux c "AFI_Plus1"
  | Case_aux c "AFI_Plus2"  | Case_aux c "AFI_EqNat1"
  | Case_aux c "AFI_EqNat2" | Case_aux c "AFI_Record"
  | Case_aux c "AFI_Access" ].

Hint Constructors appears_free_in.

Definition closed (t:term) := forall x, ~ appears_free_in x t.

Lemma free_in_context : forall x t T gamma,
                          appears_free_in x t ->
                          has_type gamma t T ->
                          exists T', gamma x = Some T'.
Proof with eauto.
  intros x t T gamma H_afi H_has_type. generalize dependent gamma.
  generalize dependent T.
  afi_cases (induction H_afi) Case; intros;
    [ remember (TVar x) as t_rem
    | remember (TApp t1 t2) as t_rem
    | remember (TApp t1 t2) as t_rem
    | remember (TLambda y T11 t12) as t_rem
    | remember (TIf t1 t2 t3) as t_rem
    | remember (TIf t1 t2 t3) as t_rem
    | remember (TIf t1 t2 t3) as t_rem
    | remember (TPlus l r) as t_rem
    | remember (TPlus l r) as t_rem
    | remember (TEqNat l r) as t_rem
    | remember (TEqNat l r) as t_rem
    | remember (TLiteral (leftI ++ id :: rightI) (leftT ++ t :: rightT)) as t_rem
    | remember (TAccess t id) as t_rem
    ]; induction H_has_type; inversion Heqt_rem; subst...
    Case "AFI_Lambda".
      SCase "T_Lambda".
        apply IHH_afi in H_has_type.
        apply not_eq_beq_id_false in H. rewrite extend_neq in H_has_type; assumption.
    Case "AFI_Record".
      apply Forall2_app_inv_l in H3. inversion H3.
      inversion H4. inversion H5. inversion H7. inversion H8. subst.
      apply IHH_afi with (T := y). assumption.
Qed.

Lemma context_invariance : forall gamma gamma' t T,
                             has_type gamma t T ->
                             (forall x, appears_free_in x t -> gamma x = gamma' x) ->
                             has_type gamma' t T.
Proof with eauto.
  intros.
  generalize dependent gamma'.
  has_type_cases (induction H) Case; intros; try solve [auto].
  Case "T_Var".
    apply T_Var. rewrite <- H0...
  Case "T_Lambda".
    apply T_Lambda. apply IHhas_type. intros x0 Hafi.
    unfold SfLib.extend. remember (beq_id x x0). destruct b...
  Case "T_App".
    eapply T_App...
  Case "T_Literal".
    eapply T_Literal... generalize dependent li. induction H2; intros...
    SCase "Inductive".
      destruct li; try solve by inversion.
      constructor... apply H. intros. apply H5.
      apply AFI_Record with (leftI := nil) (leftT := nil)...
      inversion H3; subst. eapply IHForall2... intros.
      inversion H4. apply H10. intros. apply H5.
      inversion H6.
      apply AFI_Record with (leftI := i :: leftI)
                              (leftT := x :: leftT)
                              (rightI := rightI)
                              (rightT := rightT)...
  Case "T_Access".
    eapply T_Access...
  Case "T_Subtype".
    apply IHhas_type in H1. apply T_Subtype with (T := T)...
Qed.


Lemma substitution_preserves_typing : forall gamma x U t t' T,
                                        has_type (extend gamma x U) t T ->
                                        has_type empty t' U ->
                                        has_type gamma ([x:=t']t) T.
Proof with eauto.
  intros gamma x U t t' T Ht Ht'.
  generalize dependent gamma. generalize dependent T.
  term_cases (induction t) Case; intros T gamma H';
  remember (extend gamma x U); simpl;
  [ rename i into y; remember (TVar y) as rem
  | remember (TApp t1 t2) as rem
  | rename i into y; remember (TLambda y t t0) as rem
  | remember TTrue as rem
  | remember TFalse as rem
  | remember (TIf t1 t2 t3) as rem
  | remember (TNum n) as rem
  | remember (TPlus t1 t2) as rem
  | remember (TEqNat t1 t2) as rem
  | remember (TLiteral li lv) as rem
  | remember (TAccess t i) as rem];
  induction H'; inversion Heqrem; subst...

  Case "TVar".
    remember (beq_id x y) as e. destruct e.
      SCase "x=y". apply beq_id_eq in Heqe. subst. rewrite extend_eq in H.
        inversion H. subst. eapply context_invariance... intros x Hcontra.
        destruct (free_in_context _ _ T empty Hcontra)... inversion H0.
      SCase "x<>y". constructor. rewrite extend_neq in H...
  Case "TLambda".
    apply T_Lambda. remember (beq_id x y) as e. destruct e.
    SCase "x=y".
      eapply context_invariance...
      apply beq_id_eq in Heqe; subst.
      intros x Hafi. unfold SfLib.extend. unfold extend.
      remember (beq_id y x) as e. destruct e...
    SCase "x<>y".
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold extend. unfold SfLib.extend.
      remember (beq_id y z) as e0. destruct e0...
      apply beq_id_eq in Heqe0. subst.
      rewrite <- Heqe...
  Case "TLiteral".
    apply T_Literal...
    apply weird_forall_forall2 with (l' := lt) (g := gamma) in H...
    rewrite map_length...
  Case "TAccess".
    eapply T_Access with (v := subst x t' v)...
    inversion H'; subst; rewrite combine_map; apply in_map_iff; exists (i,v)...
Qed.



Lemma lambda_body_type :
  forall x T t12 T12 T11,
    has_type empty (TLambda x T t12) (TArrow T11 T12) ->
    has_type (extend empty x T11) t12 T12.
Proof with eauto.
  intros.
  remember (TLambda x T t12).
  remember (TArrow T11 T12).
  remember empty.
  generalize dependent T11.
  generalize dependent T12.
  generalize dependent t12.
  has_type_cases (induction H) Case; try solve [intros;
                                                 inversion Heqt;
                                                 inversion Heqt0;
                                                 subst; subst; auto].
  intros.
  remember H.
  clear Heqs.
  inversion Heqt.
  inversion Heqt0.
  subst.
  clear H2.
  clear H1.
  apply consistent_subtypes_lambda in H.
  inversion H as [T21]. inversion H1 as [T22]. inversion H2. inversion H4. subst.
  clear H. clear H1. clear H2. clear H4.
  apply T_Subtype with (T := T22)...
  assert ((TLambda x T t12) = (TLambda x T t12))...
  apply IHhas_type with (T12 := T22) (T11 := T21) in H...
  clear IHhas_type. clear s. clear H6. clear H0.
  remember (extend empty x T11) as sub.
  remember (extend empty x T21) as sup.
  assert (forall i, not (i = x) -> sup i = sub i).
    SCase "Proof of assertion". intros. subst. unfold extend.
      remember (beq_id x i). destruct b... contradict H0. apply beq_id_eq in Heqb...
  assert (sub x = Some T11). subst. unfold extend. rewrite <- beq_id_refl...
  assert (sup x = Some T21). subst. unfold extend. rewrite <- beq_id_refl...
  clear Heqsup.
  clear Heqsub.
  generalize dependent sup.
  generalize dependent sub.
  generalize dependent T22.
  term_cases (induction t12) SCase; intros...
  SCase "TVar".
    remember (TVar i).
    has_type_cases (induction H) SSCase; try solve by inversion...
      SSCase "T_Var". inversion Heqt. subst.
        remember (beq_id i x). destruct b.
        SSSCase "i=x". apply (beq_id_eq i x) in Heqb. subst.
          rewrite H in H2... inversion H2. subst.
          apply T_Subtype with (T := T11)...
        SSSCase "i!=x". symmetry in Heqb. apply beq_id_false_not_eq in Heqb.
          apply H0 in Heqb. constructor. rewrite <- Heqb...
  SCase "TApp".
    remember (TApp t12_1 t12_2).
    has_type_cases (induction H) SSCase; inversion Heqt; subst...
  SCase "TLambda".
    remember (beq_id i x). destruct b.
    SSCase "i=x". apply beq_id_eq in Heqb.
      remember (TLambda i t t12).
      has_type_cases (induction H) SSSCase; inversion Heqt0; subst...
        SSSCase "T_Lambda". clear Heqt0. clear IHhas_type.
          apply T_Lambda. apply context_invariance with (gamma := (SfLib.extend G x t))...
          intros. unfold SfLib.extend. remember (beq_id x x0).
          destruct b...
          SSSSCase "x<>x0". symmetry in Heqb. apply beq_id_false_not_eq in Heqb.
            assert (x0 <> x)...
    SSCase "i<>x". 
      remember (TLambda i t t12).
      has_type_cases (induction H) SSSCase; inversion Heqt0; subst...
      SSSCase "T_Lambda".
        clear IHhas_type. constructor. apply IHt12 with (sup := SfLib.extend G i t)...
        unfold SfLib.extend. rewrite <- Heqb...
        intros. unfold SfLib.extend. apply H0 in H3. remember (beq_id i i0).
        destruct b...
        unfold SfLib.extend. rewrite <- Heqb...
  SCase "TTrue".
    remember TTrue.
    induction H; inversion Heqt; subst...
  SCase "TFalse".
    remember TFalse.
    induction H; inversion Heqt; subst...
  SCase "TIf".
    remember (TIf t12_1 t12_2 t12_3).
    induction H; inversion Heqt; subst...
  SCase "TNum".
    remember (TNum n).
    induction H; inversion Heqt; subst...
  SCase "TPlus".
    remember (TPlus t12_1 t12_2).
    induction H; inversion Heqt; subst...
  SCase "TEqNat".
    remember (TEqNat t12_1 t12_2).
    induction H; inversion Heqt; subst...
  SCase "TLiteral".
    remember (TLiteral li lv).
    has_type_cases (induction H0) SSCase; inversion Heqt; subst...
    SSCase "T_Literal". clear H7. constructor...
      generalize dependent lt. generalize dependent li.
      induction H; intros.
        SSSCase "Forall_nil". destruct lt; try solve by inversion...
        SSSCase "Forall_cons". destruct lt; try solve by inversion...
          destruct li; try solve by inversion...
          constructor. inversion H8...
          apply IHForall with (li := li)...
          inversion H6... inversion H8...
  SCase "TAccess".
    remember (TAccess t12 i).
    induction H; inversion Heqt; subst...
Qed.

Lemma literal_info :
  forall G li lv lt,
    has_type G (TLiteral li lv) (TRecord li lt) ->
    Forall2 (has_type G) lv lt /\
    Uniq li /\
    length li = length lv /\
    length li = length lt.
Proof with eauto.
  intros. remember (TLiteral li lv).
  remember (TRecord li lt).
  has_type_cases (induction H) Case; inversion Heqt; inversion Heqt0; subst...
Admitted.

Theorem preservation : forall t t' T,
                         has_type empty t T ->
                         t ==> t' ->
                         has_type empty t' T.
Proof with eauto.
  remember empty as gamma.
  intros t t' T HT. generalize dependent t'.
  has_type_cases (induction HT) Case;
    intros t' HE; subst;  
       try solve [inversion HE; subst; auto]...
  Case "T_App".
    inversion HE; subst...
    (* Most of the cases are immediate by induction, 
       and eauto takes care of them *)
    SCase "ST_AppAbs".
      apply substitution_preserves_typing with T11...
      apply lambda_body_type with (T := T)...
  Case "T_Literal". 
  inversion HE; subst. constructor...
    SCase "types match up". generalize dependent lt. generalize dependent li0.
      induction lv0; intros.
      SSCase "Base". simpl in *.
        destruct lt; try solve by inversion...
        constructor...
        inversion H2. subst. apply H10...
        inversion H3...
      SSCase "Inductive". destruct li0; try solve by inversion.
        destruct lt; try solve by inversion. constructor...
        inversion H3... inversion H6. inversion H5. eapply IHlv0...
        inversion H1...
        inversion H2...
        inversion H3...
        rewrite app_length in *. rewrite app_length in * ...
  Case "T_Access". inversion HE; subst...
    apply literal_info in HT; inversion HT.
    inversion HT as [Forall_HT [HUniq [H_li_lv H_li_lt]]].
    SCase "literal is value".
      apply lookup_in_pair in H6... 
      apply Forall2_combine_in with (xs := lv) (ys := lt)...
      apply combine_3 with (xs := li) (x := i)...
    SCase "literal steps".
      inversion H4; subst. apply IHHT in H4...
      apply literal_info in H4. subst.
      remember (beq_id i i0); destruct b...
      SSCase "i=i0". apply beq_id_eq in Heqb; subst.
        apply T_Access with (v := v') (lt := lt)...
        rewrite <- combine_app... apply in_or_app. right. simpl...
      SSCase "i!=i0". apply T_Access with (v := v) (lt := lt)...
        rewrite <- combine_app... rewrite <- combine_app in H...
        apply in_or_app... apply in_app_or in H. inversion H...
        right. simpl in *. right. inversion H1... inversion H2. subst.
        rewrite <- beq_id_refl in Heqb. inversion Heqb.
Qed.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.
  

Definition stuck (t : term) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary soundness : forall t t' T,
  has_type empty t T -> 
  t ==>* t' ->
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

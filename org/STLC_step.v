Require Import SfLib.
Require Import util.
Require Import STLC_types.
Require Import STLC_terms.

Reserved Notation "t1 '==>' t2" (at level 40).
(* Note: Induction should be fine here. No descent into the list of a literal
   is required. *)
Inductive step : term -> term -> Prop :=
| ST_AppLambda : forall x T t12 v2,
                   value v2 -> (TApp (TLambda x T t12) v2) ==> [x := v2]t12
| ST_App1 : forall t1 t1' t2, t1 ==> t1' -> TApp t1 t2 ==> TApp t1' t2
| ST_App2 : forall v1 t2 t2', value v1 -> t2 ==> t2' -> TApp v1 t2 ==> TApp v1 t2'
| ST_IfTrue : forall t1 t2, TIf TTrue t1 t2 ==> t1
| ST_IfFalse : forall t1 t2, TIf TFalse t1 t2 ==> t2
| ST_If : forall t1 t1' t2 t3, t1 ==> t1' -> TIf t1 t2 t3 ==> TIf t1' t2 t3
| ST_Plus : forall n m, TPlus (TNum n) (TNum m) ==> TNum (n + m)
| ST_PlusL : forall l l' r, l ==> l' -> TPlus l r ==> TPlus l' r
| ST_PlusR : forall l r r', value l -> r ==> r' -> TPlus l r ==> TPlus l r'
| ST_EqNatT : forall n m, beq_nat n m = true ->
                          TEqNat (TNum n) (TNum m) ==> TTrue
| ST_EqNatF : forall n m, beq_nat n m = false ->
                          TEqNat (TNum n) (TNum m) ==> TFalse
| ST_EqNatL : forall l l' r, l ==> l' -> TEqNat l r ==> TEqNat l' r
| ST_EqNatR : forall l r r', value l -> r ==> r' -> TEqNat l r ==> TEqNat l r'
| ST_Literal : forall li lv ri rv i v v', value (TLiteral li lv) ->
                                               length li = length lv ->
                                               v ==> v' ->
                                               TLiteral (li ++ (i :: ri))
                                                        (lv ++ (v :: rv)) ==>
                                                 TLiteral (li ++ (i :: ri))
                                                          (lv ++ (v' :: rv))
| ST_Access : forall li lv i v, value (TLiteral li lv) ->
                                  lookup i li lv = Some v ->
                                  TAccess (TLiteral li lv) i ==> v
| ST_AccessS : forall r r' i, r ==> r' -> TAccess r i ==> TAccess r' i
    where "t1 '==>' t2" := (step t1 t2).

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
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).


Lemma values_no_step : forall (t : term), value t -> ((exists t', t ==> t') -> False).
Proof with auto.
  intros t HValue HStep.
  value_cases (induction HValue) Case; try (inversion HStep as [t' HStep']; inversion HStep'; subst)...
  Case "v_literal".
    apply Forall_app in H.
    inversion H. inversion H1; subst.
    apply H7. exists v'...
Qed.


Theorem step_determinism : forall (t t'1 t'2 : term),
  t ==> t'1 -> t ==> t'2 -> t'1 = t'2.
Proof with eauto.
  intros. generalize dependent t'1. generalize dependent t'2.
  term_cases (induction t) Case; intros; try solve by inversion.
  Case "TApp".
    inversion H; inversion H0; subst; try solve by inversion...
    SCase "steps with ST_AppLambda".
      inversion H5; subst...
    SCase "t2 is a value but steps".
      apply values_no_step in H4. inversion H4. exists t2'...
    SCase "t1 steps".
      assert (t1' = t1'0). apply IHt1...
      subst...
    SCase "t1 steps and is a value".
      apply values_no_step in H7. inversion H7. exists t1'...
    SCase "t2 steps and is a value".
      apply values_no_step in H9. inversion H9. exists t2'...
    SCase "t1 is a value but steps".
      apply values_no_step in H3. inversion H3. exists t1'...
    SCase "t2 steps".
      assert (t2' = t2'0). apply IHt2...
      subst...
  Case "TIf".
    inversion H; inversion H0; subst; try solve by inversion...
    assert (t1' = t1'0). apply IHt1...
    subst...
  Case "TPlus".
    inversion H; inversion H0; subst; try solve by inversion...
    SCase "t1 and t2 are numbers".
      inversion H5; inversion H6; subst...
    SCase "t1 steps".
      assert (l' = l'0). apply IHt1...
      subst...
    SCase "t1 steps and is a value".
      apply values_no_step in H7. inversion H7... exists l'...
    SCase "t1 is a value and steps".
      apply values_no_step in H3. inversion H3... exists l'...
    SCase "t2 steps".
      assert (r' = r'0). apply IHt2...
      subst...
  Case "TEqNat".
    inversion H; inversion H0; subst; try solve by inversion...
    SCase "t1 and t2 are numbers; true/false".
      inversion H7; inversion H5; subst.
      rewrite -> H8 in H4.
      inversion H4.
    SCase "t1 and t2 are numbers; false/true".
      inversion H7; inversion H5; subst.
      rewrite -> H8 in H4.
      inversion H4.
    SCase "t1 steps".
      assert (l' = l'0). apply IHt1...
      subst...
    SCase "t1 steps and is a value".
      apply values_no_step in H7. inversion H7. exists l'...
    SCase "t1 is a value and steps".
      apply values_no_step in H3. inversion H3. exists l'...
    SCase "t2 steps".
      assert (r' = r'0). apply IHt2...
      subst...
  Case "TLiteral".
    inversion H0; inversion H1; subst... clear H0 H1.
    inversion H4; inversion H10; subst.
    apply append_length in H8; inversion H8; clear H8; subst...
    inversion H2; subst; clear H2.
    Focus 2. 
    apply append_length in H9; inversion H9; subst...
    apply append_length in H8; inversion H8; subst...
    inversion H2; subst.
    assert (v' = v'0). apply Forall_app in H; inversion H.
      inversion H12; subst.
      apply H16...
    subst.
    inversion H3; subst...
inversion H8; subst...
inversion H9. inversion H12; subst...

 clear H9... subst. apply append_length in H8...
    assert (lv1 = lv0). 
    admit.
  Case "TAccess".
    inversion H; inversion H0; subst... clear H H0.
    SCase "literal is a value".
      inversion H6; subst.
      rewrite -> H5 in H10.
      inversion H10...
    SCase "literal is a value but steps".
      apply values_no_step in H3. inversion H3. exists r'...
    SCase "literal is a value but steps".
      apply values_no_step in H7. inversion H7. exists r'...
    SCase "literal steps".
      assert (r' = r'0). apply IHt...
      subst...

Admitted.

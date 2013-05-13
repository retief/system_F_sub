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
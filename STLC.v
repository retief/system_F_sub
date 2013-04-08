Require Import SfLib.
Require Import partial_map.

Module STLC.

(* types *)
Inductive type : Type :=
| TBool : type
| TArrow : type -> type -> type.


(* terms *)
Inductive term : Type :=
| TVar : id -> term
| TApp : term -> term -> term
| TLambda : id -> type -> term -> term
| TTrue : term
| TFalse : term
| TIf : term -> term -> term -> term.

Notation "\ x : t1 . y" := (TLambda x t1 y) (at level 50).


Inductive value : term -> Prop :=
| v_abs : forall x T t, value (TLambda x T t)
| v_true : value TTrue
| v_false : value TFalse.


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
where "t1 '=>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppLambda" | Case_aux c "ST_App1"
  | Case_aux c "ST_App2"      | Case_aux c "ST_IfTrue"
  | Case_aux c "ST_IfFalse"   | Case_aux c "ST_If" ].

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
         has_type G (TIf t1 t2 t3) T.


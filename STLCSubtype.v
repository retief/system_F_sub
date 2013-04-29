Require Import SfLib.
Require Import partial_map.
Require Import Permutation.

Module STLC.

Hint Resolve beq_id_eq beq_id_false_not_eq.

Inductive Uniq {t : Type} : list t -> Prop :=
| Uniq_nil : Uniq []
| Uniq_cons : forall x xs, not (In x xs) -> Uniq xs -> Uniq (x :: xs).

Hint Constructors Uniq.

Lemma uniq_app {T} : forall (l1 l2 : list T), Uniq (l1 ++ l2) -> Uniq l1 /\ Uniq l2.
Proof with auto.
  induction l1; intros... inversion H; subst. apply IHl1 in H3. inversion H3. split...
    constructor... intro. contradict H2. apply in_or_app. left...
Qed.

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

Definition Admitted {T : Type} : T. admit. Qed.

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

Reserved Notation "t1 '==>' t2" (at level 40).
(* Note: Induction should be fine here *)
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

Definition context := partial_map type.

(* TODO: Fix induction like type induction on has_type in the
 T_Literal case doesn't have that the Forall2's has_types
 imply anything *)
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
  (f10 : forall G t T T', P G t T -> subtype T T' -> P G t T') =>
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
    | T_Subtype G t T T' ht st => f10 G t T T' (F G t T ht) st
  end.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var"   | Case_aux c "T_Lambda"
  | Case_aux c "T_App"   | Case_aux c "T_True"
  | Case_aux c "T_False" | Case_aux c "T_If"
  | Case_aux c "T_Nat"   | Case_aux c "T_Plus"
  | Case_aux c "T_EqNat" | Case_aux c "T_Literal"
  | Case_aux c "T_Access" | Case_aux c "T_Subtype" ].

Hint Constructors has_type.
Hint Unfold beq_nat beq_id extend.

Lemma consistent_subtypes_lambda :
  forall T T' A R,
    subtype T T' -> T' = (TArrow A R) -> exists A' R', T = TArrow A' R'.
Proof with auto.
  intros. generalize dependent A. generalize dependent R.
  subtype_cases (induction H) Case; intros; try solve by inversion.
  Case "Sub_refl". exists A. exists R...
  Case "Sub_trans". apply IHsubtype0 in H0. inversion H0.
    inversion H. apply IHsubtype in H1...
  Case "Sub_arrow". exists a. exists r...
Qed.

Lemma canonical_forms_lambda :
  forall G t T A R,
    has_type G t T -> T = (TArrow A R) -> value t -> exists i ty te, t = TLambda i ty te.
Proof with auto.
  intros. generalize dependent A. generalize dependent R.
  has_type_cases (induction H) Case; intros; try solve by inversion.
  Case "T_Lambda". exists x. exists T11. exists t12...
  Case "T_Subtype". apply consistent_subtypes_lambda with (A := A) (R := R) in H...
    inversion H. inversion H2. apply IHhas_type with (R := x0) (A := x)...
Qed.

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
        value_cases (inversion H) SSSCase; subst;
          try solve [apply canonical_forms_lambda with (A := T11) (R := T12) in Ht1; auto;
                     inversion Ht1 as (e,he); inversion he as (e1, he1);
                     inversion he1 as (e2,he2); inversion he2].
        SSSCase "v_abs". exists ([x := t2] t). constructor...
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
          left. (* (TLiteral ((i0, t) :: l)) is a value *)
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
            (* first prove that (TLiteral ((i0, t) :: l0)) is a value *)
              apply v_literal. constructor...
              inversion H15... simpl. rewrite H16...
      SSCase "exists t' : x ==> t'".
        right. inversion H. destruct li; simpl in *; try solve by inversion.
        exists (TLiteral (i :: li) (x0 :: l)).
        apply ST_Literal with (lv := nil) (li := nil) (v := x) (v' := x0)...
  Case "T_Access".
    destruct IHHt...
    SCase "TLiteral is a value". right. inversion Ht; subst. apply in_lookup in H...
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
Proof.
  intros x t T gamma H H0. generalize dependent gamma.
  generalize dependent T.
  afi_cases (induction H) Case; intros; try solve [inversion H0; eauto].
    Case "AFI_Lambda". inversion H1. subst. apply IHappears_free_in in H7.
      apply not_eq_beq_id_false in H. rewrite extend_neq in H7; assumption.
    Case "AFI_Record".
      inversion H0; subst... apply Forall2_app_inv_l in H3. inversion H3.
      inversion H1. inversion H2. inversion H7. inversion H9; subst.
      apply IHappears_free_in with (T := y). assumption.
    Case "AFI_Access".
      inversion H0; subst.
      apply IHappears_free_in in H3. assumption.
Qed.

Lemma context_invariance : forall gamma gamma' t T,
                             has_type gamma t T ->
                             (forall x, appears_free_in x t -> gamma x = gamma' x) ->
                             has_type gamma' t T.
Proof with eauto.
  intros.
  generalize dependent gamma'.
  has_type_cases (induction H) Case; intros; try solve [auto].
  Case "T_Var". apply T_Var. rewrite <- H0...
  Case "T_Lambda". apply T_Lambda. apply IHhas_type. intros x0 Hafi.
    unfold extend. remember (beq_id x x0). destruct b...
  Case "T_App".
    eapply T_App...
  Case "T_Literal".
    eapply T_Literal... generalize dependent li. induction H2; intros...
    SCase "Inductive". destruct li; try solve by inversion.
      constructor... apply H. intros. apply H5.
      apply AFI_Record with (leftI := nil) (leftT := nil)...
      inversion H3; subst. eapply IHForall2... intros.
      inversion H4. apply H10. intros. apply H5.
      inversion H6.
      apply AFI_Record with (leftI := i :: leftI)
                              (leftT := x :: leftT)
                              (rightI := rightI)
                              (rightT := rightT)...
  Case "T_Access". eapply T_Access...
Qed.

Lemma combine_map {A} {B} {C} : forall (f : B -> C) (l1 : list A) (l2 : list B),
                                  combine l1 (map f l2) = map (fun p =>
                                                                 (fst p, f (snd p)))
                                                              (combine l1 l2).
Proof with auto.
  intros f l1. induction l1; intros; simpl...
  Case "Inductive". destruct l2... simpl. rewrite IHl1...
Qed.

Lemma substitution_preserves_typing : forall gamma x U t t' T,
                                        has_type (extend gamma x U) t T ->
                                        has_type empty t' U ->
                                        has_type gamma ([x:=t']t) T.
Proof with eauto.
  intros gamma x U t t' T Ht Ht'.
  generalize dependent gamma. generalize dependent T.
  term_cases (induction t) Case; intros T gamma H'; inversion H'; subst; simpl...
  Case "TVar". rename i into y. remember (beq_id x y) as e. destruct e.
    SCase "x=y". apply beq_id_eq in Heqe. subst. rewrite extend_eq in H1.
      inversion H1. subst. eapply context_invariance... intros x Hcontra.
      destruct (free_in_context _ _ T empty Hcontra)... inversion H.
    SCase "x<>y". constructor. rewrite extend_neq in H1...
  Case "TLambda". rename i into y. apply T_Lambda.
    remember (beq_id x y) as e. destruct e.
    SCase "x=y". eapply context_invariance... apply beq_id_eq in Heqe. subst.
      intros x Hafi. unfold extend. remember (beq_id y x) as e. destruct e...
    SCase "x<>y".
      apply IHt. eapply context_invariance... intros z Hafi. unfold extend.
      remember (beq_id y z) as e0. destruct e0...
      apply beq_id_eq in Heqe0. subst.
      rewrite <- Heqe...
  Case "TLiteral". constructor... generalize dependent li. generalize dependent lt.
    induction H; intros.
    SCase "base". inversion H2. constructor.
    SCase "inductive". destruct lt; try solve by inversion. constructor.
      inversion H2. apply H...
      inversion H2. destruct li; try solve by inversion. inversion H3.
      apply IHForall with (li := li)...
      rewrite map_length...
  Case "TAccess".
    eapply T_Access with (v := subst x t' v)... inversion H1. subst.
    rewrite combine_map. apply in_map_iff. exists (i,v)...
Qed.

Lemma combine_3 {A B C} : forall (x : A) (y : B) (z : C) xs ys zs,
                    In (x,y) (combine xs ys) ->
                    In (x,z) (combine xs zs) ->
                    Uniq xs ->
                    In (y,z) (combine ys zs).
Proof with auto.
  induction xs.
  Case "base". simpl in *. intros. inversion H.
  Case "inductive". intros. destruct ys; try solve by inversion.
    destruct zs; try solve by inversion. simpl in *.
    inversion H; inversion H0; try solve by inversion.
    inversion H2; inversion H3; subst.
    left...
    inversion H2; subst. inversion H1. subst.
    contradict H6. apply (in_combine_l xs zs x z)...
    inversion H3; subst. inversion H1. subst.
    contradict H6. apply (in_combine_l xs ys x y)...
    right. inversion H1. apply IHxs...
Qed.

Lemma Forall2_combine_in {A B} : forall P (x : A) (y : B) xs ys,
                                   In (x,y) (combine xs ys) ->
                                   Forall2 P xs ys ->
                                   P x y.
Proof with auto.
  intros. induction H0; try solve by inversion.
  Case "Inductive". simpl in H.  inversion H...
  inversion H2; subst...
Qed.

Lemma combine_app {A B} : forall l1 l2 l3 l4 (x : A) (y : B),
                      length l1 = length l2 ->
                      (combine l1 l2) ++ (@combine A B l3 l4) = combine (l1 ++ l3) (l2 ++ l4).
Proof with auto.
  intros. inversion H.
  generalize dependent l2.
  induction l1; intros; destruct l2; try solve by inversion...
  Case "Inductive". simpl. rewrite IHl1...
Qed.  

Theorem preservation : forall t t' T,
                         has_type empty t T ->
                         t ==> t' ->
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
  Case "T_Literal". inversion HE; subst. constructor...
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
  Case "T_Access". inversion HE; subst... inversion HT; subst.
    SCase "literal is value".
      apply lookup_in_pair in H6... 
      apply Forall2_combine_in with (xs := lv) (ys := lt)...
      apply combine_3 with (xs := li) (x := i)...
    SCase "literal steps". inversion H4; subst. apply IHHT in H4...
      inversion H4. subst.
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

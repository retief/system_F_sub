Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Lt.
Require Import Coq.MSets.MSetList.
Require Import Coq.FSets.FMapList.
Require Import Coq.Strings.String.
Require Import Coq.Logic.Decidable.
Require Import Omega.
Require Import "../SfLib".
Set Implicit Arguments.
Require Export Setoid SetoidClass.
Require Import SetoidDec.


Module UOT_to_OrderedTypeLegacy (UOT:OrderedType) <: (IsEqOrig UOT) <: OrderedType.OrderedType.
  Definition t := UOT.t.
  Definition lt := UOT.lt.
  Definition eq := UOT.eq.
  Definition eq_refl := let (r, _, _) := UOT.eq_equiv in r.
  Definition eq_sym := let (_, s, _) := UOT.eq_equiv in s.
  Definition eq_trans := let (_, _, t) := UOT.eq_equiv in t.
  Lemma lt_trans : forall x y z : t, UOT.lt x y -> UOT.lt y z -> UOT.lt x z.
  Proof. destruct UOT.lt_strorder as [i t]. apply t. Qed.
  Lemma lt_not_eq : forall x y : t, UOT.lt x y -> ~ UOT.eq x y.
  Proof. destruct UOT.lt_strorder as [i t]. intros. intro. rewrite H0 in *. exact (i y H). Qed.
  Definition compare (x y : t) : OrderedType.Compare UOT.lt UOT.eq x y :=
    match (CompareSpec2Type (UOT.compare_spec x y)) with
      | CompLtT l => OrderedType.LT l
      | CompEqT e => OrderedType.EQ e
      | CompGtT g => OrderedType.GT g
    end.
  Definition eq_dec := UOT.eq_dec.
  Definition eq_equiv := UOT.eq_equiv.
  Definition lt_strorder := UOT.lt_strorder.
  Definition lt_compat := UOT.lt_compat.
End UOT_to_OrderedTypeLegacy.

Module Type ATOM.

  Parameter atom : Set.
  Declare Module Atom : Orders.UsualOrderedType with Definition t := atom.
  Module Atom_as_OT : OrderedType.OrderedType
    with Definition t := atom
    with Definition eq := Atom.eq
      := UOT_to_OrderedTypeLegacy(Atom).
  Parameter atom_fresh_for_list : forall (xs : list atom),
    exists x : atom, ~ List.In x xs.
  Definition atom_eq_dec := Atom.eq_dec.
  Lemma atom_dec_eq : forall (a1 a2 : atom), Atom.eq a1 a2 \/ ~ Atom.eq a1 a2.
  Proof. intros. assert (H := atom_eq_dec a1 a2). unfold Atom.eq. destruct H; subst; auto. Qed.

End ATOM.

Module Type STRING.

  Parameter string : Set.
  Declare Module String : Orders.UsualOrderedType with Definition t := string.
  Module String_as_OT : OrderedType.OrderedType with Definition t := string := UOT_to_OrderedTypeLegacy(String).
  Definition string_eq_dec := String.eq_dec.
  Lemma string_dec_eq : forall (s1 s2 : string), s1 = s2 \/ s1 <> s2.
  Proof. intros. assert (H := string_eq_dec s1 s2). destruct H; subst; auto. Qed.

End STRING.

Module LC (Import Atom : ATOM) (Import String : STRING).

Module Atoms := Coq.MSets.MSetList.Make (Atom.Atom).
Module AtomEnv := Coq.FSets.FMapList.Make (Atom.Atom_as_OT).


Lemma eq_atom_refl : forall (a : atom), Atom.eq a a.
Proof. reflexivity. Qed.
Lemma eq_atom_sym : forall (a1 a2 : atom), Atom.eq a1 a2 -> Atom.eq a2 a1.
Proof. intros. symmetry. assumption. Qed.
Lemma eq_atom_trans : forall (a1 a2 a3 : atom), Atom.eq a1 a2 -> Atom.eq a2 a3 -> Atom.eq a1 a3.
Proof. intros. transitivity a2; assumption. Qed.

Add Relation Atom.atom Atom.eq
  reflexivity proved by eq_atom_refl
  symmetry proved by eq_atom_sym
  transitivity proved by eq_atom_trans
as Eq_atom.

Definition atom := Atom.atom. (* free variables *)
Definition loc := Atom.atom.
Definition string := String.string.

(* Example use: "There exists a distinguished string that we'll call __proto__" *)
Parameter __proto__ : string.
(* Example use: "There exist at least two distinct atoms x and y" *)
Parameter x : atom.
Parameter y : atom.
Axiom distinct_x_y : ~ Atom.eq x y.
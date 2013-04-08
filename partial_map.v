Require Import SfLib.

Module PartialMap.

Definition partial_map (A : Type) := id -> option A.

Definition empty {A : Type} : partial_map A := (fun _ => None).

Definition extend {A : Type} (G : partial_map A) (x : id) (T : A) :=
  fun x' => if beq_id x x' then Some T else G x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Admitted.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  beq_id x2 x1 = false ->
  (extend ctxt x2 T) x1 = ctxt x1.
Admitted.

End PartialMap.
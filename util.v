Require Import SfLib.

Inductive Uniq {t : Type} : list t -> Prop :=
| Uniq_nil : Uniq []
| Uniq_cons : forall x xs, not (In x xs) -> Uniq xs -> Uniq (x :: xs).

Hint Constructors Uniq.

Lemma uniq_app {T} : forall (l1 l2 : list T), Uniq (l1 ++ l2) -> Uniq l1 /\ Uniq l2.
Proof with auto.
  induction l1; intros... inversion H; subst. apply IHl1 in H3. inversion H3. split...
    constructor... intro. contradict H2. apply in_or_app. left...
Qed.



Definition partial_map (A : Type) := id -> option A.

Definition empty {A : Type} : partial_map A := (fun _ => None).

Definition extend {A : Type} (G : partial_map A) (x : id) (T : A) :=
  fun x' => if beq_id x x' then Some T else G x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros; unfold extend.
  rewrite <- beq_id_refl.
  reflexivity.
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  beq_id x2 x1 = false ->
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros.
  unfold extend. rewrite -> H.
  reflexivity.
Qed.

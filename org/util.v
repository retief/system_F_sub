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


Lemma length_0_nil : forall {A : Type} (la : list A),
  length la = 0 <-> la = [].
Proof with auto.
  split; intros; subst...
  Case "->".
    induction la... inversion H.
Qed.

Lemma combine_map {A} {B} {C} : forall (f : B -> C) (l1 : list A) (l2 : list B),
                                  combine l1 (map f l2) = map (fun p =>
                                                                 (fst p, f (snd p)))
                                                              (combine l1 l2).
Proof with auto.
  intros f l1. induction l1; intros; simpl...
  Case "Inductive". destruct l2... simpl. rewrite IHl1...
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

Lemma weird_forall_forall2 {A B C : Type} :
  forall (P : A -> B -> C -> Prop)
         (f : A -> A) (f1 : B -> B)
         (l : list B) (l' : list C)
         (g : A),
    Forall (fun (t : B) =>
              forall (T : C) (g : A),
                P (f g) t T -> P g (f1 t) T) l ->
    Forall2 (P (f g)) l l' ->
    Forall2 (P g) (map f1 l) l'.
Proof with auto.
  intros.
  induction H0; simpl in *...
  inversion H. subst.
  apply Forall2_cons...
Qed.
  
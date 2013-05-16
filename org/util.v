Require Import SfLib.
Require Import List.
Require Import Permutation.



Lemma length_0_nil : forall {A : Type} (la : list A),
  length la = 0 <-> la = [].
Proof with auto.
  split; intros; subst...
  Case "->".
    induction la... inversion H.
Qed.

Lemma append_length : forall {A : Type} (l1 l1' l2 l2' : list A),
  length l1 = length l1' -> length l2 = length l2' -> l1 ++ l2 = l1' ++ l2' -> 
  l1 = l1' /\ l2 = l2'.
Proof with auto.
  intros.
  generalize dependent l1'.
  induction l1; intros; destruct l1'; try solve by inversion...
  inversion H1; subst.
  apply IHl1 in H4...
  inversion H4; subst...
Qed.

Lemma Forall_app : forall {A : Type} (P : A -> Prop) (l1 l2 : list A),
  Forall P (l1 ++ l2) -> Forall P l1 /\ Forall P l2.
Proof with auto.
  intros.
  induction l1...
  simpl in H.
  inversion H; subst. remember H3; clear Heqf.
  apply IHl1 in H3.
  split; [apply Forall_cons | apply IHl1]...
  apply H3.
Qed.


(* uniqueness property on lists - used for record types *)
Inductive Uniq {t : Type} : list t -> Prop :=
| Uniq_nil : Uniq []
| Uniq_cons : forall x xs, not (In x xs) -> Uniq xs -> Uniq (x :: xs).

Hint Constructors Uniq.

Lemma uniq_app {T} : forall (l1 l2 : list T), Uniq (l1 ++ l2) -> Uniq l1 /\ Uniq l2.
Proof with auto.
  induction l1; intros... inversion H; subst. apply IHl1 in H3. inversion H3. split...
    constructor... intro. contradict H2. apply in_or_app. left...
Qed.

Lemma in_combine_uniq {A B} :
  forall (la : list A) (lb : list B) a b b',
    In (a,b) (combine la lb) ->
    In (a,b') (combine la lb) ->
    Uniq la -> length la = length lb ->
    b = b'.
Proof with auto.
  intros. generalize dependent lb.
  induction la; intros; destruct lb; try solve by inversion.
  Case "cons".
    simpl in *. inversion H.
    SCase "a0=a".
      inversion H3. subst. inversion H0. inversion H4...
      apply in_combine_l in H4. inversion H1. contradiction.
    SCase "In (a,b) (combine la lb)".
      apply IHla with (lb := lb)...
      inversion H1...
      inversion H0... inversion H4. subst. apply in_combine_l in H3.
      inversion H1. contradiction.
Qed.

(* different form of uniqueness; this different definition means
   list elements are unique according to some function if no two list
   elements produce the same output by that function *)
Inductive Uniq_f {A B : Type} : (A -> B) -> list A -> Prop :=
| Uniq_f_nil : forall (f : A -> B), Uniq_f f []
| Uniq_f_cons : forall (f : A -> B) (x : A) (xs : list A),
                  not (In (f x) (map f xs)) -> Uniq_f f xs -> Uniq_f f (x :: xs).
Hint Constructors Uniq_f.

Lemma uniq_f_app {A B : Type} :
  forall (f : A -> B) (l1 l2 : list A), Uniq_f f (l1 ++ l2) -> Uniq_f f l1 /\ Uniq_f f l2.
Proof with auto.
  induction l1; intros... inversion H; subst. apply IHl1 in H4. inversion H4. split...
    constructor...
  intro. contradict H3.
  rewrite -> map_app.
  apply in_or_app. left...
Qed.

Lemma uniq_f_iff_uniq_map {A B : Type} :
  forall (f : A -> B) (l : list A), Uniq_f f l <-> Uniq (map f l).
Proof with auto.
  split; intros.
  Case "->".
    induction l.
    SCase "[]".
      simpl...
    SCase "a :: l".
      simpl. inversion H; subst...
  Case "<-".
    induction l...
    SCase "a :: l".
      inversion H; subst...
Qed.


(* various [combine] lemmas - these are used for proofs about record types *)
Lemma combine_eq {A B : Type} : forall (a c : list A) (b d : list B),
                     combine a b = combine c d ->
                     length a = length b ->
                     length c = length d ->
                     a = c /\ b = d.
Proof with auto.
  intros. generalize dependent b. generalize dependent c. generalize dependent d.
  induction a; intros.
    Case "nil". destruct b; destruct c; destruct d; try solve by inversion...
    Case "cons". destruct b; destruct c; destruct d; try solve by inversion.
      simpl in *. inversion H0. inversion H. inversion H1.
      apply IHa with (b := b0) in H7... inversion H7... rewrite H2. rewrite H8...
Qed.

Lemma permutation_in {A} :
  forall x (l l' : list A),
    Permutation l l' ->
    In x l' ->
    In x l.
Proof with auto.
  intros.
  induction H...
  Case "skip". unfold In.
    unfold In in H0. inversion H0...
    apply IHPermutation in H1...
  Case "swap". unfold In in H0.
    unfold In.
    inversion H0...
    inversion H...
Qed.
  
Lemma uniq_permutation {A : Type} :
  forall (l l' : list A),
    Permutation l l' ->
    Uniq l ->
    Uniq l'.
Proof with auto.
  intros.
  induction H...
  Case "skip".
    inversion H0. apply IHPermutation in H4.
    constructor... intro.
    apply (permutation_in x l l') in H5...
  Case "swap".
    inversion H0. inversion H3. constructor...
    intro. contradict H2. unfold In in H8. inversion H8.
    rewrite H2. simpl...
    apply H6 in H2. inversion H2.
    constructor... intro. contradict H2.
    unfold In...
Qed.

Lemma uniq_f_permutation {A B : Type} :
  forall (f : A -> B) (l l' : list A),
    Permutation (map f l) (map f l') -> Uniq_f f l -> Uniq_f f l'.
Proof with auto.
  intros.
  apply uniq_f_iff_uniq_map in H0. apply uniq_f_iff_uniq_map.
  apply uniq_permutation with (map f l)...
Qed.
    
    

Lemma combine_pairs {A B : Type} :
  forall (ab : list (A*B)),
  exists a b, combine a b = ab /\ length a = length b.
Proof with auto.
  intros.
  induction ab.
  Case "nil". exists []. exists []. simpl...
  Case "cons".  inversion IHab. inversion H. inversion H0.  destruct a.
    exists (a :: x). exists (b :: x0). simpl. rewrite <- H1...
Qed.

Lemma permutation_combine {A B : Type} : forall (a c : list A) (b d : list B),
                              length a = length b ->
                              length c = length d ->
                              Permutation (combine a b) (combine c d) ->
                              Permutation a c /\ Permutation b d.
Proof with eauto.
  intros. remember (combine a b). remember (combine c d).
  generalize dependent a. generalize dependent b.
  generalize dependent c. generalize dependent d.
  induction H1; intros.
  Case "nil". unfold combine in *.
    destruct a; destruct b; destruct c; destruct d; try solve by inversion...
  Case "skip".
    destruct a; destruct b; destruct c; destruct d; try solve by inversion...
    simpl in *.
    inversion Heql0. inversion Heql. subst. 
    inversion H5. subst.
    inversion H0. apply IHPermutation with (d0 := d) (c0 := c) (b := b0) (a := a0) in H3...
    inversion H3... (* immediate from [permutation_cons] *)
  Case "swap".
    destruct a; destruct b; destruct c; destruct d; try solve by inversion.
    destruct a0; destruct b0; destruct c; destruct d; try solve by inversion.
    simpl in *.
    inversion Heql. inversion Heql0. subst.
    inversion H6. inversion H5. subst.
    inversion H0. inversion H. apply combine_eq in H7...
    inversion H7. rewrite H1.
    rewrite H4. split; constructor.
  Case "trans".
    subst.
    assert (exists a b, combine a b = l' /\ length a = length b).
      apply combine_pairs.
    inversion H1. inversion H2. inversion H3. clear H1 H2 H3. subst.
    remember H5. clear Heqe.
    apply IHPermutation1 with (d := x0) (c := x) (b0 := b) (a0 := a) in H5...
    apply IHPermutation2 with (d0 := d) (c0 := c) (a := x) (b := x0) in H0...
    inversion H0. inversion H5.
    split; eapply perm_trans...
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
  Case "base []".
    simpl in *. intros. inversion H.
  Case "inductive".
    intros.
    destruct ys; try solve by inversion.
    destruct zs; try solve by inversion.
    simpl in *.
    inversion H; inversion H0; try solve by inversion.
    inversion H2; inversion H3; subst.
    left...
    inversion H2; subst. inversion H1. subst.
    contradict H6. apply (in_combine_l xs zs x z)...
    inversion H3; subst. inversion H1; subst.
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
  
Section Groups.

Require Omega.

Class Group : Type :=
{
  G : Type;
  dot : G -> G -> G;
  e : G;
  inv : G -> G;
  dot_assoc :
    forall x y z, dot (dot x y) z = dot x (dot y z);
  id_left :
    forall x, dot e x = x;
  id_right :
    forall x, dot x e = x;
  inv_left :
    forall x, dot (inv x) x = e;
  inv_right :
    forall x, dot x (inv x) = e
}.

Infix "⊙" := dot (at level 60).
Notation "- a" := (inv a).

Context `{Grp : Group}.

Theorem identity_uniqueness :
  forall u, (forall x, u ⊙ x = x) -> u = e.
    intros u H.
    rewrite <- (id_right u).
    apply H.
Qed.

Theorem inverse_uniqueness :
  forall x u, u ⊙ x = e -> u = -x.
    intros x u.
    (*split*)

    intro H.
    rewrite <- (id_right u), <- (inv_right x), <- dot_assoc, H.
    apply id_left.

    (*
    intro H.
    rewrite H.
    apply inv_left. *)
Qed.

Fact inverse_uniqueness_symmetry :
  forall x u, u ⊙ x = e <-> x ⊙ u = e.
    intros x u.
    split.

    intro H.
    rewrite (inverse_uniqueness x u).
    apply inv_right.
    assumption.

    intro H.
    rewrite (inverse_uniqueness u x).
    apply inv_right.
    assumption.
Qed.

Lemma id_self_inverse :
  e = -e.
    apply (inverse_uniqueness e e).
    apply id_left.
Qed.

Lemma double_inverse :
  forall g, g = --g.
    intro g.
    apply (inverse_uniqueness (-g) g).
    apply inv_right.
Qed.

Lemma equality :
  forall x y, x = y -> x ⊙ -y = e.
    intros x y H.
    rewrite <- H.
    apply inv_right.
Qed.

Lemma inverse_equality :
  forall x y, x = -y -> x ⊙ y = e.
    intros x y H.
    rewrite H.
    apply inv_left.
Qed.

Theorem inverse_of_dot :
  forall a b, -(a ⊙ b) = -b ⊙ -a.
    intros.
    symmetry.
    apply (inverse_uniqueness (a ⊙ b) (-b ⊙ -a)).
    rewrite dot_assoc, <- (dot_assoc (inv a) a b),
            (inv_left a), (id_left b), (inv_left b).
    trivial.
Qed.

Definition choice := nat -> G.

Fixpoint finite_dot (w : choice) (k : nat) :=
  match k with
  | O => e
  | S m => (finite_dot w m) ⊙ (w m)
  end.

Fixpoint finite_inv_dot (w : choice) (k : nat) :=
  match k with
  | O => e
  | S m => -(w m) ⊙ (finite_inv_dot w m)
  end.

Theorem inverse_of_finite_dot :
  forall w n, inv (finite_dot w n) = finite_inv_dot w n.
    intros w n.
    elim n.

    simpl.
    symmetry.
    apply id_self_inverse.

    intros n0 H.
    simpl.
    symmetry.
    apply inverse_uniqueness.
    symmetry in H.
    apply inverse_equality in H.
    rewrite dot_assoc.
    rewrite <- (dot_assoc (finite_inv_dot w n0)
                          (finite_dot w n0)
                          (w n0)).
    rewrite H.
    rewrite id_left.
    apply inv_left.
Qed.

Theorem eq_left_solution :
  forall a b x, x ⊙ a = b -> x = b ⊙ -a.
    intros a b x H.
    apply equality in H.
    rewrite dot_assoc in H.
    apply inverse_uniqueness in H.
    rewrite (inverse_of_dot a (inv b)) in H.
    rewrite <- (double_inverse b) in H.
    assumption.
Qed.

Definition has_order t :=
  exists f : G -> nat,
    forall g h : G,
      (f g < t /\ f h < t) ->
      (forall k : nat, k < t -> exists x : G, f x = k) /\
      (f g = f h -> g = h).

Definition finite :=
  exists t, has_order t.

Definition singular :=
  has_order 1.
  
Theorem singularity :
  (forall x : G, x = e) -> singular.
    unfold singular, has_order.
    intro all_id.
    exists (fun (x : G) => 0).
    intros.
    repeat split.
    repeat auto.
    omega.
    intro.
    rewrite (all_id g), (all_id h).
    reflexivity.
Qed.

End Groups.
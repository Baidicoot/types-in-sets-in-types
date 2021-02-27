Create HintDb zf.

Module Type CZF.
  Notation "A ∧ B" := (prod A B) (at level 80).
  Notation "A ↔ B" := ((A -> B) ∧ (B -> A)) (at level 95).
  
  Parameter set : Type.

  Parameter equiv : set -> set -> Type.
  Notation "A ≡ B" := (equiv A B) (at level 70).
  Parameter equiv_refl : forall {x}, x ≡ x.
  Parameter equiv_sym : forall {x y}, x ≡ y -> y ≡ x.
  Parameter equiv_trans :
    forall {x y}, x ≡ y -> forall {z}, y ≡ z -> x ≡ z.
  Hint Resolve equiv_refl : zf.
  Hint Resolve equiv_sym : zf.
  Hint Resolve equiv_trans : zf.
  Axiom equiv_irrel : forall {x y} (p q: x ≡ y), p = q.
  Axiom equiv_real : forall {x y}, x ≡ y -> x = y.
  Hint Resolve equiv_irrel : zf.
  Hint Resolve equiv_real : zf.

  Parameter member : set -> set -> Type.
  Notation "A ∈ B" := (member A B) (at level 70).
  Parameter member_sound :
    forall {x y}, x ∈ y ->
    forall {z w}, x ≡ z -> y ≡ w -> z ∈ w.
  Parameter equiv_ext :
    forall {x y}, (forall {z}, z ∈ x ↔ z ∈ y) -> x ≡ y.
  Parameter equiv_def :
  forall {x y}, x ≡ y -> (forall {z}, z ∈ x ↔ z ∈ y).
  Notation "A ∉ B" := (A ∈ B -> False) (at level 70).
  Hint Resolve member_sound : zf.
  Hint Resolve equiv_ext : zf.
  Hint Resolve equiv_def : zf.
  Axiom member_irrel : forall {x y} (p q: x ∈ y), p = q.
  Hint Resolve member_irrel : zf.

  Definition subset A B := forall x, x ∈ A -> x ∈ B.
  Notation "A ⊆ B" := (subset A B) (at level 70).
  Lemma subset_sound :
    forall {x y}, x ⊆ y ->
    forall {z w}, x ≡ z -> y ≡ w -> z ⊆ w.
  Proof.
    unfold subset.
    eauto with zf.
  Qed.
  Axiom subset_irrel : forall {x y} (p p0: x ⊆ y), p = p0.
  Hint Resolve subset_sound : zf.
  Hint Resolve subset_irrel : zf.
  
  Parameter empty : set.
  Notation "∅" := empty.
  Parameter empty_prop : forall {x}, x ∉ ∅.
  Hint Resolve empty_prop : zf.

  Parameter insert : set -> set -> set.
  Notation "x +> y" := (insert x y) (at level 60).
  Parameter insert_sound :
    forall {x y z w}, x ≡ z -> y ≡ w -> x +> y ≡ z +> w.
  Parameter insert_prop :
    forall {x y}, x ∈ x +> y ∧ y ⊆ x +> y.
  Hint Resolve insert_sound : zf.
  Hint Resolve insert_prop : zf.

  Parameter union : set -> set.
  Notation "⋃ X" := (union X) (at level 60).
  Parameter union_sound :
    forall {x y}, x ≡ y -> ⋃x ≡ ⋃y.
  Parameter union_prop :
    forall {x y}, y ∈ x -> forall {z}, z ∈ y -> z ∈ ⋃x.
  Parameter union_def :
    forall {x z}, z ∈ ⋃x -> {y & z ∈ y ∧ y ∈ x}.
  Hint Resolve union_sound : zf.
  Hint Resolve union_prop : zf.

  Definition ordered_pair x y :=
    insert (insert x ∅) (insert (insert x (insert y ∅)) ∅).
  Notation "⟨ x , y ⟩" := (ordered_pair x y).
  Lemma pair_sound :
    forall {x y z w}, x ≡ z -> y ≡ w ->
                 ⟨x,y⟩ ≡ ⟨z,w⟩.
  Proof.
    unfold ordered_pair. intros.
    assert (x +> ∅ ≡ z +> ∅) by auto with zf.
    eauto with zf.
  Qed.
  Hint Resolve pair_sound : zf.

  Definition Suc x := x +> x.
  
  Parameter infinity : set.
  Notation "∞" := infinity (at level 60).
  Parameter infinity_prop :
    forall {x}, x ∈ ∞ -> Suc x ∈ ∞.
  Hint Resolve infinity_prop : zf.

  Definition left_total (P: set -> set -> Type) D := forall x, x ∈ D -> {y & P x y}.
  Definition functional (P: set -> set -> Type) := forall x y, P x y -> forall z, P x z -> y ≡ z.
  Definition relation_sound (P: set -> set -> Type) := forall x y, P x y -> forall z w, x ≡ z -> y ≡ w -> P z w.

  Definition formula P D := functional P ∧ relation_sound P ∧ left_total P D.

  Lemma left_total_sound : forall {P D}, left_total P D -> forall {E}, D ≡ E -> left_total P E.
  Proof.
    unfold left_total.
    eauto with zf.
  Defined.
  Hint Resolve left_total_sound : zf.

  Lemma formula_sound : forall {P D}, formula P D -> forall {E}, D ≡ E -> formula P E.
  Proof.
    unfold formula.
    intros. destruct X.
    split. auto.
    eauto with zf.
  Defined.
  Hint Resolve formula_sound : zf.

  Definition fun_sound : forall {I} (P: forall x, x ∈ I -> set) {J},
      I ≡ J -> forall x, x ∈ J -> set.
  Proof.
    intros.
    assert (x ∈ I) by eauto with zf.
    exact (P x X1).
  Defined.
  Hint Resolve fun_sound : zf.
  
  Parameter replacement : forall {I}, (forall x, x ∈ I -> set) -> set.
  Parameter collection : forall {P I}, formula P I -> set.
  Parameter replacement_sound : forall {I P J} (H: I ≡ J),
      replacement P ≡ replacement (fun_sound P H).
  Parameter collection_sound : forall {P I} (H: formula P I), forall {J} (H0: I ≡ J),
        collection H ≡ collection (formula_sound H H0).
  Parameter replacement_prop : forall {I P x}, x ∈ replacement P ↔ {i & {p: i ∈ I & P i p ≡ x}}.
  Parameter collection_prop : forall {P I} {H: formula P I} {x}, x ∈ collection H ↔ {i & i ∈ I ∧ P i x}.
  Hint Resolve replacement_sound : zf.
  Hint Resolve collection_sound : zf.
  Hint Resolve replacement_prop : zf.
  Hint Resolve collection_prop : zf.

  Definition prop_sound (P: set -> Type) := forall x y, x ≡ y -> P x = P y.
  
  Parameter induction :
    forall {P}, prop_sound P ->
           (forall x, (forall y, y ∈ x -> P y) -> P x) ->
           forall x, P x.
  Axiom induction_prop :
    forall {P} {H: prop_sound P} {H0 x}, induction H H0 x = H0 x (fun y _ => induction H H0 y).
End CZF.

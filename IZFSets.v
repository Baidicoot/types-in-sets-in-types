Require Import IZF.

Module IZFSetsF (ST: IZF).
  Import ST.

  Notation "A ∧ B" := (prod A B) (at level 80).

  Lemma replacement_prf :
    forall {D} (f: forall x, x ∈ D -> set),
      {P: @formula D & (forall x y (p: x ∈ D), proj1_sig P x y <-> y ≡ f x p) ∧ forall x y, proj1_sig P x y -> x ∈ D}.
  Proof.
    intros.
    simple refine (existT _ _ _).
    unfold formula.
    exists (fun x y => exists p, y ≡ f x p).
    intros.
    exists (f x H). exists H. auto with zf.
    split; simpl; intros.
    split; intros.
    destruct H.
    rewrite (M p x0).
    auto.
    exists p. auto.
    destruct H.
    auto.
  Qed.
  
  Definition replacement : forall {D}, (forall x, x ∈ D -> set) -> set.
  Proof.
    intros.
    destruct (replacement_prf X).
    destruct p.
    simple refine (collection _).
    exact D.
    exact x.
  Defined.

  Lemma replacement_propH : forall {D f x}, x ∈ replacement f -> exists d (H: d ∈ D), f d H ≡ x.
  Proof.
    unfold replacement.
    intros.
    destruct (replacement_prf f).
    destruct p.
    simpl in *; intros.
    apply collection_propH in H.
    destruct H.
    destruct H.
    exists x1. exists H.
    destruct (i x1 x H).
    apply H1 in H0.
    eauto with zf.
  Qed.

  Lemma replacement_propG : forall {D f x}, (exists d (H: d ∈ D), f d H ≡ x) -> x ∈ replacement f.
  Proof.
    intros.
    destruct H.
    destruct H.
    subst x.
    unfold replacement.
    destruct (replacement_prf f).
    destruct p.
    apply collection_propG.
    exists x0. split. auto.
    destruct (i x0 (f x0 x1) x1).
    assert (f x0 x1 ≡ f x0 x1) by auto.
    apply H0 in H1.
    auto.
  Qed.
                                                                       
  Definition cartesian_product (A B: set) :=
    union (replacement (fun x (_: x ∈ A) => replacement (fun y (_: y ∈ B) => ⟨x,y⟩))).    
  Notation "A × B" := (cartesian_product A B) (at level 60).
  
  Lemma cartesian_product_propG : forall {A B z}, (exists x y, x ∈ A /\ y ∈ B /\ z ≡ ⟨x,y⟩) -> z ∈ A × B.
  Proof.
    intros. unfold cartesian_product.
    repeat destruct H.
    destruct H0.
    subst z.
    apply union_propG.
    exists (replacement (fun y (_: y ∈ B) => ⟨x,y⟩)).
    split. apply replacement_propG.
    exists x. exists H.
    auto.
    apply replacement_propG.
    exists x0. exists H0. auto.
  Qed.

  Lemma cartesian_product_propH : forall {A B z}, z ∈ A × B -> exists x y, x ∈ A /\ y ∈ B /\ z ≡ ⟨x,y⟩.
  Proof.
    intros.
    unfold cartesian_product in H.
    apply union_propH in H.
    destruct H. destruct H.
    apply replacement_propH in H.
    destruct H. destruct H.
    subst x.
    apply replacement_propH in H0.
    destruct H0. destruct H.
    subst z.
    exists x0. exists x. auto.
  Qed.

  Definition disjoint_union {I} (F: forall x, x ∈ I -> set) :=
    union (replacement (fun x (H: x ∈ I) => replacement (fun y (_: y ∈ F x H) => ⟨x,y⟩))).
  
  Notation "⨆ F" := (disjoint_union F) (at level 60).
  
  Lemma disjoint_union_propG : forall {I F z}, (exists x (H: x ∈ I) y, y ∈ F x H /\ z ≡ ⟨x,y⟩) -> z ∈ ⨆F.
  Proof.
    intros. unfold disjoint_union.
    repeat destruct H.
    subst z.
    apply union_propG.
    exists (replacement (fun y (_: y ∈ F x x0) => ⟨x,y⟩)).
    split. apply replacement_propG.
    exists x. exists x0. auto.
    apply replacement_propG.
    exists x1. exists H. auto.
  Qed.

  Lemma disjoint_union_propH : forall {I F z}, z ∈ ⨆F -> exists x (H: x ∈ I) y, y ∈ F x H /\ z ≡ ⟨x,y⟩.
  Proof.
    intros. unfold disjoint_union in H.
    apply union_propH in H.
    repeat destruct H.
    apply replacement_propH in H.
    repeat destruct H.
    apply replacement_propH in H0.
    destruct H0. destruct H.
    subst z. exists x0. exists x1. exists x.
    auto.
  Qed.

  Lemma cartesian_product_is_extreme_disjoint_union : forall {A B}, A × B ≡ ⨆(fun x (_: x ∈ A) => B).
  Proof.
    reflexivity.
  Qed.

  Definition union2 (A B: set) := ⋃ (A +> (B +> ∅)).
  Notation "x ∪ y" := (union2 x y) (at level 60).
  
  Lemma union2_propG : forall {A B x}, (x ∈ A \/ x ∈ B) -> x ∈ A ∪ B.
  Proof.
    intros.
    unfold union2.
    intros.
    destruct H.
    assert (A ∈ A +> (B +> ∅)) by eauto with zf.
    eauto with zf.
    assert (B ∈ A +> (B +> ∅)) by eauto with zf.
    eauto with zf.
  Qed.

  Lemma union2_propH : forall {A B x}, x ∈ A ∪ B -> x ∈ A \/ x ∈ B.
  Proof.
    unfold union2.
    intros.
    apply union_propH in H.
    destruct H.
    destruct H.
    apply insert_propH in H.
    destruct H.
    apply insert_propH in H.
    destruct H.
    apply empty_prop in H.
    contradiction.
    rewrite H in *.
    eauto with zf.
    rewrite H in *.
    eauto with zf.
  Qed.
  Hint Resolve union2_propH union2_propG : zf.
  
  Definition ϵ_iter Γ := ϵ_rec (fun x f => ⋃ (replacement (fun x H => Γ(f x H)))).
  
  Lemma ϵ_iter_prop : forall {Γ x},
      ϵ_iter Γ x = ⋃ replacement (fun y (_: y ∈ x) => Γ(ϵ_iter Γ y)).
  Proof.
    intros.
    unfold ϵ_iter.
    rewrite ϵ_rec_prop.
    eauto with zf.
  Qed.

  Definition lfp (Γ: set -> set) := ⋃ replacement (fun x (_: x ∈ ω) => ϵ_iter Γ x).

  Lemma replacement_of_empty : forall {f},
      @replacement ∅ f ≡ ∅.
  Proof.
    intros.
    apply equiv_ext.
    split; intros.
    apply replacement_propH in H.
    destruct H. destruct H.
    apply empty_prop in x0 as H1.
    contradiction.
    apply empty_prop in H.
    contradiction.
  Qed.

  Lemma union_empty : ⋃∅ ≡ ∅.
  Proof.
    apply equiv_ext.
    split; intros.
    apply union_propH in H.
    destruct H. destruct H.
    apply empty_prop in H.
    contradiction.
    apply empty_prop in H.
    contradiction.
  Qed.

  Definition monotone Γ := forall x y, x ⊆ y -> Γ x ⊆ Γ y.

  Lemma union_monotone : monotone union.
  Proof.
    unfold monotone.
    unfold subset.
    intros.
    apply union_propG.
    apply union_propH in H0.
    destruct H0. destruct H0.
    apply H in H0.
    exists x1. eauto.
  Qed.

  Definition monotone_dom {x} (Γ: forall y, y ∈ x -> set) :=
    forall z w (p: z ∈ x) (p0: w ∈ x), z ⊆ w -> Γ z p ⊆ Γ w p0.

  Definition restrict_dom {x y} (p: x ⊆ y) (Γ: forall z, z ∈ y -> set)
    : forall z, z ∈ x -> set.
  Proof.
    intros.
    exact (Γ z (p z H)).
  Defined.
  
  Lemma replacement_monotone :
    forall {D E Γ} (p: D ⊆ E), replacement (restrict_dom p Γ) ⊆ replacement Γ.
  Proof.
    unfold subset.
    unfold restrict_dom.
    intros.
    apply replacement_propH in H.
    destruct H. destruct H.
    subst x.
    apply replacement_propG.
    exists x0. exists (p x0 x1). auto.
  Qed.
  
  Lemma ϵ_iter_monotone : forall {Γ}, monotone (ϵ_iter Γ).
  Proof.
    (* by the definition of monotonicities, it suffices to prove: *)
    (* ∀Γ x y, x ⊆ y → ∀x0 x0 ∈ ϵ_iter Γ x → x0 ∈ ϵ_iter Γ y *)
    unfold monotone.
    unfold subset.
    intros.
    rewrite ϵ_iter_prop in H0.
    (* x0 ∈ ϵ_iter Γ x, therefore x0 ∈ ⋃{ Γ(ϵ_iter Γ y) | y ∈ x } *)
    apply union_propH in H0.
    (* therefore ∃x1 ∈ { Γ(ϵ_iter Γ y) | y ∈ x} s.t. x0 ∈ x1 *)
    destruct H0. destruct H0.
    apply replacement_propH in H0.
    (* therefore ∃x2 ∈ x s.t Γ(ϵ_iter Γ x2) ≡ x1 *)
    destruct H0. destruct H0.
    subst x1.
    (* so x0 ∈ Γ(ϵ_iter Γ x2) *)
    rewrite ϵ_iter_prop.
    (* it suffices to prove x0 ∈ ⋃{ Γ(ϵ_iter Γ x) | x ∈ y } *)
    apply union_propG.
    (* so we have to provide a y0 ∈ { Γ(ϵ_iter Γ x) | x ∈ y} s.t. x0 ∈ y0 *)
    exists (Γ (ϵ_iter Γ x2)).
    split.
    apply replacement_propG.
    (* Γ(ϵ_iter Γ x2) ∈ { Γ(ϵ_iter Γ x) | x ∈ y } as x2 ∈ y *)
    exists x2. exists (H x2 x3). auto.
    (* as previously proven, x0 ∈ Γ(ϵ_iter Γ x2) *)
    auto.
  Qed.

  Lemma ϵ_iter_empty : forall {Γ}, ϵ_iter Γ ∅ ≡ ∅.
  Proof.
    intros.
    apply equiv_ext.
    split; intros.
    rewrite ϵ_iter_prop in H.
    rewrite replacement_of_empty in H.
    rewrite union_empty in H.
    auto.
    apply empty_prop in H.
    contradiction.
  Qed.

  Lemma union2_comm : forall {x y}, x ∪ y ≡ y ∪ x.
  Proof.
    intros.
    apply equiv_ext.
    split; intros;
    apply union2_propH in H;
    apply union2_propG;
    destruct H; auto.
  Qed.

  Lemma union2_assoc : forall {x y z}, x ∪ (y ∪ z) ≡ (x ∪ y) ∪ z.
  Proof.
    intros.
    apply equiv_ext.
    split; intros.
    apply union2_propG.
    apply union2_propH in H.
    destruct H.
    left.
    apply union2_propG.
    auto.
    apply union2_propH in H.
    destruct H.
    left.
    apply union2_propG.
    auto.
    auto.
    apply union2_propG.
    apply union2_propH in H.
    destruct H.
    apply union2_propH in H.
    destruct H.
    left.
    auto.
    right.
    apply union2_propG.
    auto.
    right.
    apply union2_propG.
    auto.
  Qed.

  Lemma union2_ident : forall {x}, x ∪ ∅ ≡ x.
  Proof.
    intros.
    apply equiv_ext.
    split; intros.
    apply union2_propH in H.
    destruct H.
    auto.
    apply empty_prop in H.
    contradiction.
    apply union2_propG.
    auto.
  Qed.

  Lemma in_ϵ_iter_sup :
    forall {Γ x y z}, x ∈ ϵ_iter Γ y -> y ⊆ z -> x ∈ ϵ_iter Γ z.
  Proof.
    intros.
    rewrite ϵ_iter_prop in H.
    apply union_propH in H.
    destruct H. destruct H.
    apply replacement_propH in H.
    destruct H. destruct H.
    subst x0.
    rewrite ϵ_iter_prop.
    apply union_propG.
    exists (Γ (ϵ_iter Γ x1)).
    split.
    apply replacement_propG.
    exists x1. exists (H0 _ x2).
    auto.
    auto.
  Qed.

  Lemma union2_insert :
    forall {x y z}, x ∪ (y +> z) ≡ y +> (x ∪ z).
  Proof.
    intros.
    apply equiv_ext.
    split; intros.
    apply union2_propH in H.
    apply insert_propG.
    destruct H.
    left.
    apply union2_propG.
    auto.
    apply insert_propH in H.
    destruct H.
    left.
    apply union2_propG.
    auto.
    auto.
    apply insert_propH in H.
    apply union2_propG.
    destruct H.
    apply union2_propH in H.
    destruct H.
    auto.
    right.
    eauto with zf.
    eauto with zf.
  Qed.

  Lemma empty_subset :
    forall {x}, ∅ ⊆ x.
  Proof.
    unfold subset.
    intros.
    apply empty_prop in H.
    contradiction.
  Qed.

End IZFSetsF.

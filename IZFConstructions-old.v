Require Import IZF.
Require Import Lists.List.

Module IZFConstructions (ST: IZF).
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

  Lemma replacement_prop : forall {D f x}, x ∈ replacement f <-> exists d (H0: d ∈ D), f d H0 ≡ x.
  Proof.
    unfold replacement.
    intros.
    destruct (replacement_prf f).
    destruct p.
    split; simpl in *; intros.
    apply collection_propl in H.
    destruct H.
    destruct H.
    exists x1. exists H.
    destruct (i x1 x H).
    apply H1 in H0.
    eauto with zf.
    apply collection_propr.
    destruct H.
    destruct H.
    exists x1. split.
    exact x2.
    destruct (i x1 x x2).
    eauto with zf.
  Qed.
  
  Definition cartesian_product (A B: set) :=
    union (replacement (fun x (_: x ∈ A) => replacement (fun y (_: y ∈ B) => ⟨x,y⟩))).    
  Notation "A × B" := (cartesian_product A B) (at level 60).
  
  Lemma cartesian_product_prop : forall {A B x y}, x ∈ A -> y ∈ B -> ⟨x,y⟩ ∈ A × B.
  Proof.
    intros. unfold cartesian_product.
    assert (⟨x,y⟩ ∈ replacement (fun (y0 : set) (_ : y0 ∈ B) => ⟨ x, y0 ⟩)).
    apply replacement_prop. exists y. exists H0.
    eauto with zf.
    assert (replacement (fun (y0 : set) (_ : y0 ∈ B) => ⟨ x, y0 ⟩)
                        ∈ replacement (fun (x0 : set) (_ : x0 ∈ A) => replacement (fun (y0 : set) (_ : y0 ∈ B) => ⟨ x0, y0 ⟩))).
    apply replacement_prop. exists x. exists H. eauto with zf.
    eauto with zf.
  Qed.

  Definition disjoint_union {I} (F: forall x, x ∈ I -> set) :=
    union (replacement (fun x (H: x ∈ I) => replacement (fun y (_: y ∈ F x H) => ⟨x,y⟩))).
  
  Notation "⨆ F" := (disjoint_union F) (at level 60).
  
  Lemma disjoint_union_prop : forall {I F x y} (H: x ∈ I), y ∈ F x H -> ⟨x,y⟩ ∈ ⨆F.
  Proof.
    intros. unfold disjoint_union.
    assert (⟨x,y⟩ ∈ replacement (fun y (_: y ∈ F x H) => ⟨x,y⟩)).
    apply replacement_prop.
    exists y. exists H0. eauto with zf.
    assert (replacement (fun y (_: y ∈ F x H) => ⟨x,y⟩) ∈ replacement (fun x (H: x ∈ I) => replacement (fun y (_: y ∈ F x H) => ⟨x,y⟩))).
    apply replacement_prop.
    exists x. exists H. eauto with zf.
    eauto with zf.
  Qed.

  Lemma cartesian_product_is_extreme_disjoint_union : forall {A B}, A × B ≡ ⨆(fun x (_: x ∈ A) => B).
  Proof.
    reflexivity.
  Qed.
  
  Inductive ind_rule : Type :=
  | ind : (set -> ind_rule) -> ind_rule
  | ext : forall {S}, (forall x, x ∈ S -> ind_rule) -> ind_rule
  | ins : set -> ind_rule.

  Reserved Notation "⦅ x ⦆ y" (at level 60).
  Program Fixpoint interp_rule (r: ind_rule) (X: set) : set :=
    match r with
    | ind f => ⋃ (replacement (fun x (_: x ∈ X) => ⦅f x⦆X))
    | ins x => x +> ∅
    | ext f => ⋃ (replacement (fun x H => ⦅f x H⦆X))
    end
  where "⦅ x ⦆ y" := (interp_rule x y).
  
  Definition union2 (A B: set) := ⋃ (A +> (B +> ∅)).
  Notation "x ∪ y" := (union2 x y) (at level 60).
  
  Lemma union2_prop : forall {A B x}, (x ∈ A \/ x ∈ B) <-> x ∈ A ∪ B.
  Proof.
    intros.
    unfold union2.
    split; intros.
    destruct H.
    assert (A ∈ A +> (B +> ∅)) by eauto with zf.
    eauto with zf.
    assert (B ∈ A +> (B +> ∅)) by eauto with zf.
    eauto with zf.
    apply union_propr in H.
    destruct H.
    destruct H.
    apply insert_propl in H.
    destruct H.
    apply insert_propl in H.
    destruct H.
    apply empty_prop in H.
    contradiction.
    rewrite H in *.
    eauto with zf.
    rewrite H in *.
    eauto with zf.
  Qed.
  Hint Resolve union2_prop : zf.
  
  Reserved Notation "⟦ x ⟧ y" (at level 60).
  Fixpoint interp_rules (rs: list ind_rule) (X: set) : set :=
    match rs with
    | nil => ∅
    | r::rs => (⦅r⦆X) ∪ (⟦rs⟧X)
    end
  where "⟦ x ⟧ y" := (interp_rules x y).

  Fixpoint rule_prop (r: ind_rule) (X: set) (S: set) : Prop :=
    match r with
    | ind f => forall x, x ∈ X -> rule_prop (f x) X S
    | ins x => x ∈ S
    | ext f => forall x H, rule_prop (f x H) X S
    end.

  Fixpoint rules_prop_suc (rs: list ind_rule) (X: set) (S: set) : Prop :=
    match rs with
    | nil => True
    | r::rs => rule_prop r X S /\ rules_prop_suc rs X S
    end.

  Definition rules_prop rs X := rules_prop_suc rs X (⟦rs⟧X).

  Notation "'has' x , y" := (ind (fun x => y)) (at level 200, x at level 69).
  Notation "'for' x '∈' y , z" := (ext (fun x (_: x ∈ y) => z)) (at level 200, x at level 69).

  Definition S_rule := has n, ins ⟨∅,n⟩.
  Definition Z_rule := ins ⟨∅ +> ∅, ∅⟩. 
  
  Definition ϵ_iter Γ := ϵ_rec Γ (fun x f => ⋃ (replacement f)).
  
  Lemma ϵ_iter_prop : forall {Γ x},
      ϵ_iter Γ x = ⋃ replacement (fun y (_: y ∈ x) => Γ(ϵ_iter Γ y)).
  Proof.
    intros.
    unfold ϵ_iter.
    rewrite ϵ_rec_prop.
    eauto with zf.
  Qed.

  Definition lfp (Γ: set -> set) := ⋃ replacement (fun x (_: x ∈ ω) => ϵ_iter Γ x).
  
  Definition nat_Γ X := ⟦S_rule :: Z_rule :: nil⟧X.

  Lemma s_in_nat_Γ : forall {n x}, n ∈ x -> ⟨∅,n⟩ ∈ nat_Γ x.
  Proof.
    unfold nat_Γ.
    intros.
    assert (⟨∅,n⟩ ∈ ⟨∅,n⟩ +> ∅) by eauto with zf.
    assert (⟨∅,n⟩ +> ∅ ∈ replacement (fun n (_: n ∈ x) => ⟨ ∅, n ⟩ +> ∅)).
    apply replacement_prop.
    exists n. exists H. eauto with zf.
    assert (⟨ ∅, n ⟩ ∈ (⋃ replacement (fun (n0 : set) (_ : n0 ∈ x) => ⟨ ∅, n0 ⟩ +> ∅))).
    eauto with zf.
    apply union2_prop.
    left.
    auto.
  Qed.

  Definition nat := lfp nat_Γ.

  Lemma x_in_Suc_x : forall {x}, x ∈ Suc x.
  Proof.
    intros.
    unfold Suc.
    apply insert_propr.
    eauto with zf.
  Qed.

  Lemma suc_in_ϵ_Suc : forall {n x},
      n ∈ ϵ_iter nat_Γ x -> ⟨∅,n⟩ ∈ ϵ_iter nat_Γ (Suc x).
  Proof.
    intros.
    rewrite ϵ_iter_prop.
    assert (⟨∅,n⟩ ∈ nat_Γ (ϵ_iter nat_Γ x)).
    exact (s_in_nat_Γ H).
    assert (nat_Γ (ϵ_iter nat_Γ x) ∈ replacement (fun y (_ : y ∈ Suc x) => nat_Γ (ϵ_iter nat_Γ y))).
    apply replacement_prop.
    exists x. exists x_in_Suc_x. auto.
    eauto with zf.
  Qed.
  
  Lemma s_in_nat : forall {n}, n ∈ nat -> ⟨∅,n⟩ ∈ nat.
  Proof.
    unfold nat.
    intros.
    apply union_propr in H.
    destruct H. destruct H.
    apply replacement_prop in H.
    destruct H. destruct H.
    assert (Suc x0 ∈ ω) by eauto with zf.
    assert (⟨∅,n⟩ ∈ ϵ_iter nat_Γ (Suc x0)).
    apply suc_in_ϵ_Suc.
    rewrite H. auto.
    assert (ϵ_iter nat_Γ (Suc x0) ∈ replacement (fun x (_: x ∈ ω) => ϵ_iter nat_Γ x)).
    apply replacement_prop.
    exists (Suc x0). exists H1. eauto with zf.
    eauto with zf.
  Qed.

  Lemma replacement_of_empty : forall {f},
      @replacement ∅ f ≡ ∅.
  Proof.
    intros.
    apply equiv_ext.
    split; intros.
    apply replacement_prop in H.
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
    apply union_propr in H.
    destruct H. destruct H.
    apply empty_prop in H.
    contradiction.
    apply empty_prop in H.
    contradiction.
  Qed.
    
  Lemma z_in_nat : ⟨∅ +> ∅, ∅⟩ ∈ nat.
  Proof.
    unfold nat.
    apply union_propl.
    exists (nat_Γ ∅). split.
    apply replacement_prop.
    exists (∅ +> ∅).
    assert (∅ +> ∅ ∈ ω) by eauto with zf.
    exists H.
    rewrite ϵ_iter_prop.
    apply equiv_ext.
    split; intros.
    apply union_propr in H0.
    destruct H0.
    destruct H0.
    apply replacement_prop in H0.
    destruct H0.
    destruct H0.
    assert (x0 ≡ ∅).
    destruct (insert_propl x1).
    apply empty_prop in H2.
    contradiction.
    auto.
    rewrite H2 in *.
    rewrite ϵ_iter_prop in H0.
    rewrite replacement_of_empty in H0.
    rewrite union_empty in H0.
    subst x.
    auto.
    apply union_propl.
    exists (nat_Γ ∅). split.
    apply replacement_prop.
    exists ∅. assert (∅ ∈ ∅ +> ∅) by eauto with zf.
    exists H1.
    rewrite ϵ_iter_prop.
    rewrite replacement_of_empty.
    rewrite union_empty.
    auto.
    auto.
    unfold nat_Γ.
    simpl.
    rewrite replacement_of_empty.
    rewrite union_empty.
    apply union2_prop.
    right.
    apply union2_prop.
    left.
    eauto with zf.
  Qed.

  Definition monotone Γ := forall x y, x ⊆ y -> Γ x ⊆ Γ y.

  Lemma union_monotone : monotone union.
  Proof.
    unfold monotone.
    unfold subset.
    intros.
    apply union_propl.
    apply union_propr in H0.
    destruct H0. destruct H0.
    apply H in H0.
    exists x1. eauto.
  Qed.

  Definition monotone_dom {x} (Γ: forall y, y ∈ x -> set) :=
    forall {z w} (p: z ∈ x) (p0: w ∈ x), z ⊆ w -> Γ z p ⊆ Γ w p0.

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
    apply replacement_prop in H.
    destruct H. destruct H.
    subst x.
    apply replacement_prop.
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
    apply union_propr in H0.
    (* therefore ∃x1 ∈ { Γ(ϵ_iter Γ y) | y ∈ x} s.t. x0 ∈ x1 *)
    destruct H0. destruct H0.
    apply replacement_prop in H0.
    (* therefore ∃x2 ∈ x s.t Γ(ϵ_iter Γ x2) ≡ x1 *)
    destruct H0. destruct H0.
    subst x1.
    (* so x0 ∈ Γ(ϵ_iter Γ x2) *)
    rewrite ϵ_iter_prop.
    (* it suffices to prove x0 ∈ ⋃{ Γ(ϵ_iter Γ x) | x ∈ y } *)
    apply union_propl.
    (* so we have to provide a y0 ∈ { Γ(ϵ_iter Γ x) | x ∈ y} s.t. x0 ∈ y0 *)
    exists (Γ (ϵ_iter Γ x2)).
    split.
    apply replacement_prop.
    (* Γ(ϵ_iter Γ x2) ∈ { Γ(ϵ_iter Γ x) | x ∈ y } as x2 ∈ y *)
    exists x2. exists (H x2 x3). auto.
    (* as previously proven, x0 ∈ Γ(ϵ_iter Γ x2) *)
    auto.
  Qed.

  Lemma subset_infinity : forall {x}, x ∈ ω -> x ⊆ ω.
  Proof.
    apply ω_induction; unfold subset; intros.
    assert (Suc x ∈ ω) by eauto with zf.
    unfold Suc in *.
    apply insert_propl in H1.
    destruct H1.
    eauto.
    subst x0.
    auto.
    apply empty_prop in H.
    contradiction.
  Qed.
  
  Lemma nat_least : forall {x}, x ∈ nat -> x ≡ ⟨∅+>∅,∅⟩ \/ exists x0, x ≡ ⟨∅,x0⟩ /\ x0 ∈ nat.
  Proof.
    intros.
    unfold nat in H.
    unfold lfp in H.
    apply union_propr in H.
    destruct H. destruct H.
    apply replacement_prop in H.
    destruct H. destruct H.
    subst x0.
    rewrite ϵ_iter_prop in H0.
    apply union_propr in H0.
    destruct H0. destruct H.
    apply replacement_prop in H.
    destruct H. destruct H.
    unfold nat_Γ in H.
    subst x0. apply union2_prop in H0.
    destruct H0.
    apply union_propr in H.
    destruct H. destruct H.
    apply replacement_prop in H.
    destruct H. destruct H.
    simpl in *. right.
    subst x0. apply insert_propl in H0.
    destruct H0.
    apply empty_prop in H.
    contradiction.
    exists x5. split. auto.
    unfold nat.
    assert (x3 ∈ ω).
    apply subset_infinity in x2.
    apply x2 in x4. auto.
    unfold lfp.
    apply union_propl.
    exists ( ϵ_iter (fun X : set => (⋃ replacement (fun (x : set) (_ : x ∈ X) => ⟨ ∅, x ⟩ +> ∅)) ∪ ((⟨ ∅ +> ∅, ∅ ⟩ +> ∅) ∪ ∅)) x3).
    split.
    apply replacement_prop.
    exists x3. exists H0. auto.
    auto.
    apply union2_prop in H.
    destruct H.
    apply insert_propl in H.
    destruct H.
    apply empty_prop in H.
    contradiction.
    left. auto.
    apply empty_prop in H.
    contradiction.
  Qed.
  
  Lemma nat_fixpoint : nat_Γ nat = nat.
  Proof.
    apply equiv_ext.
    split; intros.
    unfold nat_Γ in H.
    simpl in H.
    apply union2_prop in H.
    destruct H.
    apply union_propr in H.
    destruct H. destruct H.
    apply replacement_prop in H.
    destruct H. destruct H.
    subst x.
    apply insert_propl in H0.
    destruct H0.
    auto.
    apply empty_prop in H.
    contradiction.
    subst z.
    apply s_in_nat.
    auto.
    apply union2_prop in H.
    destruct H.
    apply insert_propl in H.
    destruct H.
    auto.
    apply empty_prop in H.
    contradiction.
    subst z.
    apply z_in_nat.
    auto.
    apply empty_prop in H.
    contradiction.
    unfold nat_Γ.
    apply union2_prop.
    apply nat_least in H.
    destruct H.
    subst z.
    right.
    apply union2_prop.
    left.
    simpl.
    eauto with zf.
    destruct H. destruct H.
    left.
    simpl.
    subst z.
    assert (⟨∅,x⟩ ∈ ⟨∅,x⟩ +> ∅) by eauto with zf.
    assert (⟨∅,x⟩ +> ∅ ∈ replacement (fun (x0 : set) (_ : x0 ∈ nat) => ⟨ ∅, x0 ⟩ +> ∅)).
    apply replacement_prop.
    exists x. exists H0. auto.
    eauto with zf.
  Qed.

  Lemma infinity_only_contains_nats :
    forall {x}, x ∈ ω -> x ≡ ∅ \/ exists n, n ∈ ω /\ x ≡ Suc n.
  Proof.
    apply ω_induction; intros.
    right. exists x. auto.
    left. auto.
  Qed.

  Definition fin := nat_rect (fun _ => set) ∅ (fun _ n => n +> ∅).

  Definition tree_Γ X := ⟦(has x, has y, ins ⟨∅, ⟨x, y⟩⟩) :: (ins ⟨∅+>∅,∅⟩) :: nil⟧X.

  Definition trees := lfp tree_Γ.

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

  Lemma leaf_in_tree_Γ : forall {x}, ⟨∅+>∅,∅⟩ ∈ tree_Γ x.
  Proof.
    intros.
    unfold tree_Γ.
    simpl.
    apply union2_prop.
    right.
    apply union2_prop.
    left.
    eauto with zf.
  Qed.

  Lemma leaf_in_trees : ⟨∅+>∅,∅⟩ ∈ trees.
  Proof.
    unfold trees.
    unfold lfp.
    apply union_propl.
    exists (⟨∅+>∅,∅⟩+>∅).
    split.
    apply replacement_prop.
    exists (∅+>∅).
    assert (∅+>∅∈ω) by eauto with zf.
    exists H. rewrite ϵ_iter_prop.
    apply equiv_ext.
    split; intros.
    apply union_propr in H0.
    destruct H0. destruct H0.
    apply replacement_prop in H0.
    destruct H0. destruct H0.
    subst x.
    apply insert_propl in x1.
    destruct x1. apply empty_prop in H0.
    contradiction.
    subst x0.
    rewrite ϵ_iter_empty in H1.
    unfold tree_Γ in H1.
    simpl in H1.
    apply union2_prop in H1.
    destruct H1.
    rewrite replacement_of_empty in H0.
    rewrite union_empty in H0.
    apply empty_prop in H0.
    contradiction.
    apply union2_prop in H0.
    destruct H0.
    auto.
    apply empty_prop in H0.
    contradiction.
    apply insert_propl in H0.
    destruct H0.
    apply empty_prop in H0.
    contradiction.
    subst z.
    apply union_propl.
    exists (⟨∅+>∅,∅⟩+>∅).
    split.
    apply replacement_prop.
    exists ∅. assert (∅∈∅+>∅) by eauto with zf.
    exists H0. rewrite ϵ_iter_empty. unfold tree_Γ.
    simpl. rewrite replacement_of_empty. rewrite union_empty.
    assert (forall x, x ∪ ∅ ≡ x).
    intros. apply equiv_ext.
    split; intros.
    apply union2_prop in H1.
    destruct H1.
    auto.
    apply empty_prop in H1.
    contradiction.
    apply union2_prop.
    auto.
    rewrite (H1 _).
    assert (forall x, ∅ ∪ x ≡ x).
    intros. apply equiv_ext.
    split; intros.
    apply union2_prop in H2.
    destruct H2.
    apply empty_prop in H2.
    contradiction.
    auto.
    apply union2_prop.
    eauto with zf.
    rewrite (H2 _).
    auto.
    eauto with zf.
    eauto with zf.
  Qed.

  Lemma union2_comm : forall {x y}, x ∪ y ≡ y ∪ x.
  Proof.
    intros.
    apply equiv_ext.
    split; intros;
    apply union2_prop in H;
    apply union2_prop;
    destruct H; auto.
  Qed.

  Lemma union2_assoc : forall {x y z}, x ∪ (y ∪ z) ≡ (x ∪ y) ∪ z.
  Proof.
    intros.
    apply equiv_ext.
    split; intros.
    apply union2_prop.
    apply union2_prop in H.
    destruct H.
    left.
    apply union2_prop.
    auto.
    apply union2_prop in H.
    destruct H.
    left.
    apply union2_prop.
    auto.
    auto.
    apply union2_prop.
    apply union2_prop in H.
    destruct H.
    apply union2_prop in H.
    destruct H.
    left.
    auto.
    right.
    apply union2_prop.
    auto.
    right.
    apply union2_prop.
    auto.
  Qed.

  Lemma union2_ident : forall {x}, x ∪ ∅ ≡ x.
  Proof.
    intros.
    apply equiv_ext.
    split; intros.
    apply union2_prop in H.
    destruct H.
    auto.
    apply empty_prop in H.
    contradiction.
    apply union2_prop.
    auto.
  Qed.

  Lemma branch_in_tree_Γ :
    forall {x y z}, x ∈ z -> y ∈ z -> ⟨∅,⟨x,y⟩⟩ ∈ tree_Γ z.
  Proof.
    intros.
    unfold tree_Γ.
    simpl.
    apply union2_prop.
    left.
    apply union_propl.
    exists (⋃ replacement (fun (x1 : set) (_ : x1 ∈ z) => ⟨ ∅, ⟨ x, x1 ⟩ ⟩ +> ∅)).
    split.
    apply replacement_prop.
    exists x. exists H. auto.
    apply union_propl.
    exists (⟨ ∅, ⟨ x, y ⟩ ⟩ +> ∅).
    split.
    apply replacement_prop.
    exists y. exists H0. auto.
    eauto with zf.
  Qed.
  
  Lemma branch_in_suc :
    forall {x y z}, x ∈ ϵ_iter tree_Γ z -> y ∈ ϵ_iter tree_Γ z -> ⟨∅,⟨x,y⟩⟩ ∈ ϵ_iter tree_Γ (Suc z).
  Proof.
    intros.
    rewrite ϵ_iter_prop.
    apply union_propl.
    exists (tree_Γ (ϵ_iter tree_Γ z)).
    split.
    apply replacement_prop.
    exists z. assert (z ∈ Suc z) by eauto with zf.
    exists H1. auto.
    apply branch_in_tree_Γ; auto.
  Qed.

  Lemma in_ϵ_iter_sup :
    forall {Γ x y z}, x ∈ ϵ_iter Γ y -> y ⊆ z -> x ∈ ϵ_iter Γ z.
  Proof.
    intros.
    rewrite ϵ_iter_prop in H.
    apply union_propr in H.
    destruct H. destruct H.
    apply replacement_prop in H.
    destruct H. destruct H.
    subst x0.
    rewrite ϵ_iter_prop.
    apply union_propl.
    exists (Γ (ϵ_iter Γ x1)).
    split.
    apply replacement_prop.
    exists x1. exists (H0 _ x2).
    auto.
    auto.
  Qed.

  Lemma in_in_ω_in_ω :
    forall {x}, x ∈ ω -> forall {y}, y ∈ x -> y ∈ ω.
  Proof.
    apply (@ω_induction (fun x => forall y, y ∈ x -> y ∈ ω)).
    intros.
    apply insert_propl in H1.
    destruct H1.
    eauto.
    subst y. auto.
    intros.
    apply empty_prop in H.
    contradiction.
  Qed.

  Lemma pred_in_ω :
    forall {x}, Suc x ∈ ω -> x ∈ ω.
  Proof.
    intros.
    assert (x ∈ Suc x) by apply x_in_Suc_x.
    eapply in_in_ω_in_ω.
    exact H.
    auto.
  Qed.

  Lemma in_x_in_ω_subset_x : forall {x}, x ∈ ω -> forall {y}, y ∈ ω -> x ∈ y -> x ⊆ y.
  Proof.
    intros ? ?.
    apply (@ω_induction (fun y => x ∈ y -> x ⊆ y)).
    unfold subset.
    intros.
    apply insert_propl in H2.
    destruct H2.
    assert (x1 ∈ x0) by eauto.
    apply insert_propr. auto.
    subst x.
    apply insert_propr. auto.
    intros.
    apply empty_prop in H0.
    contradiction.
  Qed.

  Lemma union2_insert :
    forall {x y z}, x ∪ (y +> z) ≡ y +> (x ∪ z).
  Proof.
    intros.
    apply equiv_ext.
    split; intros.
    apply union2_prop in H.
    apply insert_propr.
    destruct H.
    left.
    apply union2_prop.
    auto.
    apply insert_propl in H.
    destruct H.
    left.
    apply union2_prop.
    auto.
    auto.
    apply insert_propl in H.
    apply union2_prop.
    destruct H.
    apply union2_prop in H.
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

  Lemma empty_nat :
    forall {x}, x ∈ ω -> ∅ ∈ x \/ x ≡ ∅.
  Proof.
    apply ω_induction.
    intros.
    left.
    destruct H0.
    eauto with zf.
    subst x.
    eauto with zf.
    right.
    auto.
  Qed.

  Lemma nat_suc_member :
    forall {x}, x ∈ ω -> forall {y}, y ∈ ω -> y ∈ x -> Suc y ∈ Suc x.
  Proof.
    apply (@ω_induction (fun x => forall y, y ∈ ω -> y ∈ x -> Suc y ∈ Suc x)).
    intros.
    apply infinity_only_contains_nats in H1.
    destruct H1.
    subst y.
    apply insert_propl in H2.
    destruct H2.
    assert (Suc ∅ ∈ Suc x).
    exact (H0 ∅ infinity_propz H1).
    eauto with zf.
    subst x.
    eauto with zf.
    destruct H1. destruct H1.
    subst y.
    apply insert_propl in H2.
    destruct H2.
    assert (Suc (Suc x0) ∈ Suc x) by eauto with zf.
    eauto with zf.
    subst x.
    eauto with zf.
    intros.
    apply empty_prop in H0.
    contradiction.
  Qed.

  Lemma nat_cmp :
    forall {x}, x ∈ ω -> forall {y}, y ∈ ω -> x ∈ y \/ y ∈ x \/ x ≡ y.
  Proof.
    apply (@ω_induction (fun x => forall y, y ∈ ω -> x ∈ y \/ y ∈ x \/ x ≡ y)).
    intros.
    apply infinity_only_contains_nats in H1.
    destruct H1.
    subst y.
    right. left.
    destruct (empty_nat H).
    eauto with zf.
    subst x.
    eauto with zf.
    destruct H1.
    destruct H1.
    subst y.
    destruct (H0 _ H1).
    left.
    apply nat_suc_member in H2; auto.
    destruct H2.
    right. left.
    apply nat_suc_member in H2; auto.
    right. right.
    subst x. auto.
    intros.
    apply empty_nat in H.
    destruct H; auto.
  Qed.
  
  Lemma maximum :
    forall {x}, x ∈ ω -> forall {y}, y ∈ ω -> x ⊆ y \/ y ⊆ x.
  Proof.
    apply (@ω_induction (fun x => forall y, y ∈ ω -> x ⊆ y \/ y ⊆ x)).
    intros.
    apply infinity_only_contains_nats in H1.
    destruct H1.
    subst y.
    right. apply empty_subset.
    destruct H1. destruct H1.
    subst y.
    destruct (nat_cmp H H1).
    apply nat_suc_member in H2.
    apply in_x_in_ω_subset_x in H2.
    auto.
    eauto with zf.
    eauto with zf.
    auto.
    auto.
    destruct H2.
    apply nat_suc_member in H2.
    apply in_x_in_ω_subset_x in H2.
    auto.
    eauto with zf.
    eauto with zf.
    auto.
    auto.
    subst x.
    left.
    unfold subset.
    intros.
    auto.
    intros.
    left.
    exact empty_subset.
  Qed.

  Lemma has_meet :
    forall {x y}, x ∈ ω -> y ∈ ω -> exists z, z ∈ ω /\ x ⊆ z /\ y ⊆ z.
  Proof.
    intros.
    destruct (maximum H H0).
    exists y.
    split.
    auto.
    split.
    auto.
    unfold subset.
    intros.
    auto.
    exists x.
    split.
    auto.
    split.
    unfold subset.
    intros.
    auto.
    auto.
  Qed.

  Lemma branch_in_tree :
    forall {x y}, x ∈ trees -> y ∈ trees -> ⟨∅,⟨x,y⟩⟩ ∈ trees.
  Proof.
    unfold trees.
    unfold lfp.
    intros.
    apply union_propr in H.
    destruct H. destruct H.
    apply union_propr in H0.
    destruct H0. destruct H0.
    apply replacement_prop in H.
    destruct H. destruct H.
    apply replacement_prop in H0.
    destruct H0. destruct H0.
    subst x0. subst x1.
    apply union_propl.
    destruct (has_meet x3 x5).
    destruct H.
    exists (ϵ_iter tree_Γ (Suc x0)).
    split.
    apply replacement_prop.
    exists (Suc x0). assert (Suc x0 ∈ ω) by eauto with zf.
    exists H3. auto.
    destruct H0.
    pose (in_ϵ_iter_sup H1 H0).
    pose (in_ϵ_iter_sup H2 H3).
    rewrite ϵ_iter_prop.
    apply union_propl.
    exists (tree_Γ (ϵ_iter tree_Γ x0)).
    split.
    apply replacement_prop.
    exists x0. assert (x0 ∈ Suc x0) by eauto with zf.
    exists H4. auto. exact (branch_in_tree_Γ m m0).
  Qed.

  Lemma tree_fixpoint : tree_Γ trees ≡ trees.
  Proof.
    apply equiv_ext.
    split; intros.
    unfold tree_Γ in H.
    simpl in H.
    apply union2_prop in H.
    destruct H.
    apply union_propr in H.
    destruct H. destruct H.
    apply replacement_prop in H.
    destruct H. destruct H.
    subst x.
    apply union_propr in H0.
    destruct H0. destruct H.
    apply replacement_prop in H.
    destruct H. destruct H.
    subst x.
    apply insert_propl in H0.
    destruct H0.
    apply empty_prop in H.
    contradiction.
    subst z.
    apply branch_in_tree; auto.
    apply union2_prop in H.
    destruct H.
    apply insert_propl in H.
    destruct H.
    apply empty_prop in H.
    contradiction.
    subst z.
    apply leaf_in_trees.
    apply empty_prop in H.
    contradiction.
    unfold trees in H.
    unfold lfp in H.
    apply union_propr in H.
    destruct H. destruct H.
    apply replacement_prop in H.
    destruct H. destruct H.
    subst x.
    rewrite ϵ_iter_prop in H0.
    apply union_propr in H0.
    destruct H0. destruct H.
    apply replacement_prop in H.
    destruct H. destruct H.
    subst x.
    unfold tree_Γ at 1 in H0.
    simpl in H0.
    apply union2_prop in H0.
    destruct H0.
    apply union_propr in H.
    destruct H. destruct H.
    apply replacement_prop in H.
    destruct H. destruct H.
    subst x. apply union_propr in H0.
    destruct H0. destruct H.
    apply replacement_prop in H.
    destruct H. destruct H.
    subst x.
    apply insert_propl in H0.
    destruct H0.
    apply empty_prop in H.
    contradiction.
    subst z.
    apply in_in_ω_in_ω in x3.
    apply branch_in_tree_Γ.
    unfold trees.
    unfold lfp.
    apply union_propl.
    exists (ϵ_iter tree_Γ x2).
    split.
    apply replacement_prop.
    exists x2. exists x3. auto.
    auto.
    unfold trees.
    unfold lfp.
    apply union_propl.
    exists (ϵ_iter tree_Γ x2).
    split.
    apply replacement_prop.
    exists x2. exists x3. auto.
    auto.
    auto.
    apply union2_prop in H.
    destruct H.
    apply insert_propl in H.
    destruct H.
    apply empty_prop in H.
    contradiction.
    subst z.
    apply leaf_in_tree_Γ.
    apply empty_prop in H.
    contradiction.
  Qed.

End IZFConstructions.

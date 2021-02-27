Require Import IZF.
Require Import IZFOmega.
Require Import Lists.List.

Module IZFConstructionsF (ST: IZF).
  Import ST.
  Module IZFOmegaM := IZFOmegaF ST.
  Include IZFOmegaM.

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

  Definition nat_Γ X := ⟦(has n, ins ⟨∅,n⟩) :: (ins ⟨∅ +> ∅, ∅⟩) :: nil⟧X.

  Definition nat := lfp nat_Γ.

  Lemma s_in_nat_Γ : forall {n x}, n ∈ x -> ⟨∅,n⟩ ∈ nat_Γ x.
  Proof.
    unfold nat_Γ.
    intros.
    assert (⟨∅,n⟩ ∈ ⟨∅,n⟩ +> ∅) by eauto with zf.
    assert (⟨∅,n⟩ +> ∅ ∈ replacement (fun n (_: n ∈ x) => ⟨ ∅, n ⟩ +> ∅)).
    apply replacement_propG.
    exists n. exists H. eauto with zf.
    assert (⟨ ∅, n ⟩ ∈ (⋃ replacement (fun (n0 : set) (_ : n0 ∈ x) => ⟨ ∅, n0 ⟩ +> ∅))).
    eauto with zf.
    apply union2_propG.
    left.
    auto.
  Qed.

  Lemma suc_in_ϵ_Suc : forall {n x},
      n ∈ ϵ_iter nat_Γ x -> ⟨∅,n⟩ ∈ ϵ_iter nat_Γ (Suc x).
  Proof.
    intros.
    rewrite ϵ_iter_prop.
    assert (⟨∅,n⟩ ∈ nat_Γ (ϵ_iter nat_Γ x)).
    exact (s_in_nat_Γ H).
    assert (nat_Γ (ϵ_iter nat_Γ x) ∈ replacement (fun y (_ : y ∈ Suc x) => nat_Γ (ϵ_iter nat_Γ y))).
    apply replacement_propG.
    exists x. exists x_in_Suc_x. auto.
    eauto with zf.
  Qed.

  Lemma s_in_nat : forall {n}, n ∈ nat -> ⟨∅,n⟩ ∈ nat.
  Proof.
    unfold nat.
    intros.
    apply union_propH in H.
    destruct H. destruct H.
    apply replacement_propH in H.
    destruct H. destruct H.
    assert (Suc x0 ∈ ω) by eauto with zf.
    assert (⟨∅,n⟩ ∈ ϵ_iter nat_Γ (Suc x0)).
    apply suc_in_ϵ_Suc.
    rewrite H. auto.
    assert (ϵ_iter nat_Γ (Suc x0) ∈ replacement (fun x (_: x ∈ ω) => ϵ_iter nat_Γ x)).
    apply replacement_propG.
    exists (Suc x0). exists H1. eauto with zf.
    eauto with zf.
  Qed.

  Lemma z_in_nat : ⟨∅ +> ∅, ∅⟩ ∈ nat.
  Proof.
    unfold nat.
    apply union_propG.
    exists (nat_Γ ∅). split.
    apply replacement_propG.
    exists (∅ +> ∅).
    assert (∅ +> ∅ ∈ ω) by eauto with zf.
    exists H.
    rewrite ϵ_iter_prop.
    apply equiv_ext.
    split; intros.
    apply union_propH in H0.
    destruct H0.
    destruct H0.
    apply replacement_propH in H0.
    destruct H0.
    destruct H0.
    assert (x0 ≡ ∅).
    destruct (insert_propH x1).
    apply empty_prop in H2.
    contradiction.
    auto.
    rewrite H2 in *.
    rewrite ϵ_iter_prop in H0.
    rewrite replacement_of_empty in H0.
    rewrite union_empty in H0.
    subst x.
    auto.
    apply union_propG.
    exists (nat_Γ ∅). split.
    apply replacement_propG.
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
    apply union2_propG.
    right.
    apply union2_propG.
    left.
    eauto with zf.
  Qed.

  Lemma nat_nojunk : forall {x}, x ∈ nat -> x ≡ ⟨∅+>∅,∅⟩ \/ exists x0, x ≡ ⟨∅,x0⟩ /\ x0 ∈ nat.
  Proof.
    intros.
    unfold nat in H.
    unfold lfp in H.
    apply union_propH in H.
    destruct H. destruct H.
    apply replacement_propH in H.
    destruct H. destruct H.
    subst x0.
    rewrite ϵ_iter_prop in H0.
    apply union_propH in H0.
    destruct H0. destruct H.
    apply replacement_propH in H.
    destruct H. destruct H.
    unfold nat_Γ in H.
    subst x0. apply union2_propH in H0.
    destruct H0.
    apply union_propH in H.
    destruct H. destruct H.
    apply replacement_propH in H.
    destruct H. destruct H.
    simpl in *. right.
    subst x0. apply insert_propH in H0.
    destruct H0.
    apply empty_prop in H.
    contradiction.
    exists x5. split. auto.
    unfold nat.
    assert (x3 ∈ ω).
    apply subset_infinity in x2.
    apply x2 in x4. auto.
    unfold lfp.
    apply union_propG.
    exists ( ϵ_iter (fun X : set => (⋃ replacement (fun (x : set) (_ : x ∈ X) => ⟨ ∅, x ⟩ +> ∅)) ∪ ((⟨ ∅ +> ∅, ∅ ⟩ +> ∅) ∪ ∅)) x3).
    split.
    apply replacement_propG.
    exists x3. exists H0. auto.
    auto.
    apply union2_propH in H.
    destruct H.
    apply insert_propH in H.
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
    apply union2_propH in H.
    destruct H.
    apply union_propH in H.
    destruct H. destruct H.
    apply replacement_propH in H.
    destruct H. destruct H.
    subst x.
    apply insert_propH in H0.
    destruct H0.
    auto.
    apply empty_prop in H.
    contradiction.
    subst z.
    apply s_in_nat.
    auto.
    apply union2_propH in H.
    destruct H.
    apply insert_propH in H.
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
    apply union2_propG.
    apply nat_nojunk in H.
    destruct H.
    subst z.
    right.
    apply union2_propG.
    left.
    simpl.
    eauto with zf.
    destruct H. destruct H.
    left.
    simpl.
    subst z.
    assert (⟨∅,x⟩ ∈ ⟨∅,x⟩ +> ∅) by eauto with zf.
    assert (⟨∅,x⟩ +> ∅ ∈ replacement (fun (x0 : set) (_ : x0 ∈ nat) => ⟨ ∅, x0 ⟩ +> ∅)).
    apply replacement_propG.
    exists x. exists H0. auto.
    eauto with zf.
  Qed.

  Definition tree_Γ X := ⟦(has x, has y, ins ⟨∅, ⟨x, y⟩⟩) :: (ins ⟨∅+>∅,∅⟩) :: nil⟧X.

  Definition trees := lfp tree_Γ.

  Lemma leaf_in_tree_Γ : forall {x}, ⟨∅+>∅,∅⟩ ∈ tree_Γ x.
  Proof.
    intros.
    unfold tree_Γ.
    simpl.
    apply union2_propG.
    right.
    apply union2_propG.
    left.
    eauto with zf.
  Qed.

  Lemma leaf_in_trees : ⟨∅+>∅,∅⟩ ∈ trees.
  Proof.
    unfold trees.
    unfold lfp.
    apply union_propG.
    exists (⟨∅+>∅,∅⟩+>∅).
    split.
    apply replacement_propG.
    exists (∅+>∅).
    assert (∅+>∅∈ω) by eauto with zf.
    exists H. rewrite ϵ_iter_prop.
    apply equiv_ext.
    split; intros.
    apply union_propH in H0.
    destruct H0. destruct H0.
    apply replacement_propH in H0.
    destruct H0. destruct H0.
    subst x.
    apply insert_propH in x1.
    destruct x1. apply empty_prop in H0.
    contradiction.
    subst x0.
    rewrite ϵ_iter_empty in H1.
    unfold tree_Γ in H1.
    simpl in H1.
    apply union2_propH in H1.
    destruct H1.
    rewrite replacement_of_empty in H0.
    rewrite union_empty in H0.
    apply empty_prop in H0.
    contradiction.
    apply union2_propH in H0.
    destruct H0.
    auto.
    apply empty_prop in H0.
    contradiction.
    apply insert_propH in H0.
    destruct H0.
    apply empty_prop in H0.
    contradiction.
    subst z.
    apply union_propG.
    exists (⟨∅+>∅,∅⟩+>∅).
    split.
    apply replacement_propG.
    exists ∅. assert (∅∈∅+>∅) by eauto with zf.
    exists H0. rewrite ϵ_iter_empty. unfold tree_Γ.
    simpl. rewrite replacement_of_empty. rewrite union_empty.
    assert (forall x, x ∪ ∅ ≡ x).
    intros. apply equiv_ext.
    split; intros.
    apply union2_propH in H1.
    destruct H1.
    auto.
    apply empty_prop in H1.
    contradiction.
    apply union2_propG.
    auto.
    rewrite (H1 _).
    assert (forall x, ∅ ∪ x ≡ x).
    intros. apply equiv_ext.
    split; intros.
    apply union2_propH in H2.
    destruct H2.
    apply empty_prop in H2.
    contradiction.
    auto.
    apply union2_propG.
    eauto with zf.
    rewrite (H2 _).
    auto.
    eauto with zf.
    eauto with zf.
  Qed.

  Lemma branch_in_tree_Γ :
    forall {x y z}, x ∈ z -> y ∈ z -> ⟨∅,⟨x,y⟩⟩ ∈ tree_Γ z.
  Proof.
    intros.
    unfold tree_Γ.
    simpl.
    apply union2_propG.
    left.
    apply union_propG.
    exists (⋃ replacement (fun (x1 : set) (_ : x1 ∈ z) => ⟨ ∅, ⟨ x, x1 ⟩ ⟩ +> ∅)).
    split.
    apply replacement_propG.
    exists x. exists H. auto.
    apply union_propG.
    exists (⟨ ∅, ⟨ x, y ⟩ ⟩ +> ∅).
    split.
    apply replacement_propG.
    exists y. exists H0. auto.
    eauto with zf.
  Qed.
  
  Lemma branch_in_suc :
    forall {x y z}, x ∈ ϵ_iter tree_Γ z -> y ∈ ϵ_iter tree_Γ z -> ⟨∅,⟨x,y⟩⟩ ∈ ϵ_iter tree_Γ (Suc z).
  Proof.
    intros.
    rewrite ϵ_iter_prop.
    apply union_propG.
    exists (tree_Γ (ϵ_iter tree_Γ z)).
    split.
    apply replacement_propG.
    exists z. assert (z ∈ Suc z) by eauto with zf.
    exists H1. auto.
    apply branch_in_tree_Γ; auto.
  Qed.

  Lemma branch_in_tree :
    forall {x y}, x ∈ trees -> y ∈ trees -> ⟨∅,⟨x,y⟩⟩ ∈ trees.
  Proof.
    unfold trees.
    unfold lfp.
    intros.
    apply union_propH in H.
    destruct H. destruct H.
    apply union_propH in H0.
    destruct H0. destruct H0.
    apply replacement_propH in H.
    destruct H. destruct H.
    apply replacement_propH in H0.
    destruct H0. destruct H0.
    subst x0. subst x1.
    apply union_propG.
    destruct (has_meet x3 x5).
    destruct H.
    exists (ϵ_iter tree_Γ (Suc x0)).
    split.
    apply replacement_propG.
    exists (Suc x0). assert (Suc x0 ∈ ω) by eauto with zf.
    exists H3. auto.
    destruct H0.
    pose (in_ϵ_iter_sup H1 H0).
    pose (in_ϵ_iter_sup H2 H3).
    rewrite ϵ_iter_prop.
    apply union_propG.
    exists (tree_Γ (ϵ_iter tree_Γ x0)).
    split.
    apply replacement_propG.
    exists x0. assert (x0 ∈ Suc x0) by eauto with zf.
    exists H4. auto. exact (branch_in_tree_Γ m m0).
  Qed.

  Lemma tree_fixpoint : tree_Γ trees ≡ trees.
  Proof.
    apply equiv_ext.
    split; intros.
    unfold tree_Γ in H.
    simpl in H.
    apply union2_propH in H.
    destruct H.
    apply union_propH in H.
    destruct H. destruct H.
    apply replacement_propH in H.
    destruct H. destruct H.
    subst x.
    apply union_propH in H0.
    destruct H0. destruct H.
    apply replacement_propH in H.
    destruct H. destruct H.
    subst x.
    apply insert_propH in H0.
    destruct H0.
    apply empty_prop in H.
    contradiction.
    subst z.
    apply branch_in_tree; auto.
    apply union2_propH in H.
    destruct H.
    apply insert_propH in H.
    destruct H.
    apply empty_prop in H.
    contradiction.
    subst z.
    apply leaf_in_trees.
    apply empty_prop in H.
    contradiction.
    unfold trees in H.
    unfold lfp in H.
    apply union_propH in H.
    destruct H. destruct H.
    apply replacement_propH in H.
    destruct H. destruct H.
    subst x.
    rewrite ϵ_iter_prop in H0.
    apply union_propH in H0.
    destruct H0. destruct H.
    apply replacement_propH in H.
    destruct H. destruct H.
    subst x.
    unfold tree_Γ at 1 in H0.
    simpl in H0.
    apply union2_propH in H0.
    destruct H0.
    apply union_propH in H.
    destruct H. destruct H.
    apply replacement_propH in H.
    destruct H. destruct H.
    subst x. apply union_propH in H0.
    destruct H0. destruct H.
    apply replacement_propH in H.
    destruct H. destruct H.
    subst x.
    apply insert_propH in H0.
    destruct H0.
    apply empty_prop in H.
    contradiction.
    subst z.
    apply in_in_ω_in_ω in x3.
    apply branch_in_tree_Γ.
    unfold trees.
    unfold lfp.
    apply union_propG.
    exists (ϵ_iter tree_Γ x2).
    split.
    apply replacement_propG.
    exists x2. exists x3. auto.
    auto.
    unfold trees.
    unfold lfp.
    apply union_propG.
    exists (ϵ_iter tree_Γ x2).
    split.
    apply replacement_propG.
    exists x2. exists x3. auto.
    auto.
    auto.
    apply union2_propH in H.
    destruct H.
    apply insert_propH in H.
    destruct H.
    apply empty_prop in H.
    contradiction.
    subst z.
    apply leaf_in_tree_Γ.
    apply empty_prop in H.
    contradiction.
  Qed.

End IZFConstructionsF.

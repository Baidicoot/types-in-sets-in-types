Require Import CZF.
Require Import Lists.List.

Module CZFConstructions (ST: CZF).
  Import ST.

  Notation "A ∨ B" := (sum A B) (at level 75).
  
  Inductive ind_rule : Type :=
  | ind : (set -> ind_rule) -> ind_rule
  | ext : forall {S}, (forall x, x ∈ S -> ind_rule) -> ind_rule
  | ins : set -> ind_rule.

  Reserved Notation "⦅ x ⦆ y" (at level 60).
  Fixpoint interp_rule (r: ind_rule) (X: set) : set :=
    match r with
    | ind f => ⋃ (replacement (fun x (_: x ∈ X) => ⦅f x⦆X))
    | ins x => x +> X
    | ext f => ⋃ (replacement (fun x H => ⦅f x H⦆X))
    end
  where "⦅ x ⦆ y" := (interp_rule x y).
  
  Definition union2 (A B: set) := ⋃ (A +> (B +> ∅)).
  Notation "x ∪ y" := (union2 x y) (at level 60).
  
  Lemma union2_prop : forall {A B x}, (x ∈ A ∨ x ∈ B) -> x ∈ A ∪ B.
  Proof.
    intros.
    unfold union2.
    destruct X.
    assert (A ∈ A +> (B +> ∅)).
    destruct (@insert_prop A (B +> ∅)).
    auto.
    eauto with zf.
    assert (B ∈ A +> (B +> ∅)).
    destruct (@insert_prop B ∅).
    destruct (@insert_prop A (B +> ∅)).
    apply s0. auto.
    eauto with zf.
  Qed.
  Hint Resolve union2_prop : zf.
  
  Reserved Notation "⟦ x ⟧ y" (at level 60).
  Fixpoint interp_rules (rs: list ind_rule) (X: set) : set :=
    match rs with
    | nil => X
    | r::rs => (⦅r⦆X) ∪ (⟦rs⟧X)
    end
  where "⟦ x ⟧ y" := (interp_rules x y).

  Fixpoint rule_prop (r: ind_rule) (X: set) (S: set) : Type :=
    match r with
    | ind f => forall x, x ∈ X -> rule_prop (f x) X S
    | ins x => x ∈ S
    | ext f => forall x H, rule_prop (f x H) X S
    end.

  Fixpoint rules_prop_suc (rs: list ind_rule) (X: set) (S: set) : Type :=
    match rs with
    | nil => True
    | r::rs => rule_prop r X S ∧ rules_prop_suc rs X S
    end.

  Definition rules_prop rs X := rules_prop_suc rs X (⟦rs⟧X).

  Notation "'has' x , y" := (ind (fun x => y)) (at level 200, x at level 69).
  Notation "'for' x '∈' y , z" := (ext (fun x (_: x ∈ y) => z)) (at level 200, x at level 69).

  Definition S_rule := has n, ins ⟨∅,n⟩.
  Definition Z_rule := ins ⟨∅ +> ∅, ∅⟩.
  
  Definition ϵ_iter (Γ: set -> set) : set -> set.
  Proof.
    apply induction.
    unfold prop_sound.
    auto.
    exact (fun x X => ⋃ (replacement (fun y H => Γ(X y H)))).
  Defined.

  Lemma ϵ_iter_prop : forall Γ x, ϵ_iter Γ x = ⋃ (replacement (fun y (_: y ∈ x) => Γ(ϵ_iter Γ y))).
  Proof.
    intros.
    unfold ϵ_iter.
    exact induction_prop.
  Qed.

  Definition nat_Γ x := ⟦S_rule :: Z_rule :: nil⟧ x.

  Lemma s_in_nat_Γ : forall {n x}, n ∈ x -> ⟨∅,n⟩ ∈ nat_Γ x.
  Proof.
    intros.
    unfold nat_Γ.
    simpl.
    assert (⟨∅,n⟩ ∈ ⋃ replacement (fun (x0 : set) (_ : x0 ∈ x) => ⟨ ∅, x0 ⟩ +> x)).
    assert (⟨∅,n⟩ ∈ ⟨∅,n⟩ +> x).
    destruct (@insert_prop ⟨∅,n⟩ x).
    auto.
    assert (⟨∅,n⟩ +> x ∈ replacement (fun x0 (_: x0 ∈ x) => ⟨∅,x0⟩ +> x)).
    apply replacement_prop.
    exists n. exists X. eauto with zf.
    eauto with zf.
    eauto with zf.
  Qed.

  Definition nat := ⋃ (replacement (fun x (_: x ∈ ∞) => ϵ_iter nat_Γ x)).

  Lemma x_in_Suc_x : forall {x}, x ∈ Suc x.
  Proof.
    unfold Suc.
    intros.
    destruct (@insert_prop x x).
    eauto with zf.
  Qed.
  
  Lemma nat_in_Suc : forall {p}, p ∈ ∞ -> forall {n}, n ∈ ϵ_iter nat_Γ p -> ⟨∅,n⟩ ∈ ϵ_iter nat_Γ (Suc p).
  Proof.
    intros.
    rewrite ϵ_iter_prop.
    assert (⟨∅,n⟩ ∈ nat_Γ (ϵ_iter nat_Γ p)).
    apply s_in_nat_Γ.
    auto.
    assert (nat_Γ (ϵ_iter nat_Γ p) ∈ replacement (fun y (_: y ∈ Suc p) => nat_Γ (ϵ_iter nat_Γ y))).
    apply replacement_prop.
    exists p. exists x_in_Suc_x. eauto with zf.
    eauto with zf.
  Qed.

  Lemma nat_has_suc : forall x, x ∈ nat -> ⟨∅,x⟩ ∈ nat.
  Proof.
    unfold nat.
    intros.
    apply union_def in X.
    destruct X as [? [? ?]].
    apply replacement_prop in m0.
    destruct m0 as [? [? ?]].
    assert (x ∈ ϵ_iter nat_Γ x1) by eauto with zf.
    assert (Suc x1 ∈ ∞) by eauto with zf.
    apply nat_in_Suc in X.
    assert (ϵ_iter nat_Γ (Suc x1) ∈ replacement (fun x (_: x ∈ ∞) => ϵ_iter nat_Γ x)).
    apply replacement_prop.
    exists (Suc x1). exists X0. eauto with zf.
    eauto with zf.
    auto.
  Qed.

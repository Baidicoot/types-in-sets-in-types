Require Import IZF.
Require Import IZFOmega.

Module IZFTacticsF (ST: IZF).
  Import ST.
  Module IZFOmegaM := IZFOmegaF ST.
  Include IZFOmegaM.
  
  Ltac destructSTHyp :=
    match goal with
    | H : _ ∈ union _ |- _ =>
      apply union_propH in H
    | H : _ ∈ replacement _ |- _ =>
      apply replacement_propH in H
    | H : _ ∈ union2 _ _ |- _ =>
      apply union2_propH in H
    | H : _ ∈ _ × _ |- _ =>
      apply cartesian_product_propH in H
    | H : _ ∈ ⨆_ |- _ =>
      apply disjoint_union_propH in H
    | H : _ ∈ _ +> _ |- _ =>
      apply insert_propH in H
    | H : _ ∈ ∅ |- _ =>
      apply empty_prop in H; contradiction
    | H : _ ∈ selection _ _ |- _ =>
      apply selection_propH in H
    end.

  Ltac crunchH :=
    match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    | H : _ \/ _ |- _ => destruct H
    end.

  Ltac simplST := tryif progress destructSTHyp then repeat crunchH; subst; simplST else idtac.

  Ltac destructSTGoal :=
    match goal with
    | |- _ /\ _ => split
    | |- _ ∈ ⋃ _ =>
      apply union_propG
    | |- _ ∈ replacement _ =>
      apply replacement_propG
    | |- _ ∈ union2 _ _ =>
      apply union2_propG
    | |- _ ∈ _ × _ =>
      apply cartesian_product_propG
    | |- _ ∈ ⨆_ =>
      apply disjoint_union_propG
    | |- _ ∈ _ +> _ =>
      apply insert_propG
    | |- _ ∈ ϵ_iter _ _ =>
      rewrite ϵ_iter_prop
    | |- _ ∈ selection _ _ =>
      apply selection_propG
    end.

  Ltac forcefill k :=
    match goal with
    | H: ?x |- exists (_: ?x), _ =>
      exists H; solve [k]
    end.

  Ltac reduceST := tryif progress destructSTGoal then intros; reduceST else idtac.
  Ltac autoST := tryif progress (simplST; reduceST; eauto) then simplST else idtac.

End IZFTacticsF.

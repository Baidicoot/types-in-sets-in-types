Require Import IZF.
Require Import IZFSets.

Module IZFOmegaF (ST: IZF).
  Import ST.
  Module IZFSetsM := IZFSetsF ST.
  Include IZFSetsM.

  Lemma subset_infinity : forall {x}, x ∈ ω -> x ⊆ ω.
  Proof.
    apply ω_induction; unfold subset; intros.
    assert (Suc x ∈ ω) by eauto with zf.
    unfold Suc in *.
    apply insert_propH in H1.
    destruct H1.
    eauto.
    subst x0.
    auto.
    apply empty_prop in H.
    contradiction.
  Qed.

  Lemma infinity_only_contains_nats :
    forall {x}, x ∈ ω -> x ≡ ∅ \/ exists n, n ∈ ω /\ x ≡ Suc n.
  Proof.
    apply ω_induction; intros.
    right. exists x. auto.
    left. auto.
  Qed.

  Lemma in_in_ω_in_ω :
    forall {x}, x ∈ ω -> forall {y}, y ∈ x -> y ∈ ω.
  Proof.
    apply (@ω_induction (fun x => forall y, y ∈ x -> y ∈ ω)).
    intros.
    apply insert_propH in H1.
    destruct H1.
    eauto.
    subst y. auto.
    intros.
    apply empty_prop in H.
    contradiction.
  Qed.

  Lemma x_in_Suc_x : forall {x}, x ∈ Suc x.
  Proof.
    intros.
    unfold Suc.
    apply insert_propG.
    eauto with zf.
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
    apply insert_propH in H2.
    destruct H2.
    assert (x1 ∈ x0) by eauto.
    apply insert_propG. auto.
    subst x.
    apply insert_propG. auto.
    intros.
    apply empty_prop in H0.
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
    apply insert_propH in H2.
    destruct H2.
    assert (Suc ∅ ∈ Suc x).
    exact (H0 ∅ infinity_propZ H1).
    eauto with zf.
    subst x.
    eauto with zf.
    destruct H1. destruct H1.
    subst y.
    apply insert_propH in H2.
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

End IZFOmegaF.

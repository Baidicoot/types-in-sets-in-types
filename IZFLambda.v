Require Import IZF.
Require Import IZFTactics.

Module IZFLambda (ST: IZF).
  Import ST.
  Module IZFTacticsM := IZFTacticsF ST.
  Include IZFTacticsM.

  Fixpoint tag n :=
    match n with
    | 0 => ∅
    | S n => tag n +> ∅
    end.

  Definition tagall n X :=
    replacement (fun x (_: x ∈ X) => ⟨tag n,x⟩).

  Fixpoint ord n :=
    match n with
    | 0 => ∅
    | S n => Suc (ord n)
    end.

  Definition lam x := ⟨tag 0, x⟩.
  Definition app x y := ⟨tag 1, ⟨x,y⟩⟩.
  Definition var x := ⟨tag 2,x⟩.

  Definition lcΓ :=
    fun X =>
      tagall 0 X ∪ tagall 1 (X × X) ∪ tagall 2 infinity.
  Definition lc := lfp lcΓ.

  Lemma lam_in_lcΓ : forall {x y}, x ∈ y -> lam x ∈ lcΓ y.
  Proof.
    intros.
    unfold lam.
    unfold lcΓ.
    unfold tagall.
    simpl.
    autoST.
    left.
    autoST.
    left.
    autoST.
  Qed.

  Lemma app_in_lcΓ : forall {x y z}, x ∈ z -> y ∈ z -> app x y ∈ lcΓ z.
  Proof.
    intros.
    unfold app.
    unfold lcΓ.
    unfold tagall.
    simpl.
    autoST.
    left.
    autoST.
    right.
    autoST.
    exists ⟨x,y⟩.
    assert (⟨x,y⟩ ∈ z × z) by autoST.
    exists H1. auto.
  Qed.

  Lemma var_in_lcΓ : forall {x}, x ∈ ω -> forall {y}, var x ∈ lcΓ y.
  Proof.
    intros.
    unfold var.
    unfold lcΓ.
    unfold tagall.
    autoST.
    right.
    autoST.
  Qed.
  
  Lemma lfp_lcΓ : lcΓ (lfp lcΓ) ≡ lfp lcΓ.
  Proof.
    unfold lfp.
    apply equiv_ext.
    split; intros.
    unfold lcΓ.
    unfold lcΓ in H at 1.
    unfold tagall in *.
    autoST.
    exists (ϵ_iter lcΓ (Suc x1)).
    autoST.
    exists (Suc x1). eauto with zf.
    exists (lcΓ (ϵ_iter lcΓ x1)).
    autoST.
    exists x1. eauto with zf.
    apply lam_in_lcΓ.
    auto.
    destruct (has_meet x4 x5).
    destruct H. destruct H0.
    pose (in_ϵ_iter_sup H2 H3).
    pose (in_ϵ_iter_sup H1 H0).
    exists (ϵ_iter lcΓ (Suc x2)). autoST.
    exists (Suc x2). eauto with zf.
    exists (lcΓ (ϵ_iter lcΓ x2)). autoST.
    exists x2. eauto with zf.
    apply app_in_lcΓ; auto.
    exists (ϵ_iter lcΓ (∅+>∅)).
    autoST.
    exists (∅+>∅). eauto with zf.
    exists (lcΓ (ϵ_iter lcΓ ∅)).
    autoST. exists ∅. eauto with zf.
    apply var_in_lcΓ; auto.
    autoST.
    rewrite ϵ_iter_prop in H0.
    autoST.
    unfold lcΓ in H0 at 1.
    unfold tagall in H0.
    autoST.
    apply lam_in_lcΓ.
    autoST.
    exists (ϵ_iter lcΓ x2).
    autoST.
    exists x2. apply in_in_ω_in_ω in x3; auto.
    eauto.
    rewrite ϵ_iter_prop in x4.
    autoST.
    exists (lcΓ (ϵ_iter lcΓ x5)).
    autoST.
    apply in_in_ω_in_ω in x3 as ?; auto.
    apply app_in_lcΓ.
    autoST.
    exists (ϵ_iter lcΓ x2).
    autoST.
    eauto.
    rewrite ϵ_iter_prop in H.
    autoST.
    exists (lcΓ (ϵ_iter lcΓ x6)).
    autoST.
    autoST.
    exists (ϵ_iter lcΓ x2).
    autoST.
    rewrite ϵ_iter_prop in H0.
    autoST.
    exists (lcΓ (ϵ_iter lcΓ x6)).
    autoST.
    apply var_in_lcΓ.
    auto.
  Qed.

  Definition terms := lfp lcΓ.

  Notation "'for' x , .. , y ∈ X , Z" :=
    (⋃ (@replacement X (fun x _ => .. (⋃ (@replacement X (fun y _ => Z))) ..)))
      (at level 200, x closed binder, y closed binder).
  Notation "'given' P , Z" := (⋃ (selection (fun _ => P) (Z+>∅))) (at level 200, P at level 200).
  
  Definition liftΓ X :=
    (for x, y ∈ ω, given y ∈ x, ⟨⟨x,var y⟩,var y⟩+>∅)
      ∪ (for x, y ∈ ω, given x ⊆ y, ⟨⟨x,var y⟩,var (Suc y)⟩+>∅)
      ∪ (for f, a, f', a' ∈ terms, for x ∈ ω,
         given ⟨⟨x,f⟩,f'⟩ ∈ X,
         given ⟨⟨x,a⟩,a'⟩ ∈ X,
         ⟨⟨x,app f a⟩,app f' a'⟩+>∅)
      ∪ (for b, b' ∈ terms, for x ∈ ω,
         given ⟨⟨Suc x,b⟩,b'⟩ ∈ X,
         ⟨⟨x,lam b⟩,lam b'⟩+>∅).

  Definition lift := lfp liftΓ.

  Definition lowerΓ X :=
    (for i, v ∈ ω, given v ∈ i, ⟨⟨i,var v⟩,var v⟩+>∅)
      ∪ (for i, v ∈ ω, given i ⊆ (Suc v), ⟨⟨i,var (Suc v)⟩,var v⟩+>∅)
      ∪ (for f, a, f', a' ∈ terms, for i ∈ ω,
         given ⟨⟨i,f⟩,f'⟩ ∈ X,
         given ⟨⟨i,a⟩,a'⟩ ∈ X,
         ⟨⟨i,app f a⟩,app f' a'⟩+>∅)
      ∪ (for b, b' ∈ terms, for i ∈ ω,
         given ⟨⟨Suc i,b⟩,b'⟩ ∈ X,
         ⟨⟨i,lam b⟩,lam b'⟩+>∅).

  Definition lower := lfp lowerΓ.
  
  Definition substΓ X :=
    (for v ∈ ω, for st ∈ terms, ⟨⟨⟨v,st⟩,var v⟩,st⟩+>∅)
      ∪ (for i, v ∈ ω, for st ∈ terms, given i <> v,
         ⟨⟨⟨i,st⟩,var v⟩,var v⟩+>∅)
      ∪ (for i ∈ ω, for st, f, f', a, a' ∈ terms,
         given ⟨⟨⟨i,st⟩,f⟩,f'⟩ ∈ X,
         given ⟨⟨⟨i,st⟩,a⟩,a'⟩ ∈ X,
         ⟨⟨⟨i,st⟩,app f a⟩,app f' a'⟩+>∅)
      ∪ (for i ∈ ω, for st, st', b, b' ∈ terms,
         given ⟨⟨∅,st⟩,st'⟩ ∈ lift,
         given ⟨⟨⟨Suc i,st'⟩,b⟩,b'⟩ ∈ X,
         ⟨⟨⟨i,st⟩,lam b⟩,lam b'⟩+>∅).

  Definition subst := lfp substΓ.

  (* CBN WHNF evaluation *)
  Definition evalΓ X :=
    (for b ∈ terms, ⟨lam b,lam b⟩+>∅)
      ∪ (for f, a, b, sb, lb, vb ∈ terms,
         given ⟨f,lam b⟩ ∈ X,
         given ⟨⟨⟨∅,a⟩,b⟩,sb⟩ ∈ subst,
         given ⟨⟨∅,sb⟩,lb⟩ ∈ lower,
         given ⟨lb,vb⟩ ∈ X,
         ⟨app f a,vb⟩+>∅).

  Definition eval := lfp evalΓ.

  Definition id := lam (var ∅).

  Lemma var_term : forall {x}, x ∈ ω -> var x ∈ terms.
  Proof.
    intros.
    unfold terms.
    rewrite <- lfp_lcΓ.
    apply var_in_lcΓ; auto.
  Qed.
  
  Lemma lam_term : forall {x}, x ∈ terms -> lam x ∈ terms.
  Proof.
    intros.
    unfold terms.
    rewrite <- lfp_lcΓ.
    apply lam_in_lcΓ.
    auto.
  Qed.

  Lemma app_term : forall {x y}, x ∈ terms -> y ∈ terms -> app x y ∈ terms.
  Proof.
    intros.
    unfold terms.
    rewrite <- lfp_lcΓ.
    apply app_in_lcΓ; auto.
  Qed.

  Lemma id_evals_id : ⟨id,id⟩ ∈ ϵ_iter evalΓ (Suc ∅).
  Proof.
    autoST.
    exists (evalΓ (ϵ_iter evalΓ ∅)).
    autoST.
    exists ∅. eauto with zf.
    unfold evalΓ at 1.
    autoST.
    left.
    autoST.
    exists (⟨id,id⟩+>∅).
    autoST.
    exists (var ∅).
    assert (var ∅ ∈ terms).
    apply var_term.
    eauto with zf.
    exists H. auto.
  Qed.

  Lemma id_subst : ⟨⟨⟨∅,id⟩,var ∅⟩,id⟩ ∈ subst.
  Proof.
    unfold subst.
    unfold lfp.
    autoST.
    exists (ϵ_iter substΓ (∅+>∅)).
    autoST.
    exists (∅+>∅). eauto with zf.
    exists (substΓ (ϵ_iter substΓ ∅)).
    autoST.
    exists ∅. eauto with zf.
    unfold substΓ.
    autoST. left.
    autoST. left.
    autoST. left.
    autoST.
    exists (for st ∈ terms, ⟨⟨⟨∅,st⟩,var ∅⟩,st⟩ +> ∅).
    autoST. exists ∅. eauto with zf.
    exists (⟨⟨⟨∅,id⟩,var ∅⟩,id⟩+>∅).
    autoST.
    exists id.
    assert (id ∈ terms).
    apply lam_term.
    apply var_term.
    eauto with zf.
    exists H. auto.
  Qed.
  
  Lemma id_lower : ⟨⟨∅,id⟩,id⟩ ∈ lower.
  Proof.
    unfold lower.
    unfold lfp.
    autoST.
    exists (ϵ_iter lowerΓ (Suc (Suc ∅))).
    autoST.
    exists (Suc (Suc ∅)). eauto with zf.
    exists (lowerΓ (ϵ_iter lowerΓ (Suc ∅))).
    autoST.
    exists (Suc ∅). eauto with zf.
    unfold lowerΓ.
    autoST.
    right.
    autoST.
    exists (for b' ∈ terms, for i ∈ ω,
       given ⟨⟨Suc i,var ∅⟩,b'⟩ ∈ ϵ_iter lowerΓ (Suc ∅),
       ⟨⟨i,id⟩,lam b'⟩ +> ∅).
    autoST.
    exists (var ∅). assert (var ∅ ∈ terms).
    apply var_term.
    eauto with zf.
    exists H. autoST.
    exists (for i ∈ ω, given ⟨⟨Suc i,var ∅⟩,var ∅⟩ ∈ ϵ_iter lowerΓ (Suc ∅), ⟨⟨i,id⟩,id⟩+>∅).
    autoST.
    exists (var ∅). assert (var ∅ ∈ terms).
    apply var_term.
    auto with zf.
    exists H. auto.
    exists (given ⟨⟨Suc ∅,var ∅⟩,var ∅⟩ ∈ ϵ_iter lowerΓ (Suc ∅), ⟨⟨∅,id⟩,id⟩+>∅).
    autoST.
    exists ∅. eauto with zf.
    exists (⟨⟨∅,id⟩,id⟩+>∅).
    autoST.
    exists (lowerΓ (ϵ_iter lowerΓ ∅)).
    autoST.
    exists ∅. eauto with zf.
    unfold lowerΓ at 1.
    autoST. left.
    autoST. left.
    autoST. left.
    autoST.
    exists (for v ∈ ω, given v ∈ Suc ∅, ⟨⟨Suc ∅,var v⟩,var v⟩ +> ∅).
    autoST.
    exists (Suc ∅). eauto with zf.
    exists (given ∅ ∈ Suc ∅, ⟨⟨Suc ∅,var ∅⟩,var ∅⟩ +> ∅).
    autoST.
    exists ∅. eauto with zf.
    exists (⟨⟨Suc ∅,var ∅⟩,var ∅⟩+>∅).
    autoST.
    eauto with zf.
  Qed.

  Lemma app_id_id_evals_id : ⟨app id id,id⟩ ∈ eval.
  Proof.
    unfold eval.
    unfold lfp.
    autoST.
    exists (ϵ_iter evalΓ (Suc (Suc ∅))).
    autoST.
    exists (Suc (Suc ∅)).
    eauto with zf.
    exists (evalΓ (ϵ_iter evalΓ (Suc ∅))).
    autoST.
    exists (Suc ∅). eauto with zf.
    unfold evalΓ at 1.
    autoST.
    right.
    autoST.
    exists (for a, b, sb, lb, vb ∈ terms,
       given ⟨id,lam b⟩ ∈ ϵ_iter evalΓ (Suc ∅),
       given ⟨⟨⟨∅,a⟩,b⟩,sb⟩ ∈ subst,
       given ⟨⟨∅,sb⟩,lb⟩ ∈ lower,
       given ⟨lb,vb⟩ ∈ ϵ_iter evalΓ (Suc ∅),
       ⟨app id a,vb⟩+>∅).
    autoST.
    exists id. assert (id ∈ terms) by (apply lam_term; apply var_term; eauto with zf).
    eauto.
    exists (for b, sb, lb, vb ∈ terms,
       given ⟨id,lam b⟩ ∈ ϵ_iter evalΓ (Suc ∅),
       given ⟨⟨⟨∅,id⟩,b⟩,sb⟩ ∈ subst,
       given ⟨⟨∅,sb⟩,lb⟩ ∈ lower,
       given ⟨lb,vb⟩ ∈ ϵ_iter evalΓ (Suc ∅),
       ⟨app id id,vb⟩+>∅).
    autoST.
    exists id. assert (id ∈ terms) by (apply lam_term; apply var_term; eauto with zf).
    eauto.
    exists (for sb, lb, vb ∈ terms,
       given ⟨id,id⟩ ∈ ϵ_iter evalΓ (Suc ∅),
       given ⟨⟨⟨∅,id⟩,var ∅⟩,sb⟩ ∈ subst,
       given ⟨⟨∅,sb⟩,lb⟩ ∈ lower,
       given ⟨lb,vb⟩ ∈ ϵ_iter evalΓ (Suc ∅),
       ⟨app id id,vb⟩+>∅).
    autoST.
    exists (var ∅). assert (var ∅ ∈ terms) by (apply var_term; eauto with zf); eauto.
    exists (for lb, vb ∈ terms,
       given ⟨id,id⟩ ∈ ϵ_iter evalΓ (Suc ∅),
       given ⟨⟨⟨∅,id⟩,var ∅⟩,id⟩ ∈ subst,
       given ⟨⟨∅,id⟩,lb⟩ ∈ lower,
       given ⟨lb,vb⟩ ∈ ϵ_iter evalΓ (Suc ∅),
       ⟨app id id,vb⟩+>∅).
    autoST. exists id. assert (id ∈ terms) by (apply lam_term; apply var_term; eauto with zf); eauto.
    exists (for vb ∈ terms,
       given ⟨id,id⟩ ∈ ϵ_iter evalΓ (Suc ∅),
       given ⟨⟨⟨∅,id⟩,var ∅⟩,id⟩ ∈ subst,
       given ⟨⟨∅,id⟩,id⟩ ∈ lower,
       given ⟨id,vb⟩ ∈ ϵ_iter evalΓ (Suc ∅),
       ⟨app id id,vb⟩+>∅).
    autoST. exists id. assert (id ∈ terms) by (apply lam_term; apply var_term; eauto with zf); eauto.
    exists (given ⟨id,id⟩ ∈ ϵ_iter evalΓ (Suc ∅),
       given ⟨⟨⟨∅,id⟩,var ∅⟩,id⟩ ∈ subst,
       given ⟨⟨∅,id⟩,id⟩ ∈ lower,
       given ⟨id,id⟩ ∈ ϵ_iter evalΓ (Suc ∅),
       ⟨app id id,id⟩+>∅).
    autoST. exists id. assert (id ∈ terms) by (apply lam_term; apply var_term; eauto with zf); eauto.
    exists (given ⟨⟨⟨∅,id⟩,var ∅⟩,id⟩ ∈ subst,
       given ⟨⟨∅,id⟩,id⟩ ∈ lower,
       given ⟨id,id⟩ ∈ ϵ_iter evalΓ (Suc ∅),
       ⟨app id id,id⟩+>∅).
    split. apply selection_propG.
    split. autoST.
    exact id_evals_id.
    autoST.
    exists (given ⟨⟨∅,id⟩,id⟩ ∈ lower,
       given ⟨id,id⟩ ∈ ϵ_iter evalΓ (Suc ∅),
       ⟨app id id,id⟩+>∅).
    split. apply selection_propG.
    split. autoST.
    exact id_subst.
    autoST.
    exists (given ⟨id,id⟩ ∈ ϵ_iter evalΓ (Suc ∅),
       ⟨app id id,id⟩+>∅).
    split. apply selection_propG.
    split. autoST.
    exact id_lower.
    autoST.
    exists (⟨app id id, id⟩ +> ∅).
    split. apply selection_propG.
    split. autoST.
    exact id_evals_id.
    autoST.
  Qed.

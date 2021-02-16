Declare Scope zf_scope.

Reserved Notation "x '∧' y" (at level 90).

Module zf.

Open Scope zf_scope.
  
Inductive set : Type :=
| mk : forall a, (a -> set) -> set.

Notation "x '∧' y" := (prod x y) (at level 90) : zf_scope.

Fixpoint equiv (x y: set) : Prop :=
match x, y with
| mk a f, mk b g =>
  (forall x, exists y, equiv (f x) (g y)) ∧ (forall y, exists x, equiv (f x) (g y))
end.

Notation "x '≡' y" := (equiv x y) (at level 70) : zf_scope.

Lemma equiv_trans : forall {x y: set}, x ≡ y -> forall {z: set}, y ≡ z -> x ≡ z.
Proof.
induction x.
intros.
destruct z. destruct y.
destruct H0. destruct H1.
split; intro.
destruct (e x).
destruct (e1 x0).
exists x1. exact (H _ _ H0 _ H1).
destruct (e2 y).
destruct (e0 x).
exists x0. exact (H _ _ H1 _ H0).
Qed.

Lemma equiv_sym : forall {x y: set}, x ≡ y -> y ≡ x.
Proof.
induction x.
destruct y.
destruct 1.
split; intro.
destruct (e0 x).
exists x0. exact (H _ _ H0).
destruct (e y).
exists x. exact (H _ _ H0).
Qed.

Lemma equiv_refl : forall {x: set}, x ≡ x.
Proof.
  induction x.
  split; intro.
  exists x. exact (H x).
  exists y. exact (H y).
Qed.

Hint Resolve equiv_refl : zf.
Hint Resolve equiv_sym : zf.
Hint Resolve equiv_trans : zf.

Definition member (x y: set) :=
match y with
| mk a f => exists i, f i ≡ x
end.

Notation "x '∈' y" := (member x y) (at level 70) : zf_scope.

Definition subset (x y: set) :=
  match x,y with
  | mk a f, mk b g => forall x, exists y, f x ≡ g y
  end.

Notation "x '⊆' y" := (subset x y) (at level 70) : zf_scope.

Lemma mutual_subset : forall {x y}, x ⊆ y -> y ⊆ x -> x ≡ y.
Proof.
  intros [a f] [b g].
  intros.
  split.
  exact H.
  intro.
  destruct (H0 y).
  exists x. auto with zf.
Qed.

Hint Resolve mutual_subset : zf.

Definition prop_resp_equiv (P: set -> Prop) := forall x, P x -> forall y, x ≡ y -> P y.

Definition comprehension (P: set -> Prop) (x: set) :=
  match x with
  | mk a s => mk {x | P (s x)} (fun p => let (x,_) := p in s x)
  end.

Lemma comp_subset : forall P x, comprehension P x ⊆ x.
Proof.
  destruct x. intro.
  destruct x.
  exists x. eauto with zf.
Qed.

Definition comp_member_satisfies_pred : forall P, prop_resp_equiv P -> forall x y, y ∈ comprehension P x -> P y.
Proof.
  destruct x. destruct y.
  destruct 1. destruct x.
  exact (H _ p _ H0).
Defined.

Lemma elem_subset : forall {x y}, x ∈ y -> forall {z}, y ⊆ z -> x ∈ z.
Proof.
  destruct x. destruct y. destruct z.
  intro. simpl in *.
  destruct H.
  destruct (H0 x).
  exists x0. apply equiv_sym in H1. exact (equiv_trans H1 H).
Qed.

Hint Resolve elem_subset : zf.

Definition empty_set : set := mk False (False_rect set).

Notation "∅" := empty_set : zf_scope.

Notation "x ∉ y" := (x ∈ y -> False) (at level 70) : zf_scope.

Lemma empty : forall x, x ∉ ∅.
Proof.
  destruct x. unfold empty_set.
  intros. destruct H.
  contradiction.
Qed.

Hint Resolve empty : zf.

Definition nonempty (s: set) := exists y, y ∈ s.

Definition induction
           (P: set -> Prop) (H: prop_resp_equiv P)
           (H0: forall x, (forall y, y ∈ x -> P y) -> P x)
           (s: set) : P s.
Proof.
  induction s. apply (H0 (mk a s)). intros.
  destruct H2. apply (H _ (H1 x) y H2).
Defined.

Definition index (x: set) := let (a,_) := x in a.

Definition union (s: set) : set.
Proof.
  destruct s. simple refine (mk {x & index (s x)} _).
  intros [x i]. destruct (s x). exact (s0 i).
Defined.

Definition indexor (s: set) : index s -> set :=
  match s return (index s -> set) with
  | mk _ f => f
  end.

Lemma member_substs_left : forall {s a b}, a ≡ b -> a ∈ s -> b ∈ s.
Proof.
  intros [s fs] [a fa] [b fb] [H H0] [x H1]. exists x.
  destruct (fs x). destruct H1. split; intros.
  destruct (e x0). destruct (H x1).
  exists x2. eauto with zf.
  destruct (H0 y). destruct (e0 x0).
  exists x1. eauto with zf.
Qed.

Hint Resolve member_substs_left : zf.

Lemma member_substs_right : forall {s a b}, a ≡ b -> s ∈ a -> s ∈ b.
Proof.
  intros [s fs] [a fa] [b fb] [H H0] [x H1].
  destruct (H x). exists x0. destruct (fb x0).
  destruct (fa x). destruct H1. destruct H2.
  split; intros.
  destruct (e2 x1). destruct (e x2).
  exists x3. eauto with zf.
  destruct (e0 y). destruct (e1 x1).
  exists x2. eauto with zf.
Qed.

Hint Resolve member_substs_right : zf.

Lemma exists_index : forall {x y}, x ∈ y -> exists (i: index y), x ≡ indexor y i.
Proof.
  destruct x. destruct y. destruct 1.
  exists x. eauto with zf.
Qed.

Lemma in_member_union : forall {x y}, x ∈ y -> forall z, y ∈ z -> x ∈ union z.
Proof.
  destruct z. intro. elim (exists_index H0).
  intros. cut (s x0 ≡ y).
  intro. cut (x ∈ s x0). intro.
  elim (exists_index H3). intros.
  exists (existT _ x0 x1). eauto with zf.
  eauto with zf.
  eauto with zf.
Qed.

Hint Resolve in_member_union : zf.

Definition fun_resp_equiv (A: set) (f: forall x, x ∈ A -> set) := forall x y (p: x ∈ A) (p0: y ∈ A), x ≡ y -> f x p ≡ f y p0.

Definition replacement {s} (f: forall x, x ∈ s -> set) : set.
Proof.
  destruct s.
  simple refine (mk a (fun i => f (s i) _)).
  exists i. eauto with zf.
Defined.
  
Lemma image_in_replacement : forall {s} {f: forall x, x ∈ s -> set}, fun_resp_equiv s f -> forall x (p: x ∈ s), f x p ∈ replacement f.
Proof.
  destruct s. intros.
  destruct p.
  exists x0. eauto with zf.
Qed.

Hint Resolve image_in_replacement : zf.

Lemma image_has_inverse : forall {s f z}, z ∈ replacement f -> exists x (p: x ∈ s), f x p ≡ z.
Proof.
  destruct s. destruct z. intros.
  destruct H.
  exists (s x). exists (ex_intro (fun i => s i ≡ s x) x equiv_refl). auto.
Qed.

Hint Resolve image_has_inverse : zf.

Definition powerset (s: set) :=
match s with
| mk a f => mk (a -> Prop)
  (fun P => mk {x: a & P x}
    (fun i => let (x,_) := i in f x))
end.

Lemma subset_in_powerset : forall {x y}, x ⊆ y -> x ∈ powerset y.
Proof.
  intros. destruct x. destruct y.
  exists (fun i => s0 i ∈ mk a s).
  split; intros.
  destruct x.
  destruct m.
  exists x0. eauto with zf.
  destruct (H y).
  simple refine (ex_intro _ (existT _ x _) _).
  exists y. auto.
  simpl. eauto with zf.
Qed.

Hint Resolve subset_in_powerset : zf.

Definition insert (e: set) (s: set) :=
match s with
| mk a f => mk (True + a) (fun i =>
  match i with
  | inl _ => e
  | inr i => f i
  end)
end.

Definition Suc s := insert s s.

Fixpoint fin n :=
  match n with
  | S n => Suc (fin n)
  | Z => ∅
  end.

Definition infinity := mk nat fin.

Lemma Suc_member_infinity : forall {x}, x ∈ infinity -> Suc x ∈ infinity.
Proof.
  intros. destruct x.
  destruct H.
  exists (S x).
  cut (forall x, fin (S x) ≡ Suc (fin x)).
  cut (forall x y, x ≡ y -> Suc x ≡ Suc y).
  intros.
  pose (H2 := H1 x).
  eauto with zf.
  intros. destruct x0. destruct y.
  split; intros.
  destruct x0.
  exists (inl I). auto.
  destruct H0.
  destruct (e a2).
  exists (inr x0). auto.
  destruct y.
  exists (inl I). auto.
  destruct H0.
  destruct (e0 a2).
  exists (inr x0). auto.
  eauto with zf.
Qed.

Hint Resolve Suc_member_infinity : zf.

Lemma insert_order_irrelevant : forall {x y z}, insert x (insert y z) ≡ insert y (insert x z).
Proof.
  destruct x. destruct y. destruct z.
  split; intros.
  destruct x.
  exists (inr (inl I)). eauto with zf.
  destruct s2.
  exists (inl I). eauto with zf.
  exists (inr (inr a2)). eauto with zf.
  destruct y.
  exists (inr (inl I)). eauto with zf.
  destruct s2.
  exists (inl I). eauto with zf.
  exists (inr (inr a2)). eauto with zf.
Qed.

Hint Resolve insert_order_irrelevant : zf.

Lemma insert_subst_left : forall x y z, x ≡ y -> insert x z ≡ insert y z.
Proof.
  destruct x. destruct y. destruct z.
  split; intros.
  destruct x.
  exists (inl I). auto with zf.
  exists (inr a2). auto with zf.
  destruct y.
  exists (inl I). auto with zf.
  exists (inr a2). auto with zf.
Qed.

Hint Resolve insert_subst_left : zf.

Lemma insert_subst_right : forall x y z, x ≡ y -> insert z x ≡ insert z y.
Proof.
  destruct x. destruct y. destruct z.
  destruct 1. split; intros.
  destruct x.
  exists (inl I). auto with zf.
  destruct (e a2).
  exists (inr x). auto.
  destruct y.
  exists (inl I). auto with zf.
  destruct (e0 a2).
  exists (inr x). auto.
Qed.

Hint Resolve insert_subst_right : zf.

Lemma redundant_insert : forall x y, insert x (insert x y) ≡ insert x y.
Proof.
  destruct x. destruct y.
  split; intros.
  destruct x.
  exists (inl I). exact equiv_refl.
  destruct s1.
  exists (inl I). exact equiv_refl.
  exists (inr a1). exact equiv_refl.
  exists (inr y). destruct y; exact equiv_refl.
Qed.

Hint Resolve redundant_insert : zf.

Lemma equiv_ext : forall x y, (forall z, z ∈ x <-> z ∈ y) -> x ≡ y.
Proof.
  destruct x. destruct y.
  intro. simpl in H.
  split; intros.
  destruct (H (s x)).
  assert (exists i, s i ≡ s x).
  exists x. auto with zf.
  apply H0 in H2. destruct H2.
  exists x0. auto with zf.
  destruct (H (s0 y)).
  assert (exists i, s0 i ≡ s0 y).
  exists y. auto with zf.
  apply H1 in H2. destruct H2.
  exists x. auto with zf.
Qed.

Hint Resolve equiv_ext : zf.

Opaque equiv.
Opaque member.
Opaque subset.
Opaque comprehension.
Opaque empty.
Opaque induction.
Opaque index.
Opaque union.
Opaque indexor.
Opaque powerset.
Opaque insert.
Opaque infinity.

Definition ordered_pair (x y: set) := insert x (insert (insert x (insert y ∅)) ∅).
Notation "⟨ x , y ⟩" := (ordered_pair x y) : zf_scope.
Notation "⟨ x , .. , y , z ⟩" := (ordered_pair x .. (ordered_pair y z) ..) : zf_scope.

End zf.

Module lc_def.

Import zf.

Notation "u :- p , .. , t" := (p -> .. (t -> u) ..) (at level 100, only parsing).

Definition Vars := infinity.

Definition lambda_term (body: set) := ⟨fin 0, body⟩.
Notation "'λ' b" := (lambda_term b) (at level 60, right associativity).

Definition var_term (index: set) := ⟨fin 1, index⟩.
Notation "! n" := (var_term n) (at level 50).

Definition app_term (fn arg: set) := ⟨fin 2, fn, arg⟩.
Notation "f @ x" := (app_term f x) (at level 45, left associativity).

Section Terms.

Variable Terms : set.
  
Definition is_terms :=
  (forall v, !v ∈ Terms :- v ∈ Vars)
  ∧ (forall b, λ b ∈ Terms :- b ∈ Terms)
  ∧ (forall f x, f @ x ∈ Terms :- f ∈ Terms, x ∈ Terms).

End Terms.

Definition subst_term (term var val res: set) := ⟨term, var, val, res⟩.
Notation "term [ var ↦ val ] ~> res" := (subst_term term var val res) (at level 50).

Section Subst.

Variable Terms : set.

Variable LEQ : set.

Definition is_leq :=
  (forall x, ⟨x, x⟩ ∈ LEQ :- x ∈ Vars)
  ∧ (forall x y, ⟨x, Suc y⟩ ∈ LEQ :- ⟨x, y⟩ ∈ LEQ, x ∈ Vars, y ∈ Vars).

Variable Lift : set.

Definition is_lift :=
  (forall v u, ⟨v, !u, !(Suc u)⟩ ∈ Lift :- ⟨v, u⟩ ∈ LEQ, v ∈ Vars, u ∈ Vars)
  ∧ (forall b c v, ⟨v, λ b, λ c⟩ ∈ Lift :- ⟨Suc v, b, c⟩ ∈ Lift, v ∈ Vars, b ∈ Terms, c ∈ Terms)
  ∧ (forall f x g y v, ⟨v, f @ x, g @ y⟩ ∈ Lift :- ⟨v, f, g⟩ ∈ Lift, ⟨v, x, y⟩ ∈ Lift,
       f ∈ Terms, x ∈ Terms, g ∈ Terms, y ∈ Terms).

Variable Subst : set.

Definition is_subst :=
  (forall x v, (!x)[x ↦ v] ~> v ∈ Subst :- x ∈ Vars, v ∈ Terms)
  ∧ (forall f g a b x v, (f @ a)[x ↦ v] ~> (g @ b) ∈ Subst :- f[x ↦ v] ~> g ∈ Subst, a[x ↦ v] ~> b ∈ Subst,
       f ∈ Terms, g ∈ Terms, a ∈ Terms, b ∈ Terms, x ∈ Vars, v ∈ Terms)
  ∧ (forall b c x v v', (λ b)[x ↦ v] ~> c ∈ Subst :- b[Suc x ↦ v'] ~> c ∈ Subst, ⟨fin 0, v, v'⟩ ∈ Lift,
       b ∈ Terms, c ∈ Terms, x ∈ Terms, v ∈ Terms, v' ∈ Terms).

End Subst.

Definition evals (term res: set) := ⟨term, res⟩.
Notation "x ~> y" := (evals x y) (at level 50).

Section Evals.

Variable Terms : set.
Variable Subst : set.

Variable Evals : set.

(* Call-By-Name WHNF Evaluation *)
Definition is_evals :=
  (forall v, v ~> v ∈ Evals :- v ∈ Vars)
  ∧ (forall f b x s r, (f @ x) ~> r ∈ Evals :- f ~> (λ b) ∈ Evals, b[fin 0 ↦ x] ~> s ∈ Subst, s ~> r ∈ Evals,
       f ∈ Terms, b ∈ Terms, x ∈ Terms, s ∈ Terms, r ∈ Terms).

End Evals.

End lc_def.

Module zf_defs.

Import zf.

Definition cartesian_product (A B: set) := union (replacement (fun x (_: x ∈ A) => replacement (fun y (_: y ∈ B) => ⟨x,y⟩))).
Notation "A × B" := (cartesian_product A B) (at level 60, right associativity).

Lemma is_cartesian_product : forall A B x y, x ∈ A -> y ∈ B -> ⟨x,y⟩ ∈ A × B.
Proof.
  intros.
  unfold cartesian_product.
  assert (H1 : ⟨x,y⟩ ∈ replacement (fun y (_: y ∈ B) => ⟨x,y⟩)).
  intros.
  cut (fun_resp_equiv B (fun y _ => ⟨x,y⟩)).
  intros.
  exact (image_in_replacement H1 _ H0).
  unfold fun_resp_equiv. unfold ordered_pair.
  eauto with zf.
  assert (replacement (fun y (_: y ∈ B) => ⟨x,y⟩) ∈ replacement (fun (x0 : set) (_ : x0 ∈ A) => replacement (fun (y0 : set) (_ : y0 ∈ B) => ⟨ x0, y0 ⟩))).
  cut (fun_resp_equiv A (fun (x0 : set) (_ : x0 ∈ A) => replacement (fun (y0 : set) (_ : y0 ∈ B) => ⟨ x0, y0 ⟩))).
  intros.
  exact (image_in_replacement H2 _ H).
  unfold fun_resp_equiv. intros.
  assert (forall y, ⟨x0,y⟩ ≡ ⟨y0,y⟩).
  intro. unfold ordered_pair.
  assert (insert x0 (insert y1 ∅) ≡ insert y0 (insert y1 ∅)) by eauto with zf.
  eauto with zf.
  assert (fun_resp_equiv B (fun y _ => ⟨x0,y⟩)).
  unfold fun_resp_equiv. unfold ordered_pair.
  eauto with zf.
  assert (fun_resp_equiv B (fun y _ => ⟨y0,y⟩)).
  unfold fun_resp_equiv. unfold ordered_pair.
  eauto with zf.
  pose (H6 := image_in_replacement H4).
  pose (H7 := image_in_replacement H5).
  apply equiv_ext.
  intros; split; intros.
  apply image_has_inverse in H8.
  destruct H8. destruct H8.
  assert (⟨y0,x1⟩ ≡ z) by eauto with zf.
  apply (member_substs_left H9).
  apply (image_in_replacement H5). auto.
  apply image_has_inverse in H8.
  destruct H8. destruct H8.
  assert (⟨x0,x1⟩ ≡ z) by eauto with zf.
  apply (member_substs_left H9).
  apply (image_in_replacement H4). auto.
  eauto with zf.
Qed.

Hint Resolve is_cartesian_product : zf.

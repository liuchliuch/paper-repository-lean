import UniformBorderRank.RetainedAnchors

/-! The original tensor as a tensor with two anchor coordinates and ordinary
finite local coordinates, with one-dimensional dummy sites at the anchors. -/
noncomputable section
namespace UniformBorderRank
open Finset Module

/-- Dimensions outside the two anchor sets; anchor positions are dummy sites. -/
def anchorOutsideDim {N : ℕ} (d : Fin N → ℕ) (L R : Finset (Fin N)) (i : Fin N) : ℕ :=
  if i ∈ L ∪ R then 1 else d i

lemma anchorOutsideDim_eq {N : ℕ} (d : Fin N → ℕ) (L R : Finset (Fin N))
    (i : Fin N) (hiL : i ∉ L) (hiR : i ∉ R) :
    anchorOutsideDim d L R i = d i := by simp [anchorOutsideDim, hiL, hiR]

/-- Assemble original coordinates from the left anchor, right anchor and
remaining local coordinates. -/
def assembleAnchorIndex {N : ℕ} (d : Fin N → ℕ) (L R : Finset (Fin N))
    (a : FiniteSites.RetainedIndex d L) (b : FiniteSites.RetainedIndex d R)
    (u : FiniteSites.TensorIndex (anchorOutsideDim d L R)) : FiniteSites.TensorIndex d :=
  fun i => if hiL : i ∈ L then a ⟨i, hiL⟩ else
    if hiR : i ∈ R then b ⟨i, hiR⟩ else Fin.cast (anchorOutsideDim_eq d L R i hiL hiR) (u i)

/-- Project original coordinates to the remaining sites, using their unique
coordinate at each dummy site. -/
def outsideAnchorIndex {N : ℕ} (d : Fin N → ℕ) (L R : Finset (Fin N))
    (w : FiniteSites.TensorIndex d) : FiniteSites.TensorIndex (anchorOutsideDim d L R) :=
  fun i => if hi : i ∈ L ∪ R then Fin.cast (by simp [anchorOutsideDim, hi]) (0 : Fin 1)
    else Fin.cast (by simp [anchorOutsideDim, hi]) (w i)

@[simp] lemma assemble_outsideAnchorIndex {N : ℕ} (d : Fin N → ℕ) (L R : Finset (Fin N))
    (w : FiniteSites.TensorIndex d) :
    assembleAnchorIndex d L R (FiniteSites.restrictIndex L w) (FiniteSites.restrictIndex R w)
      (outsideAnchorIndex d L R w) = w := by
  funext i
  by_cases hiL : i ∈ L
  · simp [assembleAnchorIndex, FiniteSites.restrictIndex, hiL]
  · by_cases hiR : i ∈ R
    · simp [assembleAnchorIndex, FiniteSites.restrictIndex, hiL, hiR]
    · simp [assembleAnchorIndex, outsideAnchorIndex, hiL, hiR]

@[simp] lemma restrict_assemble_left {N : ℕ} (d : Fin N → ℕ) (L R : Finset (Fin N))
    (a : FiniteSites.RetainedIndex d L) (b : FiniteSites.RetainedIndex d R)
    (u : FiniteSites.TensorIndex (anchorOutsideDim d L R)) :
    FiniteSites.restrictIndex L (assembleAnchorIndex d L R a b u) = a := by
  funext i
  simp [FiniteSites.restrictIndex, assembleAnchorIndex, i.property]

@[simp] lemma restrict_assemble_right {N : ℕ} (d : Fin N → ℕ) (L R : Finset (Fin N))
    (hLR : Disjoint L R)
    (a : FiniteSites.RetainedIndex d L) (b : FiniteSites.RetainedIndex d R)
    (u : FiniteSites.TensorIndex (anchorOutsideDim d L R)) :
    FiniteSites.restrictIndex R (assembleAnchorIndex d L R a b u) = b := by
  funext i
  have hiL : i.val ∉ L := fun hi => (disjoint_left.mp hLR) hi i.property
  simp [FiniteSites.restrictIndex, assembleAnchorIndex, i.property, hiL]

@[simp] lemma outside_assembleAnchorIndex {N : ℕ} (d : Fin N → ℕ) (L R : Finset (Fin N))
    (a : FiniteSites.RetainedIndex d L) (b : FiniteSites.RetainedIndex d R)
    (u : FiniteSites.TensorIndex (anchorOutsideDim d L R)) :
    outsideAnchorIndex d L R (assembleAnchorIndex d L R a b u) = u := by
  funext i
  by_cases hi : i ∈ L ∪ R
  · have hd : anchorOutsideDim d L R i = 1 := by simp [anchorOutsideDim, hi]
    haveI : Subsingleton (Fin (anchorOutsideDim d L R i)) := by rw [hd]; infer_instance
    exact Subsingleton.elim _ _
  · have hiL : i ∉ L := fun h => hi (mem_union_left R h)
    have hiR : i ∉ R := fun h => hi (mem_union_right L h)
    simp [outsideAnchorIndex, assembleAnchorIndex, hi, hiL, hiR]

/-- Splitting all the original tensor coordinates into the two actual anchor
coordinate spaces and the remaining local coordinate space is a bijection. -/
def anchorIndexEquiv {N : ℕ} (d : Fin N → ℕ) (L R : Finset (Fin N))
    (hLR : Disjoint L R) : FiniteSites.TensorIndex d ≃
      FiniteSites.RetainedIndex d L × FiniteSites.RetainedIndex d R ×
        FiniteSites.TensorIndex (anchorOutsideDim d L R) where
  toFun w := (FiniteSites.restrictIndex L w, FiniteSites.restrictIndex R w, outsideAnchorIndex d L R w)
  invFun x := assembleAnchorIndex d L R x.1 x.2.1 x.2.2
  left_inv := assemble_outsideAnchorIndex d L R
  right_inv x := by
    apply Prod.ext
    · exact restrict_assemble_left d L R x.1 x.2.1 x.2.2
    · apply Prod.ext
      · exact restrict_assemble_right d L R hLR x.1 x.2.1 x.2.2
      · exact outside_assembleAnchorIndex d L R x.1 x.2.1 x.2.2

/-- The actual original tensor with two anchor coordinates. -/
def anchorTensor {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d) (L R : Finset (Fin N))
    (a : FiniteSites.RetainedIndex d L) (b : FiniteSites.RetainedIndex d R)
    (u : FiniteSites.TensorIndex (anchorOutsideDim d L R)) : ℂ :=
  T (assembleAnchorIndex d L R a b u)

/-- Contraction covectors on the remaining sites, normalized to one at the
one-dimensional dummy anchor sites. -/
def anchorOutsideBase {N : ℕ} (d : Fin N → ℕ) (L R : Finset (Fin N))
    (q : FiniteSites.Covectors d) : FiniteSites.Covectors (anchorOutsideDim d L R) :=
  fun i a => if hi : i ∈ L ∪ R then 1 else q i (Fin.cast (by simp [anchorOutsideDim, hi]) a)

private def anchorWeight {N : ℕ} (d : Fin N → ℕ) (L R : Finset (Fin N))
    (q : FiniteSites.Covectors d) (a : FiniteSites.RetainedIndex d L)
    (b : FiniteSites.RetainedIndex d R) (w : FiniteSites.TensorIndex d) : ℂ :=
  ∏ i, if hi : i ∈ L then (if w i = a ⟨i, hi⟩ then 1 else 0)
    else if hj : i ∈ R then (if w i = b ⟨i, hj⟩ then 1 else 0) else q i (w i)

private lemma anchorWeight_assemble {N : ℕ} (d : Fin N → ℕ) (L R : Finset (Fin N))
    (hLR : Disjoint L R) (q : FiniteSites.Covectors d)
    (a a' : FiniteSites.RetainedIndex d L) (b b' : FiniteSites.RetainedIndex d R)
    (u : FiniteSites.TensorIndex (anchorOutsideDim d L R)) :
    anchorWeight d L R q a b (assembleAnchorIndex d L R a' b' u) =
      (if a' = a then 1 else 0) * (if b' = b then 1 else 0) *
        ∏ i, anchorOutsideBase d L R q i (u i) := by
  classical
  by_cases hA : a' = a
  · subst a'
    by_cases hB : b' = b
    · subst b'
      simp only [ite_true, one_mul]
      apply prod_congr rfl
      intro i _
      by_cases hiL : i ∈ L
      · simp [anchorWeight, assembleAnchorIndex, anchorOutsideBase, hiL]
      · by_cases hiR : i ∈ R
        · simp [anchorWeight, assembleAnchorIndex, anchorOutsideBase, hiL, hiR]
        · simp [anchorWeight, assembleAnchorIndex, anchorOutsideBase, hiL, hiR]
    · simp only [ite_true, if_neg hB, mul_zero, zero_mul]
      obtain ⟨i, hi⟩ : ∃ i, b' i ≠ b i := by
        by_contra! h
        exact hB (funext h)
      have hiL : i.val ∉ L := fun h => (disjoint_left.mp hLR) h i.property
      apply prod_eq_zero (mem_univ i.val)
      simp [anchorWeight, assembleAnchorIndex, hiL, i.property, hi]
  · simp only [if_neg hA, zero_mul]
    obtain ⟨i, hi⟩ : ∃ i, a' i ≠ a i := by
      by_contra! h
      exact hA (funext h)
    apply prod_eq_zero (mem_univ i.val)
    simp [anchorWeight, assembleAnchorIndex, i.property, hi]

/-- The ordinary product contraction of the actual anchor tensor is precisely
the faithful core obtained from the original cut. -/
theorem anchorTensor_core_eq {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d)
    (L R : Finset (Fin N)) (hLR : Disjoint L R) (q : FiniteSites.Covectors d)
    (a : FiniteSites.RetainedIndex d L) (b : FiniteSites.RetainedIndex d R) :
    (∑ u, anchorTensor d T L R a b u * ∏ i, anchorOutsideBase d L R q i (u i)) =
      anchorContract d T L R q a b := by
  classical
  change _ = ∑ w, T w * anchorWeight d L R q a b w
  rw [← (anchorIndexEquiv d L R hLR).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  change _ = ∑ a', ∑ b', ∑ u, T (assembleAnchorIndex d L R a' b' u) *
    anchorWeight d L R q a b (assembleAnchorIndex d L R a' b' u)
  simp_rw [anchorWeight_assemble d L R hLR]
  simp [anchorTensor, mul_ite, ite_mul]

/-- An arbitrary coordinate restriction can only decrease matrix rank. -/
theorem rowSpan_finrank_reindex_le {I J I' J' : Type*} [Fintype J] [Fintype J']
    (M : I → J → ℂ) (f : I' → I) (g : J' → J) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (fun i' j' => M (f i') (g j')))) ≤
      Module.finrank ℂ (Submodule.span ℂ (Set.range M)) := by
  let l : (J → ℂ) →ₗ[ℂ] (J' → ℂ) :=
    { toFun := fun x j' => x (g j')
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hs : Submodule.span ℂ (Set.range (fun i' j' => M (f i') (g j'))) ≤
      (Submodule.span ℂ (Set.range M)).map l := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i', rfl⟩
    exact ⟨M (f i'), Submodule.subset_span ⟨f i', rfl⟩, rfl⟩
  exact (Submodule.finrank_mono hs).trans (Submodule.finrank_map_le l _)

def anchorSeparatingCut {N : ℕ} (L R S : Finset (Fin N)) : Finset (Fin N) :=
  L ∪ (S \ (L ∪ R))

private def anchorCutRow {N : ℕ} (d : Fin N → ℕ) (L R S : Finset (Fin N))
    (x : FiniteSites.RetainedIndex d L × (∀ i ∈ S, Fin (anchorOutsideDim d L R i))) :
    ∀ i ∈ anchorSeparatingCut L R S, Fin (d i) := by
  intro i hiA
  by_cases hiL : i ∈ L
  · exact x.1 ⟨i, hiL⟩
  · have hx : i ∈ S ∧ i ∉ L ∪ R := by simpa [anchorSeparatingCut, hiL] using hiA
    have hiR : i ∉ R := fun h => hx.2 (mem_union_right L h)
    exact Fin.cast (anchorOutsideDim_eq d L R i hiL hiR) (x.2 i hx.1)

private def anchorCutCol {N : ℕ} (d : Fin N → ℕ) (L R S : Finset (Fin N))
    (x : FiniteSites.RetainedIndex d R × (∀ i ∈ Sᶜ, Fin (anchorOutsideDim d L R i))) :
    ∀ i ∈ (anchorSeparatingCut L R S)ᶜ, Fin (d i) := by
  intro i hiA
  have hiA' : i ∉ anchorSeparatingCut L R S := mem_compl.mp hiA
  by_cases hiR : i ∈ R
  · exact x.1 ⟨i, hiR⟩
  · have hiL : i ∉ L := fun h => hiA' (mem_union_left _ h)
    have hiS : i ∉ S := by
      intro h
      exact hiA' (mem_union_right _ (mem_sdiff.mpr ⟨h, by simp [hiL, hiR]⟩))
    exact Fin.cast (anchorOutsideDim_eq d L R i hiL hiR) (x.2 i (mem_compl.mpr hiS))

/-- The raw matrix for a cut of the remaining local sites, always keeping
the two anchors on opposite sides. -/
def anchorTensorCut {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d) (L R S : Finset (Fin N))
    (x : FiniteSites.RetainedIndex d L × (∀ i ∈ S, Fin (anchorOutsideDim d L R i)))
    (y : FiniteSites.RetainedIndex d R × (∀ i ∈ Sᶜ, Fin (anchorOutsideDim d L R i))) : ℂ :=
  anchorTensor d T L R x.1 y.1 ((flatIndexEquiv (anchorOutsideDim d L R) S).symm (x.2, y.2))

lemma anchorTensorCut_eq_original {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d)
    (L R S : Finset (Fin N)) (hLR : Disjoint L R)
    (x : FiniteSites.RetainedIndex d L × (∀ i ∈ S, Fin (anchorOutsideDim d L R i)))
    (y : FiniteSites.RetainedIndex d R × (∀ i ∈ Sᶜ, Fin (anchorOutsideDim d L R i))) :
    anchorTensorCut d T L R S x y = flatCoeff d T (anchorSeparatingCut L R S)
      (anchorCutRow d L R S x) (anchorCutCol d L R S y) := by
  unfold anchorTensorCut anchorTensor flatCoeff
  congr 1
  funext i
  by_cases hiL : i ∈ L
  · simp [assembleAnchorIndex, anchorSeparatingCut, anchorCutRow, hiL]
  · by_cases hiR : i ∈ R
    · simp [assembleAnchorIndex, anchorSeparatingCut, anchorCutCol, hiL, hiR]
    · by_cases hiS : i ∈ S
      · simp [assembleAnchorIndex, anchorSeparatingCut, anchorCutRow, flatIndexEquiv, hiL, hiR, hiS]
      · simp [assembleAnchorIndex, anchorSeparatingCut, anchorCutCol, flatIndexEquiv, hiL, hiR, hiS]

/-- Every raw anchor block matrix inherits the actual original all-cut bound. -/
theorem anchorTensorCut_rank_le {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d)
    (L R : Finset (Fin N)) (hL : L.Nonempty) (hR : R.Nonempty)
    (hLR : Disjoint L R) (r : ℕ) (hcut : allCutLe d T r) (S : Finset (Fin N)) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (anchorTensorCut d T L R S))) ≤ r := by
  classical
  have hAne : anchorSeparatingCut L R S ≠ ∅ := by
    obtain ⟨i, hi⟩ := hL
    exact ne_empty_of_mem (mem_union_left _ hi)
  have hAuniv : anchorSeparatingCut L R S ≠ univ := by
    obtain ⟨i, hi⟩ := hR
    intro h
    have hiA : i ∈ anchorSeparatingCut L R S := h ▸ mem_univ i
    have hiL : i ∉ L := fun hj => (disjoint_left.mp hLR) hj hi
    simpa [anchorSeparatingCut, hiL, hi] using hiA
  have hm : anchorTensorCut d T L R S = fun x y =>
      flatCoeff d T (anchorSeparatingCut L R S)
        (anchorCutRow d L R S x) (anchorCutCol d L R S y) := by
    funext x y
    exact anchorTensorCut_eq_original d T L R S hLR x y
  rw [hm]
  exact (rowSpan_finrank_reindex_le (flatCoeff d T (anchorSeparatingCut L R S))
    (anchorCutRow d L R S) (anchorCutCol d L R S)).trans
    (hcut _ hAne hAuniv)

end UniformBorderRank

import Paper17.RationalHalfspaceVertices

/-! Compact rational sections of pointed homogeneous rational systems. -/
noncomputable section
open scoped BigOperators
namespace Paper17

@[simp] theorem ratVector_neg {n : ℕ} (q : Fin n → ℚ) : ratVector (-q) = -ratVector q := by
  ext j
  simp [ratVector]

@[simp] theorem ratVector_sum {n : ℕ} {J : Type*} [Fintype J] (q : J → Fin n → ℚ) :
    ratVector (∑ i, q i) = ∑ i, ratVector (q i) := by
  ext j
  simp [ratVector]

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

def rationalInequalityCone (a : ι → Fin n → ℚ) : Set (V n) :=
  {x | ∀ i, 0 ≤ dot (ratVector (a i)) x}

def rationalEvaluation (a : ι → Fin n → ℚ) : V n →ₗ[ℝ] (ι → ℝ) where
  toFun x i := dot (ratVector (a i)) x
  map_add' := by intro x y; ext i; exact dot_add_right _ _ _
  map_smul' := by intro t x; ext i; exact dot_smul_right _ _ _

def rationalSectionNormals (a : ι → Fin n → ℚ) : ι ⊕ Bool → Fin n → ℚ
  | .inl i => -a i
  | .inr false => ∑ i, a i
  | .inr true => -(∑ i, a i)

def rationalSectionHeights : ι ⊕ Bool → ℚ
  | .inl _ => 0
  | .inr false => 1
  | .inr true => -1

private theorem section_pairing (a : ι → Fin n → ℚ) (x : V n) :
    dot (ratVector (∑ i, a i)) x = ∑ i, dot (ratVector (a i)) x := by
  rw [ratVector_sum]
  simpa only [one_smul, one_mul] using dot_fintype_sum_smul (fun _ : ι => (1 : ℝ))
    (fun i => ratVector (a i)) x

/-- The actual cross-section is given by rational finite H-data. -/
theorem mem_rationalSection (a : ι → Fin n → ℚ) (x : V n) :
    x ∈ finiteHalfspaces (fun i => ratVector (rationalSectionNormals a i))
      (fun i => (rationalSectionHeights (ι := ι) i : ℝ)) ↔
    x ∈ rationalInequalityCone a ∧ ∑ i, dot (ratVector (a i)) x = 1 := by
  have hneg : ∀ v : V n, dot (-v) x = -dot v x := by
    intro v
    simpa only [neg_one_smul, neg_one_mul] using dot_smul_left (-1) v x
  constructor
  · intro hx
    refine ⟨fun i => ?_, ?_⟩
    · have hh := hx (.inl i)
      simpa only [rationalSectionNormals, ratVector_neg, hneg, rationalSectionHeights,
        Rat.cast_zero, neg_nonpos] using hh
    · have hp := hx (.inr false)
      have hm := hx (.inr true)
      simp only [rationalSectionNormals, ratVector_neg, hneg, rationalSectionHeights,
        Rat.cast_one, Rat.cast_neg, section_pairing] at hp hm
      linarith
  · rintro ⟨hx, heq⟩ i
    rcases i with i | b
    · simpa only [rationalSectionNormals, ratVector_neg, hneg, rationalSectionHeights,
        Rat.cast_zero, neg_nonpos] using hx i
    · cases b <;> simp only [rationalSectionNormals, ratVector_neg, hneg,
        rationalSectionHeights, Rat.cast_one, Rat.cast_neg, section_pairing, heq, le_refl]

/-- The section is compact because its injective evaluation map sends it into
the finite cube `[0,1]^ι`. No simplicity assumption enters this argument. -/
theorem rationalSection_isCompact (a : ι → Fin n → ℚ)
    (hk : ∀ x : V n, (∀ i, dot (ratVector (a i)) x = 0) → x = 0) :
    IsCompact (finiteHalfspaces (fun i => ratVector (rationalSectionNormals a i))
      (fun i => (rationalSectionHeights (ι := ι) i : ℝ))) := by
  let L := rationalEvaluation a
  have hker : LinearMap.ker L = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro x y hxy
    apply sub_eq_zero.mp
    apply hk
    intro i
    have hh := congrFun hxy i
    change dot (ratVector (a i)) x = dot (ratVector (a i)) y at hh
    change ∑ j, ratVector (a i) j * (x j - y j) = 0
    simp only [mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hh
  have hcompact := (LinearMap.isClosedEmbedding_of_injective hker).isCompact_preimage
    (isCompact_Icc : IsCompact (Set.Icc (0 : ι → ℝ) 1))
  apply hcompact.of_isClosed_subset (finiteHalfspaces_isClosed _ _)
  intro x hx
  obtain ⟨hx0, hx1⟩ := (mem_rationalSection a x).mp hx
  refine ⟨hx0, ?_⟩
  intro i
  change dot (ratVector (a i)) x ≤ 1
  rw [← hx1]
  exact Finset.single_le_sum (fun j _ => hx0 j) (Finset.mem_univ i)

/-- A pointed homogeneous rational system is the positive span of finitely
many rational vectors, obtained from the vertices of its compact section. -/
theorem rationalCone_finite_rational_generators (a : ι → Fin n → ℚ)
    (hk : ∀ x : V n, (∀ i, dot (ratVector (a i)) x = 0) → x = 0) :
    ∃ s : Finset (V n), (∀ x ∈ s, IsRatPoint x) ∧
      rationalInequalityCone a = raySpan (fun x : s => x.val) Finset.univ := by
  classical
  let H := finiteHalfspaces (fun i => ratVector (rationalSectionNormals a i))
    (fun i => (rationalSectionHeights (ι := ι) i : ℝ))
  obtain ⟨s, hs, hrat⟩ := rationalHalfspaces_finite_vertices
    (rationalSectionNormals a) rationalSectionHeights (rationalSection_isCompact a hk)
  have hsmem : ∀ y ∈ s, y ∈ rationalInequalityCone a := by
    intro y hy
    apply ((mem_rationalSection a y).mp _).1
    rw [hs]
    exact subset_convexHull ℝ _ hy
  refine ⟨s, hrat, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]
      exact raySpan_zero _ _
    let t : ℝ := ∑ i, dot (ratVector (a i)) x
    have ht0 : 0 ≤ t := Finset.sum_nonneg (fun i _ => hx i)
    have ht : 0 < t := by
      apply lt_of_le_of_ne ht0
      intro heq
      apply hx0
      apply hk x
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hx i)).mp heq.symm i
        (Finset.mem_univ _)
    have hy : t⁻¹ • x ∈ convexHull ℝ (s : Set (V n)) := by
      rw [← hs, mem_rationalSection]
      constructor
      · intro i
        rw [dot_smul_right]
        exact mul_nonneg (inv_nonneg.mpr ht.le) (hx i)
      · simp only [dot_smul_right, ← Finset.mul_sum]
        exact inv_mul_cancel₀ ht.ne'
    obtain ⟨w, hw, _, heq⟩ := Finset.mem_convexHull'.mp hy
    refine ⟨fun y => t * w y.val, fun y => mul_nonneg ht.le (hw y.val y.property),
      by simp, ?_⟩
    calc x = t • (t⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
      _ = t • (∑ y ∈ s, w y • y) := by rw [heq]
      _ = ∑ y : s, (t * w y.val) • y.val := by
        rw [← Finset.sum_coe_sort s (fun y => w y • y), Finset.smul_sum]
        simp only [smul_smul]
  · rintro x ⟨c, hc, _, rfl⟩ i
    rw [dot_comm, dot_fintype_sum_smul]
    exact Finset.sum_nonneg (fun y _ => mul_nonneg (hc y)
      (by rw [dot_comm]; exact hsmem y.val y.property i))

end
end Paper17

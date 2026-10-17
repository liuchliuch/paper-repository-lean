import Paper17.LatticeResolution
import Paper17.Delzant

/-!
# Subdivision and resolution of one simplicial lattice cone

The generators and all cone containments in this file are actual subsets of
`V n`. The single stellar step replaces each generator having a positive
coefficient in the chosen lattice point. Determinant descent then terminates
and gives a finite cover by unimodular cones. Compatibility between different
initial cones and projective realization are separate obligations.
-/

noncomputable section
open scoped BigOperators
namespace Paper17

/-- Nonnegative real span of the rows of an integral square matrix. -/
def latticeCone {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Set (V n) :=
  {x | ∃ c : Fin n → ℝ, (∀ i, 0 ≤ c i) ∧
    ∀ j, x j = ∑ i, c i * (A i j : ℝ)}

/-- Replacing a row by a nonnegative combination produces a subcone. -/
theorem latticeCone_updateRow_subset {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (u : Fin n → ℤ) (b : Fin n → ℝ)
    (hb : ∀ i, 0 ≤ b i)
    (hu : ∀ j, (u j : ℝ) = ∑ i, b i * (A i j : ℝ)) (k : Fin n) :
    latticeCone (A.updateRow k u) ⊆ latticeCone A := by
  rintro x ⟨c, hc, hx⟩
  refine ⟨fun i => (if i = k then 0 else c i) + c k * b i, ?_, ?_⟩
  · intro i
    exact add_nonneg (by split_ifs; exact le_refl 0; exact hc i) (mul_nonneg (hc k) (hb i))
  · intro j
    rw [hx j]
    have hleft : ∑ i, c i * ((A.updateRow k u) i j : ℝ) =
        c k * (u j : ℝ) + ∑ i ∈ Finset.univ.erase k, c i * (A i j : ℝ) := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k)]
      congr 1
      · simp
      · apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_erase] at hi
        simp [Matrix.updateRow, hi.1]
    have hright : ∑ i, ((if i = k then 0 else c i) + c k * b i) * (A i j : ℝ) =
        (∑ i ∈ Finset.univ.erase k, c i * (A i j : ℝ)) +
          c k * ∑ i, b i * (A i j : ℝ) := by
      simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
      congr 1
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k)]
      simp only [ite_true, zero_mul, zero_add]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_erase] at hi
      simp [hi.1]
    rw [hleft, hright, ← hu j, add_comm]

/-- Every point in a simplicial cone belongs to one of the cones in a stellar
subdivision at a nonzero nonnegative combination of its generators. -/
theorem latticeCone_stellar_cover {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (u : Fin n → ℤ) (b : Fin n → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hbpos : ∃ i, 0 < b i)
    (hu : ∀ j, (u j : ℝ) = ∑ i, b i * (A i j : ℝ)) :
    latticeCone A = ⋃ k : {i // 0 < b i}, latticeCone (A.updateRow k.1 u) := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨c, hc, hx⟩
    let S : Finset (Fin n) := Finset.univ.filter (fun i => 0 < b i)
    have hS : S.Nonempty := by
      obtain ⟨i, hi⟩ := hbpos
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image S (fun i => c i / b i) hS
    have hbk : 0 < b k := (Finset.mem_filter.mp hk).2
    let t := c k / b k
    have ht : 0 ≤ t := div_nonneg (hc k) hbk.le
    have hres : ∀ i, 0 ≤ c i - t * b i := by
      intro i
      by_cases hi : 0 < b i
      · have hle := hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
        exact sub_nonneg.mpr ((le_div_iff₀ hi).mp hle)
      · have hz : b i = 0 := le_antisymm (le_of_not_gt hi) (hb i)
        simp [hz, hc i]
    apply Set.mem_iUnion.mpr
    refine ⟨⟨k, hbk⟩, fun i => if i = k then t else c i - t * b i, ?_, ?_⟩
    · intro i
      dsimp only
      split_ifs
      · exact ht
      · exact hres i
    · intro j
      have heq : ∑ i, (if i = k then t else c i - t * b i) *
          ((A.updateRow k u) i j : ℝ) =
          t * (u j : ℝ) + ∑ i, (c i - t * b i) * (A i j : ℝ) := by
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k)]
        have hz : c k - t * b k = 0 := by dsimp [t]; field_simp; ring
        rw [← Finset.add_sum_erase Finset.univ
          (fun i => (c i - t * b i) * (A i j : ℝ)) (Finset.mem_univ k)]
        simp only [ite_true, Matrix.updateRow_self, hz, zero_mul, zero_add]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        have hik : i ≠ k := (Finset.mem_erase.mp hi).1
        simp [hik, Matrix.updateRow]
      rw [heq, hu j, hx j]
      simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
      ring
  · intro x hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    exact latticeCone_updateRow_subset A u b hb hu k.1 hk

/-- A full-dimensional integral simplicial cone is the union of finitely many
unimodular integral simplicial cones, each contained in the original cone.
This assertion does not assert compatibility with any other initial cone. -/
theorem exists_unimodular_cone_cover {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det ≠ 0) :
    ∃ S : Finset (Matrix (Fin n) (Fin n) ℤ),
      (∀ B ∈ S, B.det.natAbs = 1 ∧ latticeCone B ⊆ latticeCone A) ∧
      latticeCone A = ⋃ B ∈ S, latticeCone B := by
  classical
  suffices ∀ d : ℕ, ∀ A : Matrix (Fin n) (Fin n) ℤ,
      A.det.natAbs = d → A.det ≠ 0 →
      ∃ S : Finset (Matrix (Fin n) (Fin n) ℤ),
        (∀ B ∈ S, B.det.natAbs = 1 ∧ latticeCone B ⊆ latticeCone A) ∧
        latticeCone A = ⋃ B ∈ S, latticeCone B from
    this _ A rfl hA
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro A hdet hA
    by_cases hd : d = 1
    · refine ⟨{A}, ?_, ?_⟩
      · intro B hB
        have heq : B = A := Finset.mem_singleton.mp hB
        subst B
        exact ⟨hdet.trans hd, Set.Subset.rfl⟩
      · simp
    · have hdpos : 0 < d := by
        rw [← hdet]
        exact Int.natAbs_pos.mpr hA
      have hdlarge : 1 < A.det.natAbs := by omega
      obtain ⟨u, hu0, b, hb, hu⟩ := exists_nonzero_parallelepiped_point A hdlarge
      have hbpos : ∃ i, 0 < b i := by
        by_contra hn
        push_neg at hn
        have hz : ∀ i, b i = 0 := fun i => le_antisymm (hn i) (hb i).1
        apply hu0
        ext j
        simpa [hz] using hu j
      let I := {i : Fin n // 0 < b i}
      have hstep : ∀ k : I, 0 < (A.updateRow k.1 u).det.natAbs ∧
          (A.updateRow k.1 u).det.natAbs < d := by
        intro k
        simpa only [hdet] using multiplicity_strictly_decreases A u b hu hA k.1 k.2 (hb k.1).2
      have hrec : ∀ k : I, ∃ S : Finset (Matrix (Fin n) (Fin n) ℤ),
          (∀ B ∈ S, B.det.natAbs = 1 ∧ latticeCone B ⊆ latticeCone (A.updateRow k.1 u)) ∧
          latticeCone (A.updateRow k.1 u) = ⋃ B ∈ S, latticeCone B := by
        intro k
        exact ih _ (hstep k).2 _ rfl (Int.natAbs_ne_zero.mp (hstep k).1.ne')
      choose S hS hcover using hrec
      refine ⟨Finset.univ.biUnion S, ?_, ?_⟩
      · intro B hB
        obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hB
        exact ⟨(hS k B hk).1, (hS k B hk).2.trans
          (latticeCone_updateRow_subset A u b (fun i => (hb i).1) hu k.1)⟩
      · rw [latticeCone_stellar_cover A u b (fun i => (hb i).1) hbpos hu]
        ext x
        simp only [Set.mem_iUnion, Finset.mem_biUnion, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨k, hk⟩
          rw [hcover k] at hk
          obtain ⟨B, hB⟩ := Set.mem_iUnion.mp hk
          obtain ⟨hB, hxB⟩ := Set.mem_iUnion.mp hB
          exact ⟨B, ⟨k, hB⟩, hxB⟩
        · rintro ⟨B, ⟨k, hB⟩, hxB⟩
          exact ⟨k, by rw [hcover k]; exact Set.mem_iUnion.mpr ⟨B, Set.mem_iUnion.mpr ⟨hB, hxB⟩⟩⟩

/-- The positive span is an actual convex cone in the geometric model. -/
def latticeConeObject {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Cone n where
  carrier := latticeCone A
  convex' := by
    rw [convex_iff_add_mem]
    rintro x ⟨c, hc, hx⟩ y ⟨d, hd, hy⟩ a b ha hb _
    refine ⟨fun i => a * c i + b * d i, fun i =>
      add_nonneg (mul_nonneg ha (hc i)) (mul_nonneg hb (hd i)), ?_⟩
    intro j
    change a * x j + b * y j = _
    rw [hx j, hy j]
    simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  smul_mem' := by
    rintro x a ⟨c, hc, hx⟩ ha
    refine ⟨fun i => a * c i, fun i => mul_nonneg ha (hc i), ?_⟩
    intro j
    change a * x j = _
    rw [hx j]
    simp only [mul_assoc, ← Finset.mul_sum]
  zero_mem' := ⟨0, by simp, by simp⟩

/-- A unimodular integral generator matrix gives genuine smoothness of its
positive span, including equality with the generated cone. -/
theorem latticeConeObject_isSmooth {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det.natAbs = 1) :
    Fan.IsSmoothCone (latticeConeObject A) := by
  refine ⟨fun i j => (A i j : ℝ), fun i j => ⟨A i j, rfl⟩, ?_, ?_⟩
  · have hcast : ((A.det.natAbs : ℕ) : ℝ) = 1 := by exact_mod_cast hA
    simpa only [Int.cast_natAbs, Int.cast_abs, Int.cast_det] using hcast
  · ext x
    change (∃ c : Fin n → ℝ, (∀ i, 0 ≤ c i) ∧
      ∀ j, x j = ∑ i, c i * (A i j : ℝ)) ↔ _
    constructor
    · rintro ⟨c, hc, hx⟩
      refine ⟨c, hc, ?_⟩
      ext j
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hx j
    · rintro ⟨c, hc, hx⟩
      refine ⟨c, hc, fun j => ?_⟩
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hx j

/-- A geometric version of the finite unimodular cover theorem. -/
theorem exists_smooth_cone_cover {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det ≠ 0) :
    ∃ S : Finset (Cone n),
      (∀ C ∈ S, Fan.IsSmoothCone C ∧ (C : Set (V n)) ⊆ latticeCone A) ∧
      latticeCone A = ⋃ C ∈ S, (C : Set (V n)) := by
  classical
  obtain ⟨T, hT, hcover⟩ := exists_unimodular_cone_cover A hA
  refine ⟨T.image latticeConeObject, ?_, ?_⟩
  · intro C hC
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hC
    exact ⟨latticeConeObject_isSmooth B (hT B hB).1, (hT B hB).2⟩
  · rw [hcover]
    ext x
    simp only [Set.mem_iUnion, Finset.mem_image]
    constructor
    · rintro ⟨B, hB, hxB⟩
      exact ⟨latticeConeObject B, ⟨B, hB, rfl⟩, hxB⟩
    · rintro ⟨C, ⟨B, hB, rfl⟩, hxB⟩
      exact ⟨B, hB, hxB⟩

end Paper17

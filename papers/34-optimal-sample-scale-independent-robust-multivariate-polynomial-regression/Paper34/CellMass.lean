import Paper34.Model
import Paper34.GridGeometry
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Actual measures of the closed Chebyshev cells

The uniform and Chebyshev laws in this file are exactly the measures defined in
`Paper34.Model`. In particular, the Chebyshev law is its angular pushforward.
-/

open Set MeasureTheory
open scoped BigOperators

namespace Paper34

noncomputable section

/-- The length of a coordinate interval under normalized uniform measure. -/
def normalizedCellWidth {n m : ℕ} (j : CellIndex n m) (k : Fin n) : ℝ :=
  (cellUpper j k - cellLower j k) / 2

lemma cell_raw_width_nonneg {n m : ℕ} (hm : 0 < m) (j : CellIndex n m) (k : Fin n) :
    0 ≤ cellUpper j k - cellLower j k := by
  obtain ⟨x, hx⟩ := closedCell_nonempty hm j
  exact sub_nonneg.mpr ((hx.1 k).trans (hx.2 k))

lemma normalizedCellWidth_nonneg {n m : ℕ} (hm : 0 < m) (j : CellIndex n m) (k : Fin n) :
    0 ≤ normalizedCellWidth j k :=
  div_nonneg (cell_raw_width_nonneg hm j k) (by norm_num)

lemma normalizedCellWidth_lower_bound {n m : ℕ} (hm : 0 < m)
    (j : CellIndex n m) (k : Fin n) :
    (m : ℝ)⁻¹ ^ 2 ≤ normalizedCellWidth j k := by
  simpa [normalizedCellWidth, cellUpper, cellLower] using
    ChebyshevCounterexample.uniform_cell_width_lower_bound m (by omega) (j k)

/-- The actual normalized uniform mass is the product of coordinate widths. -/
theorem uniformLaw_closedCell {n m : ℕ} (hm : 0 < m) (j : CellIndex n m) :
    uniformLaw n (closedCell j) = ∏ k : Fin n, ENNReal.ofReal (normalizedCellWidth j k) := by
  have hcell : MeasurableSet (closedCell j) := measurableSet_Icc
  rw [uniformLaw, Measure.smul_apply, Measure.restrict_apply hcell,
    inter_eq_left.mpr (closedCell_subset_cube j)]
  change (ENNReal.ofReal ((2 : ℝ) ^ n))⁻¹ * volume (closedCell j) = _
  rw [closedCell, Real.volume_Icc_pi]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun k _ => cell_raw_width_nonneg hm j k)]
  rw [← ENNReal.ofReal_inv_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) n)]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹)]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun k _ => normalizedCellWidth_nonneg hm j k)]
  congr 1
  simp only [normalizedCellWidth, div_eq_mul_inv]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [inv_pow]
  ring

/-- The actual uniform cell probability is at least `m^(-2n)`, as in (6.4). -/
theorem uniformLaw_closedCell_lower_bound {n m : ℕ} (hm : 0 < m) (j : CellIndex n m) :
    ENNReal.ofReal ((m : ℝ)⁻¹ ^ (2 * n)) ≤ uniformLaw n (closedCell j) := by
  rw [uniformLaw_closedCell hm j]
  calc
    ENNReal.ofReal ((m : ℝ)⁻¹ ^ (2 * n)) =
        (ENNReal.ofReal ((m : ℝ)⁻¹ ^ 2)) ^ n := by
      rw [pow_mul, ENNReal.ofReal_pow (sq_nonneg _)]
    _ = ∏ _k : Fin n, ENNReal.ofReal ((m : ℝ)⁻¹ ^ 2) := by simp
    _ ≤ ∏ k : Fin n, ENNReal.ofReal (normalizedCellWidth j k) := by
      exact Finset.prod_le_prod' (fun k _ => ENNReal.ofReal_le_ofReal
        (normalizedCellWidth_lower_bound hm j k))


/-- Lower angular endpoint, before applying the decreasing cosine map. -/
def angularCellLower {n m : ℕ} (j : CellIndex n m) (k : Fin n) : ℝ :=
  (j k : ℕ) * Real.pi / m

/-- Upper angular endpoint. -/
def angularCellUpper {n m : ℕ} (j : CellIndex n m) (k : Fin n) : ℝ :=
  ((j k : ℕ) + (1 : ℝ)) * Real.pi / m

/-- The actual angular box whose cosine image is the source cell. -/
def angularCell {n m : ℕ} (j : CellIndex n m) : Set (Point n) :=
  Icc (angularCellLower j) (angularCellUpper j)

lemma angularCellLower_nonneg {n m : ℕ} (j : CellIndex n m) (k : Fin n) :
    0 ≤ angularCellLower j k := by
  unfold angularCellLower
  positivity

lemma angularCellLower_le_upper {n m : ℕ} (j : CellIndex n m) (k : Fin n) :
    angularCellLower j k ≤ angularCellUpper j k := by
  unfold angularCellLower angularCellUpper
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
  nlinarith [Real.pi_pos]

lemma angularCellUpper_le_pi {n m : ℕ} (hm : 0 < m)
    (j : CellIndex n m) (k : Fin n) : angularCellUpper j k ≤ Real.pi := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hj : (j k : ℝ) + 1 ≤ m := by exact_mod_cast (Nat.succ_le_iff.mpr (j k).isLt)
  unfold angularCellUpper
  apply (div_le_iff₀ hm').2
  nlinarith [mul_le_mul_of_nonneg_right hj Real.pi_pos.le]

lemma angularCell_subset_box {n m : ℕ} (hm : 0 < m) (j : CellIndex n m) :
    angularCell j ⊆ Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => Real.pi) := by
  intro theta htheta
  exact ⟨fun k => (angularCellLower_nonneg j k).trans (htheta.1 k),
    fun k => (htheta.2 k).trans (angularCellUpper_le_pi hm j k)⟩

lemma cos_mem_closedCell_iff {n m : ℕ} (hm : 0 < m) (j : CellIndex n m)
    (theta : Point n)
    (htheta : theta ∈ Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => Real.pi)) :
    (fun k => Real.cos (theta k)) ∈ closedCell j ↔ theta ∈ angularCell j := by
  have hlo (k : Fin n) : angularCellLower j k ∈ Icc (0 : ℝ) Real.pi :=
    ⟨angularCellLower_nonneg j k,
      (angularCellLower_le_upper j k).trans (angularCellUpper_le_pi hm j k)⟩
  have hhi (k : Fin n) : angularCellUpper j k ∈ Icc (0 : ℝ) Real.pi :=
    ⟨(angularCellLower_nonneg j k).trans (angularCellLower_le_upper j k),
      angularCellUpper_le_pi hm j k⟩
  constructor
  · intro h
    constructor
    · intro k
      exact (Real.strictAntiOn_cos.le_iff_ge ⟨htheta.1 k, htheta.2 k⟩ (hlo k)).mp (h.2 k)
    · intro k
      exact (Real.strictAntiOn_cos.le_iff_ge (hhi k) ⟨htheta.1 k, htheta.2 k⟩).mp (h.1 k)
  · intro h
    constructor
    · intro k
      exact (Real.strictAntiOn_cos.le_iff_ge (hhi k) ⟨htheta.1 k, htheta.2 k⟩).mpr (h.2 k)
    · intro k
      exact (Real.strictAntiOn_cos.le_iff_ge ⟨htheta.1 k, htheta.2 k⟩ (hlo k)).mpr (h.1 k)

/-- The restricted preimage equality needed by the actual pushforward measure. -/
lemma cos_preimage_closedCell_inter_box {n m : ℕ} (hm : 0 < m) (j : CellIndex n m) :
    ((fun theta : Point n => fun k => Real.cos (theta k)) ⁻¹' closedCell j) ∩
      Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => Real.pi) = angularCell j := by
  ext theta
  constructor
  · rintro ⟨hcos, hbox⟩
    exact (cos_mem_closedCell_iff hm j theta hbox).mp hcos
  · intro h
    have hbox := angularCell_subset_box hm j h
    exact ⟨(cos_mem_closedCell_iff hm j theta hbox).mpr h, hbox⟩

lemma angularCell_width {n m : ℕ} (j : CellIndex n m) (k : Fin n) :
    angularCellUpper j k - angularCellLower j k = Real.pi / m := by
  unfold angularCellUpper angularCellLower
  ring

/-- The actual angular-pushforward Chebyshev law gives each closed cell mass
`m^(-n)`, as in (6.2). Boundary points have zero angular volume automatically. -/
theorem chebyshevLaw_closedCell {n m : ℕ} (hm : 0 < m) (j : CellIndex n m) :
    chebyshevLaw n (closedCell j) = ENNReal.ofReal ((m : ℝ)⁻¹ ^ n) := by
  have hcos : Continuous (fun theta : Point n => fun k => Real.cos (theta k)) :=
    continuous_pi (fun k => Real.continuous_cos.comp (continuous_apply k))
  have hcell : MeasurableSet (closedCell j) := measurableSet_Icc
  rw [chebyshevLaw, Measure.map_apply hcos.measurable hcell, angularLaw,
    Measure.smul_apply, Measure.restrict_apply (hcell.preimage hcos.measurable),
    cos_preimage_closedCell_inter_box hm j]
  change (ENNReal.ofReal (Real.pi ^ n))⁻¹ * volume (angularCell j) = _
  rw [angularCell, Real.volume_Icc_pi]
  simp_rw [angularCell_width]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ Real.pi / m) n,
    ← ENNReal.ofReal_inv_of_pos (pow_pos Real.pi_pos n),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (Real.pi ^ n)⁻¹)]
  congr 1
  rw [div_eq_mul_inv, mul_pow, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero n Real.pi_pos.ne'), one_mul]


/-- Every actual uniform cell has strictly positive probability. -/
lemma uniformLaw_closedCell_pos {n m : ℕ} (hm : 0 < m) (j : CellIndex n m) :
    0 < uniformLaw n (closedCell j) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hpos : (0 : ENNReal) < ENNReal.ofReal ((m : ℝ)⁻¹ ^ (2 * n)) := by positivity
  exact hpos.trans_le (uniformLaw_closedCell_lower_bound hm j)

/-- Every actual Chebyshev cell has strictly positive probability. -/
lemma chebyshevLaw_closedCell_pos {n m : ℕ} (hm : 0 < m) (j : CellIndex n m) :
    0 < chebyshevLaw n (closedCell j) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [chebyshevLaw_closedCell hm j]
  positivity


/-- Normalization of the actual uniform law on the source cube. -/
lemma uniformLaw_univ (n : ℕ) : uniformLaw n Set.univ = 1 := by
  have hvolume : volume (cube n) = ENNReal.ofReal ((2 : ℝ) ^ n) := by
    norm_num [cube, Real.volume_Icc_pi, ENNReal.ofReal_pow]
  rw [uniformLaw, Measure.smul_apply, Measure.restrict_apply_univ, hvolume]
  change (ENNReal.ofReal ((2 : ℝ) ^ n))⁻¹ * ENNReal.ofReal ((2 : ℝ) ^ n) = 1
  exact ENNReal.inv_mul_cancel (by positivity) (by simp)

instance uniformLaw_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (uniformLaw n) where
  measure_univ := uniformLaw_univ n

/-- Normalization of the actual uniform angular law. -/
lemma angularLaw_univ (n : ℕ) : angularLaw n Set.univ = 1 := by
  have hvolume : volume (Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => Real.pi)) =
      ENNReal.ofReal (Real.pi ^ n) := by
    simp [Real.volume_Icc_pi, ENNReal.ofReal_pow, Real.pi_pos.le]
  rw [angularLaw, Measure.smul_apply, Measure.restrict_apply_univ, hvolume]
  change (ENNReal.ofReal (Real.pi ^ n))⁻¹ * ENNReal.ofReal (Real.pi ^ n) = 1
  exact ENNReal.inv_mul_cancel (by positivity) (by simp)

instance angularLaw_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (angularLaw n) where
  measure_univ := angularLaw_univ n

/-- The source Chebyshev pushforward is a probability measure. -/
lemma chebyshevLaw_univ (n : ℕ) : chebyshevLaw n Set.univ = 1 := by
  have hcos : Continuous (fun theta : Point n => fun k => Real.cos (theta k)) :=
    continuous_pi (fun k => Real.continuous_cos.comp (continuous_apply k))
  rw [chebyshevLaw, Measure.map_apply hcos.measurable MeasurableSet.univ]
  change angularLaw n Set.univ = 1
  exact angularLaw_univ n

instance chebyshevLaw_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (chebyshevLaw n) where
  measure_univ := chebyshevLaw_univ n

end

end Paper34

import Paper29.ChainingBounds
import Mathlib.Tactic.FieldSimp

noncomputable section
open scoped BigOperators ENNReal
namespace Paper29.ProcessTools

/-- Squaring the proved Huber increment inequality costs only the factor2. -/
theorem huber_increment_sq (s t : ℝ) :
    (huber s - huber t) ^ 2 ≤ 2 * huber (s - t) * (huber s + huber t) := by
  have hi := (sq_le_sq₀ (abs_nonneg (huber s - huber t))
    (mul_nonneg (psi_nonneg (s - t)) (add_nonneg (psi_nonneg s) (psi_nonneg t)))).2
      (huber_increment s t)
  rw [sq_abs, mul_pow, psi_sq] at hi
  have hs : (psi s + psi t) ^ 2 ≤ 2 * (huber s + huber t) := by
    nlinarith [psi_sq s, psi_sq t, sq_nonneg (psi s - psi t)]
  have hm := mul_le_mul_of_nonneg_left hs (huber_nonneg (s - t))
  nlinarith only [hi, hm]

theorem huberMetric_ne_top {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (τ : Fin n → ℝ) (h k : Fin d → ℝ) : Chaining.huberMetric A τ h k ≠ ⊤ := by
  have hf : (∑ i, ENNReal.ofReal (Real.sqrt (huber ((A.mulVec (h-k)) i) / τ i))) ≠ ⊤ := by
    simp
  apply ne_top_of_le_ne_top hf
  unfold Chaining.huberMetric
  apply iSup_le
  intro i
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin n => ENNReal.ofReal (Real.sqrt (huber ((A.mulVec (h-k)) j) / τ j)))
    (fun _ _ => bot_le) (Finset.mem_univ i)

/-- The original design-only max metric dominates each coordinate increment. -/
theorem coordinate_metric_bound {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (τ : Fin n → ℝ) (hτ : ∀ i, 0 < τ i) (h k : Fin d → ℝ) (i : Fin n) :
    huber ((A.mulVec (h-k)) i) ≤
      τ i * (Chaining.huberMetric A τ h k).toReal ^ 2 := by
  have he : ENNReal.ofReal (Real.sqrt (huber ((A.mulVec (h-k)) i) / τ i)) ≤
      Chaining.huberMetric A τ h k := by
    unfold Chaining.huberMetric
    exact le_iSup (fun j : Fin n => ENNReal.ofReal (Real.sqrt (huber ((A.mulVec (h-k)) j) / τ j))) i
  have hr := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (huberMetric_ne_top A τ h k)).2 he
  rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hr
  have hs := Real.sq_sqrt (div_nonneg (huber_nonneg ((A.mulVec (h-k)) i)) (hτ i).le)
  have hD := ENNReal.toReal_nonneg (a := Chaining.huberMetric A τ h k)
  have hsq : huber ((A.mulVec (h-k)) i) / τ i ≤
      (Chaining.huberMetric A τ h k).toReal ^ 2 := by
    have hh := (sq_le_sq₀ (Real.sqrt_nonneg _) hD).2 hr
    rwa [hs] at hh
  have hh := (div_le_iff₀ (hτ i)).1 hsq
  nlinarith only [hh]

theorem importanceAverage_sum {n m : ℕ} (π : Fin n → ℝ)
    (ν : Fin m → Fin n) (f : Fin n → ℝ) :
    Sampling.importanceAverage π ν f = ∑ j, f (ν j) / ((m : ℝ) * π (ν j)) := by
  simp only [Sampling.importanceAverage, Finset.sum_div, div_div]
  simp only [mul_comm]

/-- The coefficient class for centered affine increments. -/
def shiftedClass {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (z : Fin n → ℝ)
    (i : Fin n) (h : Fin d → ℝ) : ℝ := huber (z i + (A.mulVec h) i) - huber (z i)

/-- The key comparison in Lemma3.6, derived from actual shifted Huber values.
The shift z cancels from the design-only metric on the right. -/
theorem shifted_metric_sq {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (z τ π : Fin n → ℝ) (T : ℝ) (hτ : ∀ i, 0 < τ i)
    (hπ : ∀ i, 0 < π i) (hm : 0 < m) (hrel : ∀ i, τ i = T * π i)
    (ν : Fin m → Fin n) (h k : Fin d → ℝ) :
    (∑ j, ((shiftedClass A z (ν j) h - shiftedClass A z (ν j) k) /
      ((m : ℝ) * π (ν j))) ^ 2) ≤
      (2 * T / m) * (Chaining.huberMetric A τ h k).toReal ^ 2 *
        (Sampling.sampledShifted π ν A z h + Sampling.sampledShifted π ν A z k) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let D : ℝ := (Chaining.huberMetric A τ h k).toReal
  have hterm (j : Fin m) :
      ((shiftedClass A z (ν j) h - shiftedClass A z (ν j) k) /
          ((m : ℝ) * π (ν j))) ^ 2 ≤
        ((2 * T / m) * D ^ 2) *
          ((huber (z (ν j) + (A.mulVec h) (ν j)) +
            huber (z (ν j) + (A.mulVec k) (ν j))) / ((m : ℝ) * π (ν j))) := by
    let i := ν j
    have hi := huber_increment_sq (z i + (A.mulVec h) i) (z i + (A.mulVec k) i)
    have he : z i + (A.mulVec h) i - (z i + (A.mulVec k) i) = (A.mulVec (h-k)) i := by
      rw [Matrix.mulVec_sub]
      simp only [Pi.sub_apply]
      ring
    rw [he] at hi
    have hb := mul_le_mul_of_nonneg_right (coordinate_metric_bound A τ hτ h k i)
      (show 0 ≤ huber (z i + (A.mulVec h) i) + huber (z i + (A.mulVec k) i) by exact add_nonneg (huber_nonneg _) (huber_nonneg _))
    have hh : (huber (z i + (A.mulVec h) i) - huber (z i + (A.mulVec k) i)) ^ 2 ≤
        2 * (T * π i) * D ^ 2 *
          (huber (z i + (A.mulVec h) i) + huber (z i + (A.mulVec k) i)) := by
      rw [hrel i] at hb
      dsimp [D]
      nlinarith only [hi, hb]
    have hd := div_le_div_of_nonneg_right hh (sq_nonneg ((m : ℝ) * π i))
    have hc : shiftedClass A z i h - shiftedClass A z i k =
        huber (z i + (A.mulVec h) i) - huber (z i + (A.mulVec k) i) := by
      unfold shiftedClass
      ring
    dsimp only [i] at *
    rw [hc, div_pow]
    convert hd using 1 <;> field_simp [ne_of_gt hmR, ne_of_gt (hπ (ν j))] <;> ring
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hterm j)
  rw [← Finset.mul_sum] at hs
  simpa only [Sampling.sampledShifted, Sampling.sampledHuber,
    importanceAverage_sum, add_div, Finset.sum_add_distrib, D] using hs

end Paper29.ProcessTools

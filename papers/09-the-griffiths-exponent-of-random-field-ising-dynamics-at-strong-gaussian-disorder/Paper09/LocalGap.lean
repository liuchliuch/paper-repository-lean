import Paper09.LatticeGeometry
import Paper09.CanonicalPath
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators Classical Real

noncomputable section
namespace Paper09

/-- Absorb the canonical path length into a surface exponential, uniformly
for all positive integer volumes. -/
theorem canonical_denominator_le_surface_exp {a D β q : ℝ}
    (ha : 0 < a) (hD : 0 ≤ D) (hβ : 0 ≤ β) (hq : 1 ≤ q) :
    2 * q * exp (2 * β * (D * q ^ a)) ≤
      exp ((2 + 1 / a + 2 * β * D) * q ^ a) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqa : 1 ≤ q ^ a := one_le_rpow hq ha.le
  have hlogq : log q ≤ q ^ a / a := log_le_rpow_div hq0.le ha
  have hlog2 : log 2 ≤ 1 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog : log (2 * q * exp (2 * β * (D * q ^ a))) ≤
      (2 + 1 / a + 2 * β * D) * q ^ a := by
    rw [log_mul (by positivity : 2 * q ≠ 0) (exp_ne_zero _),
      log_mul (by norm_num : (2 : ℝ) ≠ 0) hq0.ne', log_exp]
    calc
      log 2 + log q + 2 * β * (D * q ^ a) ≤
          1 + q ^ a / a + 2 * β * (D * q ^ a) := by linarith
      _ ≤ (2 + 1 / a + 2 * β * D) * q ^ a := by
        rw [div_eq_mul_inv, one_div]
        nlinarith
  exact (log_le_iff_le_exp (by positivity)).mp hlog

/-- Appendix A.2, in the actual finite lattice geometry and rate-one
normalization. The constant depends only on dimension and inverse temperature;
all finite fields and all fixed boundaries are uniform. -/
theorem lemma_A_2_local_gap (d : ℕ) (β : ℝ) (hd : 2 ≤ d) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset (LatticeGeometry.Point d)), A.Nonempty →
      ∀ (Λ : Lattice ↥A),
      (∀ x y : ↥A, Λ.adj x y ↔ LatticeGeometry.Adj x.val y.val) →
      ∀ (h : ↥A → ℝ) (S : Finset ↥A) (φ : ↥A → Spin),
      C⁻¹ * exp (-C * (A.card : ℝ) ^ exponentA d) ≤
        spectralGap (gibbs Λ h β univ S φ) := by
  let a := exponentA d
  let D := LatticeGeometry.cutwidthConstant d
  let C := 2 + 1 / a + 2 * β * D
  have ha : 0 < a := exponentA_pos hd
  have hD : 0 ≤ D := (LatticeGeometry.cutwidthConstant_bounds hd).1
  have hC1 : 1 ≤ C := by
    have hi : 0 ≤ 1 / a := by positivity
    have hp : 0 ≤ 2 * β * D := by positivity
    dsimp [C]
    linarith
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  refine ⟨C, hC, ?_⟩
  intro A hA Λ hΛ h S φ
  obtain ⟨order, hwidth⟩ := LatticeGeometry.exists_ordering_cutwidth hd A Λ hΛ
  have hq : 0 < A.card := card_pos.mpr hA
  have hq1 : (1 : ℝ) ≤ A.card := by exact_mod_cast hq
  have hden := canonical_denominator_le_surface_exp ha hD hβ.le hq1
  have hbase : exp (-C * (A.card : ℝ) ^ a) ≤
      1 / (2 * (A.card : ℝ) * exp (2 * β * (D * (A.card : ℝ) ^ a))) := by
    rw [neg_mul, exp_neg]
    simpa only [one_div, C] using one_div_le_one_div_of_le (by positivity) hden
  have hsmall : C⁻¹ * exp (-C * (A.card : ℝ) ^ a) ≤
      exp (-C * (A.card : ℝ) ^ a) := by
    apply mul_le_of_le_one_left (exp_nonneg _)
    exact (inv_le_one₀ hC).mpr hC1
  exact hsmall.trans (hbase.trans
    (CanonicalPath.gap_lower_bound Λ h β hβ.le S φ hq order
      (D * (A.card : ℝ) ^ a) hwidth))

end Paper09

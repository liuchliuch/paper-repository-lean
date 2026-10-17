import ELV.RayVectors
import ELV.HilbertSeparable
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Normed

/-! The full complex tensor Fock witnesses of (4.7)--(4.9), constructed as
actual square summable vectors in the Hilbert sum of finite tensor powers. -/
noncomputable section
open scoped ENNReal
namespace ELV.Fock
variable {d : ℕ}

abbrev PowerSpace (d k : ℕ) := EuclideanSpace ℂ (Fin k → Fin d)
abbrev Space (d : ℕ) := lp (fun k : ℕ => PowerSpace d k) 2

def tensorPower (c : EuclideanSpace ℂ (Fin d)) (k : ℕ) : PowerSpace d k :=
  WithLp.toLp 2 (fun w => ∏ j : Fin k, c (w j))

theorem tensorPower_inner (c e : EuclideanSpace ℂ (Fin d)) (k : ℕ) :
    inner ℂ (tensorPower c k) (tensorPower e k) = (inner ℂ c e) ^ k := by
  change (∑ w : Fin k → Fin d, inner ℂ (∏ j : Fin k, c (w j)) (∏ j : Fin k, e (w j))) = _
  simp only [RCLike.inner_apply, map_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.sum_pow (fun i : Fin d => e i * starRingEnd ℂ (c i)) k).symm

theorem tensorPower_norm_sq (c : EuclideanSpace ℂ (Fin d)) (k : ℕ) :
    ‖tensorPower c k‖ ^ 2 = (‖c‖ ^ 2) ^ k := by
  have hi := tensorPower_inner c c k
  have hr := congrArg Complex.re hi
  simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using hr

/-- The actual Fock vector; square summability is proved from its geometric norm series. -/
def eta (c : EuclideanSpace ℂ (Fin d)) (hc : ‖c‖ ^ 2 < 1) : Space d :=
  ⟨tensorPower c, by
    apply memℓp_gen
    simpa [Real.rpow_two, tensorPower_norm_sq] using
      summable_geometric_of_lt_one (sq_nonneg ‖c‖) hc⟩

theorem eta_inner (c e : EuclideanSpace ℂ (Fin d))
    (hc : ‖c‖ ^ 2 < 1) (he : ‖e‖ ^ 2 < 1) :
    inner ℂ (eta c hc) (eta e he) = 1 / (1 - inner ℂ c e) := by
  rw [lp.inner_eq_tsum]
  change (∑' k, inner ℂ (tensorPower c k) (tensorPower e k)) = _
  simp_rw [tensorPower_inner]
  have hc1 : ‖c‖ < 1 := by nlinarith [norm_nonneg c]
  have he1 : ‖e‖ < 1 := by nlinarith [norm_nonneg e]
  have hce : ‖inner ℂ c e‖ < 1 :=
    (norm_inner_le_norm c e).trans_lt
      ((mul_le_mul_of_nonneg_left he1.le (norm_nonneg c)).trans_lt (by simpa using hc1))
  simpa [one_div] using (tsum_geometric_of_norm_lt_one hce)

/-- Equation (4.8), as a norm of a concrete Hilbert-space vector. -/
theorem eta_norm_sq (c : EuclideanSpace ℂ (Fin d)) (hc : ‖c‖ ^ 2 < 1) :
    ‖eta c hc‖ ^ 2 = 1 / (1 - ‖c‖ ^ 2) := by
  have hn : ‖eta c hc‖ ^ 2 = ∑' k, ‖tensorPower c k‖ ^ 2 := by
    simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (eta c hc)
  rw [hn]
  simp_rw [tensorPower_norm_sq]
  simpa [one_div] using tsum_geometric_of_lt_one (sq_nonneg ‖c‖) hc

instance space_separable (d : ℕ) : TopologicalSpace.SeparableSpace (Space d) :=
  Query.lp_separable

end ELV.Fock

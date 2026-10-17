import Paper37.KnownSupportRisk
import Paper37.RenewalModel

/-! The H.1 finite-vector calculation specialized to the paper's genuine
finite-mean renewal law with a known support bound. -/
noncomputable section
namespace Paper37.KnownSupportLaw
open scoped BigOperators
open Paper37.Renewal Paper37.Compression Paper37.Compression.Distribution
open Paper37.KnownSupportRisk Paper37.IIDAddOne

def vector (μ : Law) (B : ℕ) (hS : ∀ d, B ≤ d → μ.mass d=0) : Distribution (Fin B) where
  mass j := μ.mass j.val
  nonneg j := μ.nonneg j.val
  total := by
    rw [Fin.sum_univ_eq_sum_range]
    have hh : (∑' d, μ.mass d) = ∑ d ∈ Finset.range B, μ.mass d := by
      apply tsum_eq_sum
      intro d hd
      exact hS d (by simpa only [Finset.mem_range,not_lt] using hd)
    rw [← hh]
    exact μ.total.tsum_eq

lemma vector_mean (μ : Law) (B : ℕ) (hS : ∀ d, B ≤ d → μ.mass d=0) :
    finiteMean (vector μ B hS) = mean μ := by
  rw [finiteMean]
  change (∑ j : Fin B, ((j.val:ℝ)+1)*μ.mass j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun d : ℕ => ((d:ℝ)+1)*μ.mass d) B]
  symm
  apply tsum_eq_sum
  intro d hd
  rw [hS d (by simpa only [Finset.mem_range,not_lt] using hd),mul_zero]

lemma vector_survival (μ : Law) (B : ℕ) (hS : ∀ d, B ≤ d → μ.mass d=0) (a : ℕ) :
    Paper37.HazardChain.survival (vector μ B hS) a = tail μ a := by
  rw [survival_eq_sum]
  change (∑ j : Fin B, if a ≤ j.val then μ.mass j.val else 0) = _
  rw [Fin.sum_univ_eq_sum_range (fun d : ℕ => if a ≤ d then μ.mass d else 0) B]
  symm
  apply tsum_eq_sum
  intro d hd
  have hh := hS d (by simpa only [Finset.mem_range,not_lt] using hd)
  split_ifs <;> simp [hh]

/-- H.1 on its exact equilibrium-age × iid-backward-gap product law, for every
original finite-mean renewal law supported on {1,...,B}. The mean in the bound
is the source law's actual infinite-series mean. -/
theorem product_risk_bounds (μ : Law) {n B : ℕ} [Nonempty (Fin B)]
    (hS : ∀ d, B ≤ d → μ.mass d=0) (hB : 1 ≤ B) (hBn : 2*B ≤ n) :
    let p := vector μ B hS
    let k := n/B-1
    let R := ∑ s, iidLaw p k s * ∑ a, (tail μ a.val/mean μ) *
      Paper37.Boundary.klReal (μ.mass a.val/tail μ a.val) (estimatedHazard k s a)
    R ≤ ((B:ℝ)-1)/(mean μ*(n/B:ℕ)) ∧
      R ≤ (B:ℝ)*((B:ℝ)-1)/(mean μ*((n:ℝ)-B)) ∧
      R ≤ 2*(B:ℝ)^2/(mean μ*n) ∧ R ≤ 2*(B:ℝ)^2/n := by
  have h := product_hazard_risk_bounds (vector μ B hS) hB hBn
  dsimp only [ageLaw,trueHazard] at h
  simp only [vector_survival,vector_mean] at h
  exact h

end Paper37.KnownSupportLaw

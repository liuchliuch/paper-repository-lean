import Paper29.LongCompressedError
import Paper29.HardAverage
import Paper29.LowerBudgetAlgebra

noncomputable section
open scoped BigOperators ENNReal Classical
open MeasureTheory
namespace Paper29.HardDistribution
open Transcript QueryModel

/-- Complete long-block adaptive lower bound for arbitrary measurable private
seeds, actual real responses, and infinite cost on nonreturning runs. -/
theorem long_lower_bound {Ω : Type} [MeasurableSpace Ω] [Nonempty Ω]
    {n d r : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hr : 1 ≤ r) (hrd : r ≤ d) (hN : 160 ≤ n/r)
    (ε : ℝ) (hε : 0 < ε) (hεhi : ε ≤ 1/800)
    (p : QueryModel.Policy Ω n d) (hp : Correct μ p (longDesign n d r (n/r)) ε) :
    ENNReal.ofReal (lowerBudget n r (1/1280000) ε) ≤
      ⨆ b : Fin n → ℝ, ∫⁻ ω,QueryModel.queryCount p ω b ∂μ := by
  let N := n/r
  have hN0 : 0 < N := by dsimp [N]; omega
  have hblocks : r*N ≤ n := by dsimp [N]; simpa only [Nat.mul_comm] using Nat.div_mul_le_self n r
  let β := beta ε N
  obtain ⟨hβ,hβε,hβhi,hscale⟩ := beta_bounds ε N hε hεhi hN
  let label : Bool → ℝ := fun b => 4*bit b
  let code := compilePolicy hrd label p
  let q := ProcessTools.seedCodeMass μ code
  have hq := ProcessTools.seedCodeMass_nonneg μ code
  have hsq := ProcessTools.seedCodeMass_total μ code (measurable_compilePolicy hrd label p hp.2.1)
  let rep := ProcessTools.seedRepresentative code
  let policy := representativePolicy rep label p hp.1
  let decoder := representativeDecoder rep label p hrd n
  let P := hardSeedLaw (r:=r) (N:=N) q hq hsq β hβ.le (hβhi.trans (by norm_num))
  let Q := expectedQueries P policy (fun ω => ω.2.2) (fun ω => poolBits hblocks ω.2.1) n
  have he := long_compressed_hamming_lt μ hr hN0 hrd hblocks ε β hε.le (by linarith)
    hβ hβhi hscale hβε p hp
  have hi := hard_pool_query_lower hN0 hblocks q hq hsq β hβ.le hβhi policy decoder he
  change RateDistortion.cRD*r ≤ 16*β^2*Q at hi
  have hbudget := long_inverse_budget n r hr hN hε
  change (1/40000:ℝ)*min (n:ℝ) ((r:ℝ)/ε^2) ≤ (r:ℝ)/β^2 at hbudget
  have hhalf : (1/2:ℝ) ≤ RateDistortion.cRD := by linarith [RateDistortion.cRD_gt]
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have h32 : (r:ℝ)/β^2 ≤ 32*Q := by
    apply (div_le_iff₀ (sq_pos_of_pos hβ)).2
    have hh := mul_le_mul_of_nonneg_right hhalf hr0
    nlinarith
  have hB : lowerBudget n r (1/1280000) ε ≤ Q := by
    unfold lowerBudget
    linarith
  have havg := compressed_hard_cost_le μ hrd hblocks p hp.1 hp.2.1 β hβ.le (hβhi.trans (by norm_num))
  exact (ENNReal.ofReal_le_ofReal hB).trans havg

end Paper29.HardDistribution

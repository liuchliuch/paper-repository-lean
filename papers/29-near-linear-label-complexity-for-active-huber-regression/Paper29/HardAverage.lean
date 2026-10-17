import Paper29.FiniteWeightedAverage
import Paper29.CompressedSuccess
import Paper29.PoolResponse

noncomputable section
set_option maxHeartbeats 300000
open scoped BigOperators ENNReal Classical
open MeasureTheory
namespace Paper29.HardDistribution
open Transcript QueryModel

theorem hardSeedLaw_sum {E : Type} [Fintype E] {r N : ℕ}
    (q : E → ℝ) (hq : ∀ e,0 ≤ q e) (hsq : ∑ e,q e=1)
    (β : ℝ) (hβ : 0 ≤ β) (hβhi : β ≤ 1/2) (f : Signs r × (Bits r N × E) → ℝ) :
    (∑ ω,(hardSeedLaw q hq hsq β hβ hβhi).weight ω*f ω) =
      ∑ sy : Signs r × Bits r N,hardMass β sy.1 sy.2*(∑ e,q e*f (sy.1,(sy.2,e))) := by
  simp only [Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro e _
  change hardMass β s y*q e*f (s,(y,e)) = hardMass β s y*(q e*f (s,(y,e)))
  ring

/-- The distributional normalized query cost is bounded by the exact official
worst-response expected query cost of the arbitrary original seed algorithm. -/
theorem compressed_hard_cost_le {Ω : Type} [MeasurableSpace Ω] [Nonempty Ω]
    {n d r N : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (hrd : r ≤ d) (hblocks : r*N ≤ n)
    (p : QueryModel.Policy Ω n d) (hfresh : Fresh p) (hp : ∀ h,Measurable (fun ω => p ω h))
    (β : ℝ) (hβ : 0 ≤ β) (hβhi : β ≤ 1/2) :
    let code := compilePolicy hrd (fun b => 4*bit b) p
    let q := ProcessTools.seedCodeMass μ code
    let rep := ProcessTools.seedRepresentative code
    let policy := representativePolicy rep (fun b => 4*bit b) p hfresh
    let P := hardSeedLaw (r:=r) (N:=N) q (ProcessTools.seedCodeMass_nonneg μ code)
      (ProcessTools.seedCodeMass_total μ code (measurable_compilePolicy hrd (fun b => 4*bit b) p hp)) β hβ hβhi
    ENNReal.ofReal (expectedQueries P policy (fun ω => ω.2.2) (fun ω => poolBits hblocks ω.2.1) n) ≤
      ⨆ b : Fin n → ℝ, ∫⁻ ω,QueryModel.queryCount p ω b ∂μ := by
  let label : Bool → ℝ := fun b => 4*bit b
  let code := compilePolicy hrd label p
  let q := ProcessTools.seedCodeMass μ code
  have hq := ProcessTools.seedCodeMass_nonneg μ code
  have hsq := ProcessTools.seedCodeMass_total μ code (measurable_compilePolicy hrd label p hp)
  let rep := ProcessTools.seedRepresentative code
  let policy := representativePolicy rep label p hfresh
  change ENNReal.ofReal (expectedQueries (hardSeedLaw q hq hsq β hβ hβhi) policy
    (fun ω => ω.2.2) (fun ω => poolBits hblocks ω.2.1) n) ≤ _
  rw [expectedQueries,hardSeedLaw_sum]
  have hM (sy : Signs r × Bits r N) :=
    (compressed_expected_queries_le μ hrd label p hfresh hp (poolBits hblocks sy.2)).trans
      (le_iSup (fun b : Fin n → ℝ => ∫⁻ ω,QueryModel.queryCount p ω b ∂μ)
        (fun i => label (poolBits hblocks sy.2 i)))
  have hout := ProcessTools.ofReal_weighted_average_le (fun sy : Signs r × Bits r N => hardMass β sy.1 sy.2)
    (fun sy => hardMass_nonneg β hβ hβhi sy.1 sy.2)
    (by rw [Fintype.sum_prod_type]; exact hardMass_total β) q hq
    (fun sy e => Transcript.queryCount policy e (poolBits hblocks sy.2) n)
    (fun sy e => Transcript.queryCount_nonneg policy e (poolBits hblocks sy.2) n)
    (⨆ b : Fin n → ℝ, ∫⁻ ω,QueryModel.queryCount p ω b ∂μ) (by
      intro sy
      dsimp only [policy,rep,q,code]
      have hh := hM sy
      exact hh)
  exact hout

end Paper29.HardDistribution

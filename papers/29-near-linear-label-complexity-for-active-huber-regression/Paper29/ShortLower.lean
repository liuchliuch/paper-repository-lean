import Paper29.ShortCompression
import Paper29.FiniteQueryLower

noncomputable section
open scoped BigOperators ENNReal Classical
open MeasureTheory
namespace Paper29.HardDistribution
open Transcript QueryModel

/-- Complete short-block lower bound, including arbitrary measurable private
seeds and the actual padded pool. -/
theorem short_lower_bound {Ω : Type} [MeasurableSpace Ω] [Nonempty Ω]
    {n d r : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hr : 1 ≤ r) (hrn : r ≤ n) (hrd : r ≤ d) (hN : n/r < 160)
    (ε : ℝ) (p : QueryModel.Policy Ω n d) (hp : Correct μ p (shortDesign n d r) ε) :
    ENNReal.ofReal (lowerBudget n r (1/1280000) ε) ≤
      ⨆ b : Fin n → ℝ, ∫⁻ ω,QueryModel.queryCount p ω b ∂μ := by
  let code := compilePolicy hrd shortLabel p
  let q := ProcessTools.seedCodeMass μ code
  have hq := ProcessTools.seedCodeMass_nonneg μ code
  have hsq := ProcessTools.seedCodeMass_total μ code (measurable_compilePolicy hrd shortLabel p hp.2.1)
  let rep := ProcessTools.seedRepresentative code
  let policy := representativePolicy rep shortLabel p hp.1
  let decoder := representativeDecoder rep shortLabel p hrd n
  let P := shortSeedLaw (r:=r) q hq hsq
  let Q := expectedQueries P policy Prod.snd (fun ω => shortAlphabet ω.1) n
  have he := short_compressed_hamming_lt μ hr hrn hrd ε p hp
  have hi := finite_query_lower P Prod.fst policy Prod.snd (fun ω => shortAlphabet ω.1) n decoder
    (fun s => shortSeedLaw_source q hq hsq s) he (Real.log 3)
    (Law.Independent.map_left P Prod.fst Prod.snd
      (fun s : Signs r => (s,shortAlphabet (n:=n) s)) (shortSeedLaw_independent q hq hsq))
    (by
      intro t _ h hh j hj
      rw [P.localInformation_eq_condition_information Prod.fst (fun ω => shortAlphabet ω.1 j)
        (historyRV policy Prod.snd (fun ω => shortAlphabet ω.1) t) h hh]
      simpa using (P.condition _ h hh).information_le_log_card Prod.fst (fun ω => shortAlphabet ω.1 j))
  change RateDistortion.cRD*r ≤ Real.log 3*Q at hi
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun ω _ => mul_nonneg (P.nonneg ω)
    (Transcript.queryCount_nonneg policy ω.2 (shortAlphabet ω.1) n))
  have hlog : Real.log 3 ≤ 2 := by have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3); linarith
  have hhalf : (1/2:ℝ) ≤ RateDistortion.cRD := by linarith [RateDistortion.cRD_gt]
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hQR : (r:ℝ)/4 ≤ Q := by
    have hh := mul_le_mul_of_nonneg_right hhalf hr0
    have hl := mul_le_mul_of_nonneg_right hlog hQ
    linarith
  have hn : n < 160*r := (Nat.div_lt_iff_lt_mul (show 0<r by omega)).1 hN
  have hnR : (n:ℝ) < 160*r := by exact_mod_cast hn
  have hB : lowerBudget n r (1/1280000) ε ≤ Q := by
    unfold lowerBudget
    have hm := min_le_left (n:ℝ) ((r:ℝ)/ε^2)
    linarith
  exact (ENNReal.ofReal_le_ofReal hB).trans (compressed_short_cost_le μ hrd p hp.1 hp.2.1)

end Paper29.HardDistribution

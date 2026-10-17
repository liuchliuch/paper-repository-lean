import Paper29.ShortDistribution
import Paper29.PoolResponse

noncomputable section
open scoped BigOperators ENNReal Classical
open MeasureTheory
namespace Paper29.HardDistribution
open Transcript QueryModel

theorem short_compressed_hamming_lt {Ω : Type} [MeasurableSpace Ω] [Nonempty Ω]
    {n d r : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hr : 1 ≤ r) (hrn : r ≤ n) (hrd : r ≤ d) (ε : ℝ)
    (p : QueryModel.Policy Ω n d) (hp : Correct μ p (shortDesign n d r) ε) :
    let code := compilePolicy hrd shortLabel p
    let q := ProcessTools.seedCodeMass μ code
    let rep := ProcessTools.seedRepresentative code
    let policy := representativePolicy rep shortLabel p hp.1
    let P := shortSeedLaw (r:=r) q (ProcessTools.seedCodeMass_nonneg μ code)
      (ProcessTools.seedCodeMass_total μ code (measurable_compilePolicy hrd shortLabel p hp.2.1))
    (∑ ω,P.weight ω*RateDistortion.hamming ω.1
      (representativeDecoder rep shortLabel p hrd n
        (historyRV policy Prod.snd (fun ω => shortAlphabet ω.1) n ω))) < (1/25:ℝ)*r := by
  let code := compilePolicy hrd shortLabel p
  let q := ProcessTools.seedCodeMass μ code
  have hq := ProcessTools.seedCodeMass_nonneg μ code
  have hsq := ProcessTools.seedCodeMass_total μ code (measurable_compilePolicy hrd shortLabel p hp.2.1)
  let rep := ProcessTools.seedRepresentative code
  let policy := representativePolicy rep shortLabel p hp.1
  let P := shortSeedLaw (r:=r) q hq hsq
  let estimate := fun ω : Signs r × PolicyCode n r (Option Bool) =>
    representativeDecoder rep shortLabel p hrd n (historyRV policy Prod.snd (fun ω => shortAlphabet ω.1) n ω)
  let F := fun ω : Signs r × PolicyCode n r (Option Bool) =>
    codeSuccess hrd shortLabel p (shortDesign n d r) ε (shortAlphabet ω.1) ω.2
  change (∑ ω,P.weight ω*RateDistortion.hamming ω.1 (estimate ω)) < _
  apply expected_hamming_of_exact_success P Prod.fst estimate F hr
  · apply shortSeedLaw_event_ge q hq hsq F (99/100)
    intro s
    have hh := codeSuccess_probability μ hrd shortLabel p (shortDesign n d r) ε hp (shortAlphabet s)
    refine hh.trans_eq ?_
    unfold Sampling.eventMass
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext e
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,F]
  · intro ω hω
    obtain ⟨x,hdecode,hgood⟩ := codeSuccess_decoder hrd shortLabel p hp.1 (shortDesign n d r) ε
      (shortAlphabet ω.1) ω.2 hω
    change estimate ω=(fun j => decode (x (Fin.castLE hrd j))) at hdecode
    rw [hdecode]
    have he : (fun i : Fin n => shortLabel (shortAlphabet ω.1 i))=shortResponse ω.1 := (shortResponse_alphabet (n:=n) ω.1).symm
    rw [he] at hgood
    exact short_success_decodes hrn hrd ω.1 x ε hgood

/-- Finite product expectation factorization for the short hard distribution. -/
theorem shortSeedLaw_sum {E : Type} [Fintype E] {r : ℕ}
    (q : E → ℝ) (hq : ∀ e,0 ≤ q e) (hsq : ∑ e,q e=1) (f : Signs r × E → ℝ) :
    (∑ ω,(shortSeedLaw q hq hsq).weight ω*f ω) =
      ∑ s : Signs r,signMass r s*(∑ e,q e*f (s,e)) := by
  simp only [Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro e _
  change signMass r s*q e*f (s,e)=signMass r s*(q e*f (s,e))
  ring

theorem compressed_short_cost_le {Ω : Type} [MeasurableSpace Ω] [Nonempty Ω]
    {n d r : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (hrd : r ≤ d)
    (p : QueryModel.Policy Ω n d) (hfresh : Fresh p) (hp : ∀ h,Measurable (fun ω => p ω h)) :
    let code := compilePolicy hrd shortLabel p
    let q := ProcessTools.seedCodeMass μ code
    let rep := ProcessTools.seedRepresentative code
    let policy := representativePolicy rep shortLabel p hfresh
    let P := shortSeedLaw (r:=r) q (ProcessTools.seedCodeMass_nonneg μ code)
      (ProcessTools.seedCodeMass_total μ code (measurable_compilePolicy hrd shortLabel p hp))
    ENNReal.ofReal (expectedQueries P policy Prod.snd (fun ω => shortAlphabet ω.1) n) ≤
      ⨆ b : Fin n → ℝ, ∫⁻ ω,QueryModel.queryCount p ω b ∂μ := by
  let code := compilePolicy hrd shortLabel p
  let q := ProcessTools.seedCodeMass μ code
  have hq := ProcessTools.seedCodeMass_nonneg μ code
  have hsq := ProcessTools.seedCodeMass_total μ code (measurable_compilePolicy hrd shortLabel p hp)
  let rep := ProcessTools.seedRepresentative code
  let policy := representativePolicy rep shortLabel p hfresh
  change ENNReal.ofReal (expectedQueries (shortSeedLaw (r:=r) q hq hsq) policy
    Prod.snd (fun ω => shortAlphabet ω.1) n) ≤ _
  rw [expectedQueries,shortSeedLaw_sum]
  have hM (s : Signs r) :=
    (compressed_expected_queries_le μ hrd shortLabel p hfresh hp (shortAlphabet s)).trans
      (le_iSup (fun b : Fin n → ℝ => ∫⁻ ω,QueryModel.queryCount p ω b ∂μ)
        (fun i => shortLabel (shortAlphabet s i)))
  exact ProcessTools.ofReal_weighted_average_le (signMass r) (by intro s; unfold signMass; positivity)
    (signMass_total r) q hq (fun s e => Transcript.queryCount policy e (shortAlphabet s) n)
    (fun s e => Transcript.queryCount_nonneg policy e (shortAlphabet s) n)
    (⨆ b : Fin n → ℝ, ∫⁻ ω,QueryModel.queryCount p ω b ∂μ) (by
      intro s
      dsimp only [policy,rep,q,code]
      exact hM s)

end Paper29.HardDistribution

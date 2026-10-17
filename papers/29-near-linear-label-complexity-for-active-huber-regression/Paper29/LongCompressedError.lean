import Paper29.CompressedSuccess
import Paper29.PoolTranscript

noncomputable section
set_option maxHeartbeats 300000
open scoped BigOperators Classical
open MeasureTheory
namespace Paper29.HardDistribution
open Transcript QueryModel

/-- The actual hard law and a completely arbitrary measurable private seed
produce a causal finite decoder of expected Hamming error below .04r. -/
theorem long_compressed_hamming_lt {Ω : Type} [MeasurableSpace Ω] [Nonempty Ω]
    {n d r N : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hr : 1 ≤ r) (hN : 0 < N) (hrd : r ≤ d) (hblocks : r*N ≤ n)
    (ε β : ℝ) (hε : 0 ≤ ε) (hεhi : ε ≤ 1) (hβ : 0 < β) (hβhi : β ≤ 1/4)
    (hscale : 10 ≤ (N:ℝ)*β^2) (hβε : 200*ε ≤ β)
    (p : QueryModel.Policy Ω n d) (hp : Correct μ p (longDesign n d r N) ε) :
    let code := compilePolicy hrd (fun b => 4*bit b) p
    let q := ProcessTools.seedCodeMass μ code
    let rep := ProcessTools.seedRepresentative code
    let policy := representativePolicy rep (fun b => 4*bit b) p hp.1
    let P := hardSeedLaw (r:=r) (N:=N) q (ProcessTools.seedCodeMass_nonneg μ code)
      (ProcessTools.seedCodeMass_total μ code (measurable_compilePolicy hrd (fun b => 4*bit b) p hp.2.1)) β hβ.le (hβhi.trans (by norm_num))
    (∑ ω,P.weight ω*RateDistortion.hamming ω.1
      (representativeDecoder rep (fun b => 4*bit b) p hrd n
        (historyRV policy (fun ω => ω.2.2) (fun ω => poolBits hblocks ω.2.1) n ω))) < (1/25:ℝ)*r := by
  let label : Bool → ℝ := fun b => 4*bit b
  let code := compilePolicy hrd label p
  let q := ProcessTools.seedCodeMass μ code
  have hq := ProcessTools.seedCodeMass_nonneg μ code
  have hsq := ProcessTools.seedCodeMass_total μ code (measurable_compilePolicy hrd label p hp.2.1)
  let rep := ProcessTools.seedRepresentative code
  let policy := representativePolicy rep label p hp.1
  let P := hardSeedLaw (r:=r) (N:=N) q hq hsq β hβ.le (hβhi.trans (by norm_num))
  let estimate := fun ω : Signs r × (Bits r N × PolicyCode n r Bool) =>
    representativeDecoder rep label p hrd n (historyRV policy (fun ω => ω.2.2) (fun ω => poolBits hblocks ω.2.1) n ω)
  let F := fun ω : Signs r × (Bits r N × PolicyCode n r Bool) =>
    codeSuccess hrd label p (longDesign n d r N) ε (poolBits hblocks ω.2.1) ω.2.2
  have hprob (y : Bits r N) :=
    codeSuccess_probability μ hrd label p (longDesign n d r N) ε hp (poolBits hblocks y)
  change (∑ ω,P.weight ω*RateDistortion.hamming ω.1 (estimate ω)) < _
  apply finite_expected_hamming_of_good_bound P Prod.fst (fun ω => ω.2.1) estimate F hr hN β hβ
    (hβhi.trans (by norm_num)) hscale
  · intro s y
    exact ProductObservation.mass_source_responses _ _ _ _ _ _ _ _ _ s y
  · apply hardSeedLaw_event_ge q hq hsq β hβ.le (hβhi.trans (by norm_num)) F (99/100)
    intro s y
    refine (hprob y).trans_eq ?_
    unfold Sampling.eventMass
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext e
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,F]
  · intro ω hω
    obtain ⟨x,hdecode,hgood⟩ := codeSuccess_decoder hrd label p hp.1 (longDesign n d r N) ε
      (poolBits hblocks ω.2.1) ω.2.2 hω
    change estimate ω=(fun j => decode (x (Fin.castLE hrd j))) at hdecode
    rw [hdecode]
    have he : (fun i => label (poolBits hblocks ω.2.1 i))=longResponse ω.2.1 :=
      (longResponse_poolBits hN hblocks ω.2.1).symm
    rw [he] at hgood
    exact (hamming_le_bad_add_wrong β ω.1 ω.2.1 (fun j => x (Fin.castLE hrd j))).trans
      (add_le_add_left (successful_wrong_good_count hN β ε hβ hε hεhi hβε ω.1 ω.2.1
        (fun j => x (Fin.castLE hrd j))
        (long_success_block_comparator hN hrd hblocks ω.2.1 x ε hgood)) _)

end Paper29.HardDistribution

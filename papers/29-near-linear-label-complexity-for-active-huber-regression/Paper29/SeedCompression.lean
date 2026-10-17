import Paper29.SumMeasurableSingleton
import Paper29.RepresentativeSemantics
import Paper29.FiniteSeedMeasure

noncomputable section
open scoped BigOperators ENNReal Classical
open MeasureTheory
namespace Paper29.QueryModel

/-- Equal finite decision tables preserve every returned decoded answer, even
when their exact real output vectors differ. -/
theorem same_code_returned {Ω R : Type} {n d r : ℕ} (hrd : r ≤ d) (label : R → ℝ)
    (p : Policy Ω n d) (hfresh : Fresh p) (ω ω' : Ω) (b : Fin n → R)
    (hcode : compilePolicy hrd label p ω'=compilePolicy hrd label p ω)
    (x : Fin d → ℝ) (h : History n) (hrun : run p ω (fun i => label (b i))=some (x,h)) :
    ∃ x' h', run p ω' (fun i => label (b i))=some (x',h') ∧
      (fun j => HardDistribution.decode (x' (Fin.castLE hrd j))) =
        (fun j => HardDistribution.decode (x (Fin.castLE hrd j))) := by
  obtain ⟨g,hg,_⟩ := compilePolicy_run_returned hrd label p hfresh ω b x h hrun
  have hm := compilePolicy_execution_matches hrd label p hfresh ω' b (n+1) [] (by simp)
  change CodeResultMatches hrd label _ (run p ω' (fun i => label (b i))) at hm
  rw [hcode,hg] at hm
  cases hr : run p ω' (fun i => label (b i)) with
  | none => rw [hr] at hm; exact False.elim hm
  | some out =>
    rcases out with ⟨x',h'⟩
    rw [hr] at hm
    exact ⟨x',h',rfl,hm.1.symm⟩

/-- The final normalized transcript has the decoded answer of any successful
seed in its observed code fiber. No success of the chosen representative is assumed. -/
theorem compressed_decoder_returned {Ω R : Type} [Nonempty Ω] {n d r : ℕ}
    (hrd : r ≤ d) (label : R → ℝ) (p : Policy Ω n d) (hfresh : Fresh p)
    (ω : Ω) (b : Fin n → R) (x : Fin d → ℝ) (h : History n)
    (hrun : run p ω (fun i => label (b i))=some (x,h)) :
    let code := compilePolicy hrd label p
    let rep := ProcessTools.seedRepresentative code
    Transcript.representativeDecoder rep label p hrd n
      ((Transcript.representativePolicy rep label p hfresh).history (code ω) b n) =
        (fun j => HardDistribution.decode (x (Fin.castLE hrd j))) := by
  obtain ⟨x',h',hr',hd⟩ := same_code_returned hrd label p hfresh ω
    (ProcessTools.seedRepresentative (compilePolicy hrd label p) (compilePolicy hrd label p ω)) b
    (ProcessTools.seedRepresentative_observed _ ω) x h hrun
  exact (Transcript.representative_decoder_returned _ label p hfresh hrd _ b x' h' hr').trans hd

/-- Pointwise query-cost domination under the actual seed compression, retaining
extended cost ∞ on nonreturning source runs. -/
theorem compressed_queryCount_le {Ω R : Type} [Nonempty Ω] {n d r : ℕ}
    (hrd : r ≤ d) (label : R → ℝ) (p : Policy Ω n d) (hfresh : Fresh p)
    (ω : Ω) (b : Fin n → R) :
    let code := compilePolicy hrd label p
    let rep := ProcessTools.seedRepresentative code
    ENNReal.ofReal (Transcript.queryCount (Transcript.representativePolicy rep label p hfresh)
      (code ω) b n) ≤ queryCount p ω (fun i => label (b i)) := by
  let code := compilePolicy hrd label p
  let rep := ProcessTools.seedRepresentative code
  have hc := ProcessTools.seedRepresentative_observed code ω
  have hq := compilePolicy_queryCount hrd label p hfresh (rep (code ω)) b
  have hq' := compilePolicy_queryCount hrd label p hfresh ω b
  change code (rep (code ω))=code ω at hc
  change codeQueryCount (code (rep (code ω))) b = _ at hq
  rw [hc,hq'] at hq
  exact (Transcript.representative_queryCount_le rep label p hfresh (code ω) b).trans_eq hq.symm

/-- Compression of an arbitrary measurable private seed dominates the finite
normalized expected query cost. -/
theorem compressed_expected_queries_le {Ω R : Type} [MeasurableSpace Ω] [Nonempty Ω] [Fintype R]
    {n d r : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hrd : r ≤ d) (label : R → ℝ) (p : Policy Ω n d) (hfresh : Fresh p)
    (hp : ∀ h,Measurable (fun ω => p ω h)) (b : Fin n → R) :
    let code := compilePolicy hrd label p
    let rep := ProcessTools.seedRepresentative code
    (∑ e, ENNReal.ofReal (ProcessTools.seedCodeMass μ code e) *
      ENNReal.ofReal (Transcript.queryCount (Transcript.representativePolicy rep label p hfresh) e b n)) ≤
      ∫⁻ ω,queryCount p ω (fun i => label (b i)) ∂μ := by
  dsimp only
  rw [ProcessTools.seedCodeMass_lintegral μ _ (measurable_compilePolicy hrd label p hp)]
  exact lintegral_mono (fun ω => compressed_queryCount_le hrd label p hfresh ω b)

end Paper29.QueryModel

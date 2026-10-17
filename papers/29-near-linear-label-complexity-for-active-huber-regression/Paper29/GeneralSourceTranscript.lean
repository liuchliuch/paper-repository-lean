import Paper29.GeneralTranscript
import Paper29.ConditionalMapping

noncomputable section
open MeasureTheory
open scoped Classical ENNReal BigOperators
namespace Paper29.GeneralTranscript
open GeneralInformation

/-- Lemma4.3 for an arbitrary measurable source and arbitrary measurable
private seed. Response alphabets may be any standard Borel space (in particular
all real regression responses). General source quantization is a separately
disclosed standard Shannon theorem; posterior mappings and every adaptive
stopping/accounting deduction are proved locally. -/
theorem lemma4_3 {Ω E S R : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace S] [MeasurableSpace R] [StandardBorelSpace R] {n : ℕ}
    (rules : StandardRules) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (source : Ω → S) (seed : Ω → E) (responses : Ω → Fin n → R)
    (p : Choices E n R) (hfresh : Fresh p) (hstop : Absorbing p)
    (hsource : Measurable source) (hseed : Measurable seed) (hresponses : Measurable responses)
    (hp : ∀ t,Measurable (p t))
    (hind : ProbabilityTheory.IndepFun (fun ω => (source ω,responses ω)) seed μ)
    (K : (t : ℕ) → History E n R t → Measure (S × (Fin n → R)))
    (hcond : ∀ t∈Finset.range n,ConditionalLaw μ (fun ω => (source ω,responses ω))
      (fun ω => history p seed responses ω t) (K t)) (κ : ℝ≥0∞)
    (hlocal : ∀ t∈Finset.range n,∀ᵐ h ∂μ.map (fun ω => history p seed responses ω t),
      ∀ j,p t h=Sum.inl j → information (K t h) Prod.fst (fun sb => sb.2 j) ≤ κ) :
    information μ source (fun ω => history p seed responses ω n) ≤
      κ*∫⁻ ω,(queryCount p seed responses ω : ℝ≥0∞) ∂μ := by
  have hH := measurable_history p hp seed responses hseed hresponses n
  rw [rules.quantization μ source (fun ω => history p seed responses ω n) hsource hH]
  apply iSup_le
  intro m
  apply iSup_le
  intro f
  apply iSup_le
  intro hf
  let F : S × (Fin n → R) → Fin m × (Fin n → R) := fun sb => (f sb.1,sb.2)
  have hF : Measurable F := (hf.comp measurable_fst).prodMk measurable_snd
  let Kf := fun t h => (K t h).map F
  have hcondf : ∀ t∈Finset.range n,ConditionalLaw μ (fun ω => (f (source ω),responses ω))
      (fun ω => history p seed responses ω t) (Kf t) := by
    intro t ht
    exact (hcond t ht).map μ _ _ _ F hF
  have hindf : ProbabilityTheory.IndepFun (fun ω => (f (source ω),responses ω)) seed μ :=
    hind.comp hF measurable_id
  apply standard_source_transcript_bound rules μ (fun ω => f (source ω)) seed responses p hfresh hstop
    (hf.comp hsource) hseed hresponses hp hindf Kf hcondf κ
  intro t ht
  filter_upwards [hlocal t ht] with h hh
  intro j hj
  letI := (hcond t ht).2.1 h
  have hmap := information_map (K t h) F Prod.fst (fun sb => sb.2 j) hF measurable_fst
    ((measurable_pi_apply j).comp measurable_snd)
  change information (Kf t h) Prod.fst (fun sb => sb.2 j) =
    information (K t h) (fun sb => f sb.1) (fun sb => sb.2 j) at hmap
  rw [hmap]
  exact (rules.dataProcessing (K t h) Prod.fst (fun sb => sb.2 j) f measurable_fst
    ((measurable_pi_apply j).comp measurable_snd) hf).trans (hh j hj)

end Paper29.GeneralTranscript

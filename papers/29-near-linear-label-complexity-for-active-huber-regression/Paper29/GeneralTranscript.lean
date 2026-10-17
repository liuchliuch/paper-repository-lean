import Paper29.GeneralPosterior
import Paper29.SumBorel

noncomputable section
open MeasureTheory
open scoped Classical ENNReal BigOperators
namespace Paper29.GeneralTranscript
open GeneralInformation

/-- General measurable version of Lemma4.3. The posterior K is an actual
regular conditional law of (source,responses), with its disintegration stated
explicitly. Generic Shannon chain/relabeling rules are disclosed published
inputs. Every stopping-slot, active-slot integral, finite-chain and actual
fresh-query counting step is proved here. -/
theorem standard_source_transcript_bound {Ω E S R : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace S] [MeasurableSpace R] [StandardBorelSpace S] [StandardBorelSpace R] {n : ℕ}
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
  haveI : StandardBorelSpace (Slot n R) := by
    letI := upgradeStandardBorel R
    infer_instance
  let H := fun t ω => history p seed responses ω t
  have hH (t : ℕ) : Measurable (H t) := measurable_history p hp seed responses hseed hresponses t
  let a := fun t ω => (active p t (H t ω) : ℝ≥0∞)
  have ha (t : ℕ) : Measurable (a t) := (measurable_active p t (hp t)).comp (hH t)
  let I := fun t => ∫⁻ h,information (K t h) Prod.fst (fixedSlot p t h) ∂μ.map (H t)
  have hI (t : ℕ) (ht : t∈Finset.range n) : I t ≤ ∫⁻ ω,κ*a t ω ∂μ := by
    have hl : I t ≤ ∫⁻ h,κ*(active p t h : ℝ≥0∞) ∂μ.map (H t) := by
      apply lintegral_mono_ae
      filter_upwards [hlocal t ht] with h hh
      letI := (hcond t ht).2.1 h
      exact posterior_slot_bound rules p t h (K t h) κ hh
    exact hl.trans_eq (lintegral_map (measurable_const.mul (measurable_active p t (hp t))) (hH t))
  have hchain (k : ℕ) (hk : k≤n) : information μ source (H k) = ∑ t∈Finset.range k,I t := by
    induction k with
    | zero =>
      have hind' : ProbabilityTheory.IndepFun source seed μ := hind.comp measurable_fst measurable_id
      simpa only [H,history,Finset.sum_range_zero] using rules.independent μ source seed hsource hseed hind'
    | succ k ih =>
      have hkn : k∈Finset.range n := Finset.mem_range.mpr (by omega)
      let Z := fun ω => fixedSlot p k (H k ω) (source ω,responses ω)
      have hZ : Measurable Z := (measurable_joint_fixedSlot p k (hp k)).comp
        ((hH k).prodMk (hsource.prodMk hresponses))
      have hc := rules.chain μ source responses (H k) Z (K k) (fixedSlot p k)
        hsource hresponses (hH k) hZ (measurable_joint_fixedSlot p k (hp k)) (hcond k hkn) (fun _ => rfl)
      change information μ source (H (k+1))=information μ source (H k)+I k at hc
      rw [hc,ih (by omega),Finset.sum_range_succ]
  have hbound : information μ source (H n) ≤ ∑ t∈Finset.range n,∫⁻ ω,κ*a t ω ∂μ := by
    rw [hchain n le_rfl]
    exact Finset.sum_le_sum (fun t ht => hI t ht)
  have hQ : Measurable (fun ω => (queryCount p seed responses ω : ℝ≥0∞)) := by
    simp only [queryCount,Nat.cast_sum]
    exact Finset.measurable_sum _ (fun t _ => ha t)
  have hsum : (∑ t∈Finset.range n,∫⁻ ω,κ*a t ω ∂μ) =
      κ*∫⁻ ω,(queryCount p seed responses ω : ℝ≥0∞) ∂μ := by
    rw [← lintegral_finset_sum _ (fun t _ => measurable_const.mul (ha t))]
    calc
      _ = ∫⁻ ω,κ*(queryCount p seed responses ω : ℝ≥0∞) ∂μ := by
        apply lintegral_congr
        intro ω
        rw [← Finset.mul_sum]
        congr 1
        simp only [queryCount,Nat.cast_sum,a,H]
      _ = _ := lintegral_const_mul κ hQ
  exact hbound.trans_eq hsum

end Paper29.GeneralTranscript

import Paper35.GaussianMarked
import Paper35.GaussianSwitches
import Paper35.VisibleCrossing
import Mathlib.Analysis.Calculus.FDeriv.Measurable

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace Paper35.GaussianMarked

/-- Every transverse zero is isolated to its right, so parameter multiplicity
forms a countable set even before any probabilistic statement is applied. -/
theorem transverseZeros_countable {m : ℕ} (ψ : ℝ → Source.Space m)
    (L : ℝ) (D : Source.Space m) : (transverseZeros ψ L D).Countable := by
  apply (countable_setOf_isolated_right_within (s := transverseZeros ψ L D)).mono
  intro s hs
  refine ⟨hs, ?_⟩
  have hd : HasDerivAt (fun t => inner ℝ D (ψ t)) (inner ℝ D (deriv ψ s)) s := by
    simpa only [inner_zero_left, add_zero] using
      (hasDerivAt_const s D).inner ℝ hs.2.2.2.1.hasDerivAt
  obtain ⟨δ, hδ, hsign⟩ := signChanges_of_hasDerivAt_ne_zero hd hs.2.2.1 hs.2.2.2.2
  apply Filter.empty_mem_iff_bot.mp
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  refine ⟨Ioo (s-δ) (s+δ), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  rintro t ⟨htN, htS, hts⟩
  have htr : t ∈ Ioo s (s+δ) := ⟨hts, htN.2⟩
  have hzero : inner ℝ D (ψ t) = 0 := htS.2.2.1
  rcases hsign with ⟨_, hr⟩ | ⟨_, hr⟩
  · have hpos := hr t htr
    change 0 < inner ℝ D (ψ t) at hpos
    rw [hzero] at hpos
    exact lt_irrefl _ hpos
  · have hneg := hr t htr
    change inner ℝ D (ψ t) < 0 at hneg
    rw [hzero] at hneg
    exact lt_irrefl _ hneg

abbrev CurveParameter (L : ℝ) := Ioo (0 : ℝ) L
instance (L : ℝ) : StandardBorelSpace (CurveParameter L) :=
  (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) L)).standardBorel

abbrev MarkSample (m n : ℕ) := Source.Space m × (Source.Space m × (Fin n → Source.Space m))

/-- The actual marked transversal graph, with time as a standard Borel subtype. -/
def markedTransverseGraph {m : ℕ} (n : ℕ) (ψ : ℝ → Source.Space m) (L : ℝ) :
    Set (MarkSample m n × CurveParameter L) :=
  {z | inner ℝ z.1.1 (ψ z.2) = 0 ∧ DifferentiableAt ℝ ψ z.2 ∧
    inner ℝ z.1.1 (deriv ψ z.2) ≠ 0 ∧ z.1.2 ∈ vectorVisible n (ψ z.2)}

/-- Absolute continuity only on the source interval is sufficient for the Borel graph;
no global measurability or global continuity hypothesis is inserted. -/
theorem measurableSet_markedTransverseGraph {m : ℕ} (n : ℕ)
    (ψ : ℝ → Source.Space m) (L : ℝ) (hac : AbsolutelyContinuousOnInterval ψ 0 L) :
    MeasurableSet (markedTransverseGraph n ψ L) := by
  have hc : ContinuousOn ψ (Ioo 0 L) := hac.continuousOn.mono (fun s hs =>
    Set.mem_uIcc.mpr (Or.inl ⟨hs.1.le, hs.2.le⟩))
  have ht : Measurable (fun z : MarkSample m n × CurveParameter L => (z.2 : ℝ)) :=
    measurable_subtype_coe.comp measurable_snd
  have hcurve : Measurable (fun z : MarkSample m n × CurveParameter L => ψ z.2) :=
    hc.restrict.measurable.comp measurable_snd
  have hD : Measurable (fun z : MarkSample m n × CurveParameter L => z.1.1) := by fun_prop
  have hC : Measurable (fun z : MarkSample m n × CurveParameter L => z.1.2.1) := by fun_prop
  have hG (k : Fin n) :
      Measurable (fun z : MarkSample m n × CurveParameter L => z.1.2.2 k) := by fun_prop
  have heq := measurableSet_eq_fun (hD.inner hcurve) (measurable_const : Measurable (fun _ => (0 : ℝ)))
  have hdiff : MeasurableSet {z : MarkSample m n × CurveParameter L | DifferentiableAt ℝ ψ z.2} :=
    ht (measurableSet_of_differentiableAt ℝ ψ)
  have htrans : MeasurableSet {z : MarkSample m n × CurveParameter L |
      inner ℝ z.1.1 (deriv ψ z.2) ≠ 0} :=
    (measurableSet_eq_fun (hD.inner ((measurable_deriv ψ).comp ht))
      (measurable_const : Measurable (fun _ => (0 : ℝ)))).compl
  have hmark (k : Fin n) : MeasurableSet {z : MarkSample m n × CurveParameter L |
      inner ℝ (z.1.2.2 k) (ψ z.2) < (Real.sqrt 2)⁻¹ * inner ℝ z.1.2.1 (ψ z.2)} :=
    measurableSet_lt ((hG k).inner hcurve) ((hC.inner hcurve).const_mul _)
  convert heq.inter (hdiff.inter (htrans.inter (MeasurableSet.iInter hmark))) using 1
  ext z
  simp only [markedTransverseGraph, vectorVisible, Set.mem_setOf_eq, Set.mem_inter_iff,
    Set.mem_iInter]

/-- Sections are countable because they are subsets of actual transverse parameter sets. -/
theorem markedTransverseGraph_sections_countable {m : ℕ} (n : ℕ)
    (ψ : ℝ → Source.Space m) (L : ℝ) (a : MarkSample m n) :
    {s : CurveParameter L | (a,s) ∈ markedTransverseGraph n ψ L}.Countable := by
  apply ((transverseZeros_countable ψ L a.1).preimage Subtype.val_injective).mono
  intro s hs
  exact ⟨s.2.1, s.2.2, hs.1, hs.2.1, hs.2.2.1⟩

/-- Subtype parameter counting agrees exactly with the real-parameter encard. -/
theorem markedTransverseGraph_sectionCount {m : ℕ} (n : ℕ)
    (ψ : ℝ → Source.Space m) (L : ℝ) (a : MarkSample m n) :
    VisibleCrossing.sectionCount (markedTransverseGraph n ψ L) a =
      (((transverseZeros ψ L a.1) ∩ {s | a.2 ∈ vectorVisible n (ψ s)}).encard : ℝ≥0∞) := by
  have heq : (Subtype.val : CurveParameter L → ℝ) ''
      {s : CurveParameter L | (a,s) ∈ markedTransverseGraph n ψ L} =
        (transverseZeros ψ L a.1) ∩ {s | a.2 ∈ vectorVisible n (ψ s)} := by
    ext s
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s.2.1, s.2.2, hs.1, hs.2.1, hs.2.2.1⟩, hs.2.2.2⟩
    · rintro ⟨⟨hs0, hsL, hzero, hdiff, htrans⟩, hmark⟩
      exact ⟨⟨s, hs0, hsL⟩, ⟨hzero, hdiff, htrans, hmark⟩, rfl⟩
  unfold VisibleCrossing.sectionCount
  rw [← heq, Subtype.val_injective.encard_image]

/-- Joint measurability required by marked Tonelli, conditional only on the
same explicit published generic Lusin–Novikov theorem used by the crossing branch. -/
theorem measurable_markedTransverseCount {m : ℕ} (n : ℕ)
    (ψ : ℝ → Source.Space m) (L : ℝ) (hac : AbsolutelyContinuousOnInterval ψ 0 L)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample m n) (CurveParameter L)) :
    Measurable (fun a : MarkSample m n =>
      (((transverseZeros ψ L a.1) ∩ {s | a.2 ∈ vectorVisible n (ψ s)}).encard : ℝ≥0∞)) := by
  have hm := VisibleCrossing.measurable_sectionCount_of_LusinNovikov hLN
    (measurableSet_markedTransverseGraph n ψ L hac)
    (markedTransverseGraph_sections_countable n ψ L)
  simpa only [funext (markedTransverseGraph_sectionCount n ψ L)] using hm

/-- Tonelli converts the derived conditional marked Crofton formula to the
actual product Gaussian expectation; its measurability is proved above. -/
theorem product_marked_pair_crofton (hcrofton : ClassicalCroftonLaw)
    (hproj : GaussianUnitProjectionLaw) (m n : ℕ) (hm : 2 ≤ m) (L : ℝ) (hL : 0 < L)
    (ψ : ℝ → Source.Space m) (hac : AbsolutelyContinuousOnInterval ψ 0 L)
    (hunit : ∀ s ∈ Icc 0 L, ‖ψ s‖ = 1)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample m n) (CurveParameter L)) :
    (∫⁻ a : MarkSample m n,
      (((transverseZeros ψ L a.1) ∩ {s | a.2 ∈ vectorVisible n (ψ s)}).encard : ℝ≥0∞)
        ∂(standardGaussian m).prod (vectorMarkLaw m n)) =
      (ENNReal.ofReal (1 / Real.pi) * sphericalLength ψ L) * visibilityProbability n := by
  rw [lintegral_prod _ (measurable_markedTransverseCount n ψ L hac hLN).aemeasurable]
  exact marked_pair_crofton hcrofton hproj m n hm L hL ψ hac hunit

/-- The genuine pair-switch count is almost everywhere equal to the Borel
marked transversal count; its Gaussian product measurability is a consequence. -/
theorem aemeasurable_rotated_pairSwitchCount (hregular : ClassicalCroftonRegularityLaw)
    (m n : ℕ) (hm : 2 ≤ m) (L : ℝ) (hL : 0 < L)
    (ψ : ℝ → Source.Space m) (hac : AbsolutelyContinuousOnInterval ψ 0 L)
    (hunit : ∀ s ∈ Icc 0 L, ‖ψ s‖ = 1)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample m n) (CurveParameter L)) :
    AEMeasurable (fun a : MarkSample m n =>
      ((pairSwitchSet (rotatedScores n ψ a.1 a.2) L (firstPair n)).encard : ℝ≥0∞))
        ((standardGaussian m).prod (vectorMarkLaw m n)) := by
  apply (measurable_markedTransverseCount n ψ L hac hLN).aemeasurable.congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (hregular m hm L hL ψ hac hunit)] with a ha
  rw [pairSwitchSet_rotated_eq n ψ a.1 a.2 L ha]

/-- Product Gaussian expectation of the actual pair-switch count. -/
theorem product_first_pair_switch_crofton (hcrofton : ClassicalCroftonLaw)
    (hregular : ClassicalCroftonRegularityLaw) (hproj : GaussianUnitProjectionLaw)
    (m n : ℕ) (hm : 2 ≤ m) (L : ℝ) (hL : 0 < L)
    (ψ : ℝ → Source.Space m) (hac : AbsolutelyContinuousOnInterval ψ 0 L)
    (hunit : ∀ s ∈ Icc 0 L, ‖ψ s‖ = 1)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample m n) (CurveParameter L)) :
    (∫⁻ a : MarkSample m n,
      ((pairSwitchSet (rotatedScores n ψ a.1 a.2) L (firstPair n)).encard : ℝ≥0∞)
        ∂(standardGaussian m).prod (vectorMarkLaw m n)) =
      (ENNReal.ofReal (1 / Real.pi) * sphericalLength ψ L) * visibilityProbability n := by
  rw [lintegral_prod _
    (aemeasurable_rotated_pairSwitchCount hregular m n hm L hL ψ hac hunit hLN)]
  exact first_pair_switch_crofton hcrofton hregular hproj m n hm L hL ψ hac hunit

end Paper35.GaussianMarked

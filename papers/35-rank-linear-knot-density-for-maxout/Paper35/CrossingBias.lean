import Paper35.CrossingCount

/-! Fixed-weight conditional visible-crossing identity for two arbitrary
candidate bias densities. The remaining candidates stay fixed in this section. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal

namespace Paper35.Source.CrossingBias
open CrossingJacobian CrossingArea CrossingCount

variable {d K : ℕ}

/-- Replace just the selected two biases, preserving their weights and every
other candidate parameter. -/
def replacePairBiases (θ : Fin K → Candidate d) (q : OrderedCandidatePair K)
    (ξ : ℝ × ℝ) : Fin K → Candidate d := fun k =>
  if k = q.1.1 then ((θ q.1.1).1, ξ.1)
  else if k = q.1.2 then ((θ q.1.2).1, ξ.2) else θ k

@[simp] lemma replacePairBiases_left (θ : Fin K → Candidate d) (q : OrderedCandidatePair K)
    (ξ : ℝ × ℝ) : replacePairBiases θ q ξ q.1.1 = ((θ q.1.1).1, ξ.1) := by
  simp [replacePairBiases]

@[simp] lemma replacePairBiases_right (θ : Fin K → Candidate d) (q : OrderedCandidatePair K)
    (ξ : ℝ × ℝ) : replacePairBiases θ q ξ q.1.2 = ((θ q.1.2).1, ξ.2) := by
  simp [replacePairBiases, (ne_of_lt q.2).symm]

lemma replacePairBiases_other (θ : Fin K → Candidate d) (q : OrderedCandidatePair K)
    (ξ : ℝ × ℝ) {k : Fin K} (hki : k ≠ q.1.1) (hkj : k ≠ q.1.2) :
    replacePairBiases θ q ξ k = θ k := by
  simp [replacePairBiases, hki, hkj]

@[simp] theorem visibilityMark_replacePairBiases (p : Probe d) (θ : Fin K → Candidate d)
    (q : OrderedCandidatePair K) (ξ : ℝ × ℝ) :
    visibilityMark p (replacePairBiases θ q ξ) q = visibilityMark p θ q := by
  have hset : visibilitySet p (replacePairBiases θ q ξ) q = visibilitySet p θ q := by
    ext z
    constructor <;> intro h k hki hkj
    · simpa only [WeightedModel.scores, replacePairBiases_other θ q ξ hki hkj] using h k hki hkj
    · simpa only [WeightedModel.scores, replacePairBiases_other θ q ξ hki hkj] using h k hki hkj
  rw [visibilityMark, visibilityMark, hset]

/-- Relative Borel measurability is enough; the arbitrary continuation of the
probe outside its source interval plays no role. -/
theorem measurable_visibilityMark_on (p : Probe d) (θ : Fin K → Candidate d)
    (q : OrderedCandidatePair K) (D : Set (ℝ × ℝ)) (hsub : D ⊆ strip p) :
    Measurable (D.restrict (visibilityMark p θ q)) := by
  classical
  have hc : Continuous (fun z : D => p.curve z.1.1) := by
    simpa only [Function.comp_def] using
      p.lipschitz.continuousOn.comp_continuous
        (continuous_fst.comp continuous_subtype_val) (fun z => (hsub z.2).1)
  have hscores (k : Fin K) : Continuous (fun z : D => WeightedModel.scores p θ k z.1.1) := by
    exact (continuous_const.inner hc).add continuous_const
  have hheight : Continuous (fun z : D => z.1.2) := continuous_snd.comp continuous_subtype_val
  have hk (k : Fin K) : MeasurableSet {z : D |
      k ≠ q.1.1 → k ≠ q.1.2 → WeightedModel.scores p θ k z.1.1 < z.1.2} := by
    by_cases hki : k = q.1.1
    · simp [hki]
    by_cases hkj : k = q.1.2
    · simp [hkj]
    simpa [hki, hkj] using
      measurableSet_lt (hscores k).measurable hheight.measurable
  have hvis : MeasurableSet {z : D | z.1 ∈ visibilitySet p θ q} := by
    convert MeasurableSet.iInter hk using 1
    ext z
    simp only [visibilitySet, mem_setOf_eq, mem_iInter]
  have hm := (measurable_const : Measurable (fun _ : D => (1 : ℝ≥0∞))).indicator hvis
  exact hm

/-- For every absolutely continuous bias-pair law, almost every replaced pair
has the actual active-switch count supplied by the marked fiber formula. -/
theorem ae_visibility_fiberMass_eq_pairSwitchCount (p : Probe d)
    (θ : Fin K → Candidate d) (q : OrderedCandidatePair K)
    (ν : Measure (ℝ × ℝ)) (hν : ν ≪ (volume : Measure (ℝ × ℝ))) :
    ∀ᵐ ξ ∂ν,
      AreaFormula.fiberMass (phi p (θ q.1.1).1 (θ q.1.2).1)
          (Ioo 0 p.length ×ˢ univ) (visibilityMark p θ q) ξ =
        ((pairSwitchSet (WeightedModel.scores p (replacePairBiases θ q ξ)) p.length q).encard : ℝ≥0∞) := by
  filter_upwards [ae_not_exceptional_of_absolutelyContinuous p
    (θ q.1.1).1 (θ q.1.2).1 ν hν] with ξ hξ
  have hgood : (((replacePairBiases θ q ξ) q.1.1).2,
      ((replacePairBiases θ q ξ) q.1.2).2) ∉
      exceptionalBiases p ((replacePairBiases θ q ξ) q.1.1).1
        ((replacePairBiases θ q ξ) q.1.2).1 := by
    simpa only [replacePairBiases_left, replacePairBiases_right, Prod.fst, Prod.snd,
      Prod.mk.eta] using hξ
  have h := visibility_fiberMass_eq_pairSwitchCount p (replacePairBiases θ q ξ) q hgood
  simpa only [replacePairBiases_left, replacePairBiases_right, Prod.fst, Prod.snd,
    Prod.mk.eta, visibilityMark_replacePairBiases] using h

/-- The actual conditional pair-switch identity, with arbitrary measurable
bias-pair density. Taking `ρ ξ = gᵢ(wᵢ,ξ₁)gⱼ(wⱼ,ξ₂)` permits different laws. -/
theorem lintegral_pairSwitchCount_by_bias (p : Probe d)
    (θ : Fin K → Candidate d) (q : OrderedCandidatePair K)
    (ρ : (ℝ × ℝ) → ℝ≥0∞) (hρ : Measurable ρ) :
    (∫⁻ ξ, ((pairSwitchSet (WeightedModel.scores p (replacePairBiases θ q ξ)) p.length q).encard : ℝ≥0∞) * ρ ξ) =
      ∫⁻ z in Ioo 0 p.length ×ˢ (univ : Set ℝ),
        (visibilityMark p θ q z * ρ (phi p (θ q.1.1).1 (θ q.1.2).1 z)) *
          ENNReal.ofReal (|inner ℝ ((θ q.1.1).1 - (θ q.1.2).1) (deriv p.curve z.1)|) := by
  have hae := ae_visibility_fiberMass_eq_pairSwitchCount p θ q volume Measure.AbsolutelyContinuous.rfl
  calc
    (∫⁻ ξ, ((pairSwitchSet (WeightedModel.scores p (replacePairBiases θ q ξ)) p.length q).encard : ℝ≥0∞) * ρ ξ) =
        ∫⁻ ξ, AreaFormula.fiberMass (phi p (θ q.1.1).1 (θ q.1.2).1)
          (Ioo 0 p.length ×ˢ univ) (visibilityMark p θ q) ξ * ρ ξ := by
      apply lintegral_congr_ae
      filter_upwards [hae] with ξ hξ
      rw [hξ]
    _ = _ := phi_weighted_marked_area p (θ q.1.1).1 (θ q.1.2).1 _
      (measurableSet_Ioo.prod MeasurableSet.univ)
      (fun z hz => ⟨Ioo_subset_Icc_self hz.1, mem_univ _⟩)
      (visibilityMark p θ q)
      (measurable_visibilityMark_on p θ q _ (fun z hz => ⟨Ioo_subset_Icc_self hz.1, mem_univ _⟩)) ρ hρ

end Paper35.Source.CrossingBias

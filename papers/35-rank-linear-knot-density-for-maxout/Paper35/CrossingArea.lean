import Paper35.AreaFormula
import Paper35.Crossing
import Paper35.CrossingJacobian
import Mathlib.MeasureTheory.Group.Measure

/-! The marked rectifiable area identity (3.10) for the original affine-score
bias map, with all parameter preimages retained. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace Paper35.Source.CrossingArea
open CrossingJacobian

variable {d : ℕ}

local instance : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- The area formula for the actual bias map on any measurable part of the
probe strip. The only path assumptions are the original `Probe` assumptions. -/
theorem phi_marked_area (p : Probe d) (wi wj : Space d)
    (D : Set (ℝ × ℝ)) (hD : MeasurableSet D) (hsub : D ⊆ strip p)
    (a : (ℝ × ℝ) → ℝ≥0∞) (ha : Measurable a) :
    (∫⁻ z in D, a z * ENNReal.ofReal
      (|inner ℝ (wi - wj) (deriv p.curve z.1)|)) =
      ∫⁻ ξ, Paper35.AreaFormula.fiberMass (phi p wi wj) D a ξ := by
  have himage : volume (phi p wi wj '' (D ∩ badStrip p)) = 0 := by
    apply measure_mono_null (image_mono ?_) (phi_badStrip_image_null p wi wj)
    exact fun z hz => ⟨hsub hz.1, hz.2⟩
  have hder : ∀ z ∈ D \ badStrip p,
      HasFDerivWithinAt (phi p wi wj)
        (phiDeriv (inner ℝ wi (deriv p.curve z.1))
          (inner ℝ wj (deriv p.curve z.1))) (D \ badStrip p) z := by
    intro z hz
    apply (hasFDerivWithinAt_phi_off_badStrip p wi wj ⟨hsub hz.1, hz.2⟩).mono
    exact fun z hz => ⟨hsub hz.1, hz.2⟩
  have h := Paper35.AreaFormula.lintegral_fiberMass_of_null_exception volume hD
    (measurableSet_badStrip p) (badStrip_null p) himage hder ha
  symm
  simpa only [phiDeriv_abs_det, mul_comm] using h

/-- Marks need only be measurable on the actual domain. They are extended by
zero through the measurable subtype embedding before the area formula is used. -/
theorem phi_marked_area_on (p : Probe d) (wi wj : Space d)
    (D : Set (ℝ × ℝ)) (hD : MeasurableSet D) (hsub : D ⊆ strip p)
    (a : (ℝ × ℝ) → ℝ≥0∞) (ha : Measurable (D.restrict a)) :
    (∫⁻ z in D, a z * ENNReal.ofReal
      (|inner ℝ (wi - wj) (deriv p.curve z.1)|)) =
      ∫⁻ ξ, Paper35.AreaFormula.fiberMass (phi p wi wj) D a ξ := by
  let a0 : (ℝ × ℝ) → ℝ≥0∞ :=
    Function.extend (Subtype.val : D → ℝ × ℝ) (D.restrict a) (fun _ => 0)
  have hmeas : Measurable a0 :=
    (MeasurableEmbedding.subtype_coe hD).measurable_extend ha measurable_const
  have heq (z : ℝ × ℝ) (hz : z ∈ D) : a0 z = a z :=
    Subtype.val_injective.extend_apply (D.restrict a) (fun _ => 0) ⟨z, hz⟩
  have hmass : Paper35.AreaFormula.fiberMass (phi p wi wj) D a0 =
      Paper35.AreaFormula.fiberMass (phi p wi wj) D a := by
    funext ξ
    apply tsum_congr
    intro z
    exact heq z.1 z.2.1
  calc
    (∫⁻ z in D, a z * ENNReal.ofReal
      (|inner ℝ (wi - wj) (deriv p.curve z.1)|)) =
        ∫⁻ z in D, a0 z * ENNReal.ofReal
          (|inner ℝ (wi - wj) (deriv p.curve z.1)|) := by
      apply setLIntegral_congr_fun hD
      intro z hz
      change a z * ENNReal.ofReal |inner ℝ (wi - wj) (deriv p.curve z.1)| =
        a0 z * ENNReal.ofReal |inner ℝ (wi - wj) (deriv p.curve z.1)|
      rw [heq z hz]
    _ = ∫⁻ ξ, Paper35.AreaFormula.fiberMass (phi p wi wj) D a0 ξ :=
      phi_marked_area p wi wj D hD hsub a0 hmeas
    _ = ∫⁻ ξ, Paper35.AreaFormula.fiberMass (phi p wi wj) D a ξ := by rw [hmass]

/-- The truncated domain in the source proof of Lemma 3.1. -/
def crossingDomain (p : Probe d) (R : ℝ) : Set (ℝ × ℝ) :=
  Ioo 0 p.length ×ˢ Icc (-R) R

/-- Equation (3.10), including repeated crossings of retraced path portions. -/
theorem rectifiable_marked_area (p : Probe d) (wi wj : Space d) (R : ℝ)
    (a : (ℝ × ℝ) → ℝ≥0∞) (ha : Measurable a) :
    (∫⁻ z in crossingDomain p R, a z * ENNReal.ofReal
      (|inner ℝ (wi - wj) (deriv p.curve z.1)|)) =
      ∫⁻ ξ, Paper35.AreaFormula.fiberMass (phi p wi wj) (crossingDomain p R) a ξ := by
  apply phi_marked_area p wi wj _ (measurableSet_Ioo.prod measurableSet_Icc) ?_ a ha
  exact fun z hz => ⟨Ioo_subset_Icc_self hz.1, mem_univ _⟩

/-- No height truncation is needed after the null-image bridge is available. -/
theorem rectifiable_marked_area_unbounded (p : Probe d) (wi wj : Space d)
    (a : (ℝ × ℝ) → ℝ≥0∞) (ha : Measurable a) :
    (∫⁻ z in Ioo 0 p.length ×ˢ (univ : Set ℝ), a z * ENNReal.ofReal
      (|inner ℝ (wi - wj) (deriv p.curve z.1)|)) =
      ∫⁻ ξ, Paper35.AreaFormula.fiberMass (phi p wi wj)
        (Ioo 0 p.length ×ˢ univ) a ξ := by
  apply phi_marked_area p wi wj _ (measurableSet_Ioo.prod MeasurableSet.univ) ?_ a ha
  exact fun z hz => ⟨Ioo_subset_Icc_self hz.1, mem_univ _⟩


/-- The original parameter equality set of the two affine candidates. -/
def pairEqualityTimes (p : Probe d) (wi wj : Space d) (bi bj : ℝ) : Set ℝ :=
  {s | s ∈ Ioo 0 p.length ∧
    inner ℝ wi (p.curve s) + bi = inner ℝ wj (p.curve s) + bj}

/-- A bias-map fiber is in bijection with the corresponding parameter equality
times. The height is uniquely recovered as the common candidate value. -/
def crossingFiberEquiv (p : Probe d) (wi wj : Space d) (bi bj : ℝ) :
    {z : ℝ × ℝ | z ∈ Ioo 0 p.length ×ˢ (univ : Set ℝ) ∧
      phi p wi wj z = (bi, bj)} ≃ pairEqualityTimes p wi wj bi bj where
  toFun z := by
    refine ⟨z.1.1, z.2.1.1, ?_⟩
    have hi := congrArg Prod.fst z.2.2
    have hj := congrArg Prod.snd z.2.2
    change z.1.2 - inner ℝ wi (p.curve z.1.1) = bi at hi
    change z.1.2 - inner ℝ wj (p.curve z.1.1) = bj at hj
    linarith
  invFun s := by
    refine ⟨(s.1, inner ℝ wi (p.curve s.1) + bi), ⟨s.2.1, mem_univ _⟩, ?_⟩
    apply Prod.ext
    · change (inner ℝ wi (p.curve s.1) + bi) - inner ℝ wi (p.curve s.1) = bi
      ring
    · change (inner ℝ wi (p.curve s.1) + bi) - inner ℝ wj (p.curve s.1) = bj
      have heq := s.2.2
      linarith
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hi := congrArg Prod.fst z.2.2
      change z.1.2 - inner ℝ wi (p.curve z.1.1) = bi at hi
      change inner ℝ wi (p.curve z.1.1) + bi = z.1.2
      linarith
  right_inv s := by
    apply Subtype.ext
    rfl

/-- The area-formula multiplicity is exactly a weighted sum over original
parameters, so geometric self-intersections do not collapse the count. -/
theorem fiberMass_eq_parameter_sum (p : Probe d) (wi wj : Space d) (bi bj : ℝ)
    (a : (ℝ × ℝ) → ℝ≥0∞) :
    Paper35.AreaFormula.fiberMass (phi p wi wj) (Ioo 0 p.length ×ˢ univ) a (bi, bj) =
      ∑' s : pairEqualityTimes p wi wj bi bj,
        a (s.1, inner ℝ wi (p.curve s.1) + bi) := by
  exact ((crossingFiberEquiv p wi wj bi bj).symm.tsum_eq
    (fun z => a z.1)).symm


/-- Good parameter-height points where the candidate difference has zero speed. -/
def zeroSlopeStrip (p : Probe d) (wi wj : Space d) : Set (ℝ × ℝ) :=
  {z | z ∈ strip p \ badStrip p ∧ inner ℝ (wi - wj) (deriv p.curve z.1) = 0}

/-- The singular part of the actual bias map has a null image. -/
theorem phi_zeroSlope_image_null (p : Probe d) (wi wj : Space d) :
    volume (phi p wi wj '' zeroSlopeStrip p wi wj) = 0 := by
  have h := Paper35.AreaFormula.image_zeroJacobian_null volume
    (fun z hz => hasFDerivWithinAt_phi_off_badStrip p wi wj hz)
  have hset : {z | z ∈ strip p \ badStrip p ∧
      (phiDeriv (inner ℝ wi (deriv p.curve z.1))
        (inner ℝ wj (deriv p.curve z.1))).det = 0} = zeroSlopeStrip p wi wj := by
    ext z
    simp only [zeroSlopeStrip, mem_setOf_eq, phiDeriv_det, inner_sub_left, sub_eq_zero]
    constructor <;> intro hz <;> exact ⟨hz.1, hz.2.symm⟩
  rwa [hset] at h

/-- The two bias values for which nondifferentiable or nontransverse equalities
can occur; it is a concrete null set for every fixed weight pair. -/
def exceptionalBiases (p : Probe d) (wi wj : Space d) : Set (ℝ × ℝ) :=
  phi p wi wj '' (strip p ∩ badStrip p) ∪ phi p wi wj '' zeroSlopeStrip p wi wj

theorem exceptionalBiases_null (p : Probe d) (wi wj : Space d) :
    volume (exceptionalBiases p wi wj) = 0 :=
  measure_union_null (phi_badStrip_image_null p wi wj) (phi_zeroSlope_image_null p wi wj)

/-- Outside the explicit null bias set, every interior pair equality is
transverse at a differentiable parameter of the original probe. -/
theorem pairEquality_transverse_of_not_exceptional (p : Probe d) (wi wj : Space d)
    (bi bj : ℝ) (hgood : (bi, bj) ∉ exceptionalBiases p wi wj)
    {s : ℝ} (hs : s ∈ pairEqualityTimes p wi wj bi bj) :
    DifferentiableAt ℝ p.curve s ∧ inner ℝ (wi - wj) (deriv p.curve s) ≠ 0 := by
  let z : ℝ × ℝ := (s, inner ℝ wi (p.curve s) + bi)
  have hzs : z ∈ strip p := ⟨Ioo_subset_Icc_self hs.1, mem_univ _⟩
  have hfib : phi p wi wj z = (bi, bj) := by
    apply Prod.ext
    · change (inner ℝ wi (p.curve s) + bi) - inner ℝ wi (p.curve s) = bi
      ring
    · change (inner ℝ wi (p.curve s) + bi) - inner ℝ wj (p.curve s) = bj
      have heq := hs.2
      linarith
  have hzbad : z ∉ badStrip p := by
    intro hz
    exact hgood (Or.inl ⟨z, ⟨hzs, hz⟩, hfib⟩)
  have hdiff : DifferentiableAt ℝ p.curve s := by
    by_contra hn
    exact hzbad ⟨⟨Ioo_subset_Icc_self hs.1, hn⟩, mem_univ _⟩
  refine ⟨hdiff, ?_⟩
  intro hzero
  exact hgood (Or.inr ⟨z, ⟨⟨hzs, hzbad⟩, hzero⟩, hfib⟩)


/-- Under the explicit null-bias exclusion, strict visible equalities are
exactly the active switches of Definition 2.1 for this pair. -/
theorem pairSwitchSet_eq_visibleEqualityTimes {K : ℕ} (p : Probe d)
    (θ : Fin K → Candidate d) (q : OrderedCandidatePair K)
    (hgood : ((θ q.1.1).2, (θ q.1.2).2) ∉
      exceptionalBiases p (θ q.1.1).1 (θ q.1.2).1) :
    pairSwitchSet (WeightedModel.scores p θ) p.length q =
      {s | s ∈ Ioo 0 p.length ∧ VisiblePair (WeightedModel.scores p θ) s q} := by
  ext s
  constructor
  · rintro ⟨hs0, hsL, hvis, _⟩
    exact ⟨⟨hs0, hsL⟩, hvis⟩
  · rintro ⟨hs, hvis⟩
    have heq : s ∈ pairEqualityTimes p (θ q.1.1).1 (θ q.1.2).1
        (θ q.1.1).2 (θ q.1.2).2 := ⟨hs, hvis.1⟩
    obtain ⟨hdiff, htrans⟩ := pairEquality_transverse_of_not_exceptional p
      (θ q.1.1).1 (θ q.1.2).1 (θ q.1.1).2 (θ q.1.2).2 hgood heq
    have hi : HasDerivAt (WeightedModel.scores p θ q.1.1)
        (inner ℝ (θ q.1.1).1 (deriv p.curve s)) s := by
      simpa only [WeightedModel.scores, inner_zero_left, zero_add, add_zero] using
        (((hasDerivAt_const s (θ q.1.1).1).inner ℝ hdiff.hasDerivAt).add_const
          (θ q.1.1).2)
    have hj : HasDerivAt (WeightedModel.scores p θ q.1.2)
        (inner ℝ (θ q.1.2).1 (deriv p.curve s)) s := by
      simpa only [WeightedModel.scores, inner_zero_left, zero_add, add_zero] using
        (((hasDerivAt_const s (θ q.1.2).1).inner ℝ hdiff.hasDerivAt).add_const
          (θ q.1.2).2)
    have hne : inner ℝ (θ q.1.1).1 (deriv p.curve s) ≠
        inner ℝ (θ q.1.2).1 (deriv p.curve s) := by
      intro h
      exact htrans (by rw [inner_sub_left, h, sub_self])
    exact mem_pairSwitchSet_of_visiblePair_transverse hs.1 hs.2 hvis hi hj hne

end Paper35.Source.CrossingArea

import Paper35.CrossingBias
import Paper35.PairMarginal
import Paper35.VisibleCrossing
import Paper35.CrossingMeasurable
import Paper35.CrossingFubini
import Paper35.CrossingSlice
import Paper35.PairAlgebra
import Paper35.Heterogeneous

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped ENNReal

namespace Paper35.Source.ExactCrossing
open Source.WeightedModel CrossingJacobian CrossingArea CrossingCount CrossingBias
open Paper35.PairMarginal Paper35.VisibleCrossing
open CrossingMeasurable CrossingFubini CrossingSlice

variable {d K : ℕ}

def regularCount (p : Probe d) (q : OrderedCandidatePair K)
    (θ : Fin K → Candidate d) : ℝ≥0∞ := sectionCount (regularVisibleGraph p q) θ

lemma visibilityMark_replaceTwo (p : Probe d) (θ : Fin K → Candidate d)
    (q : OrderedCandidatePair K) (a b : Candidate d) :
    visibilityMark p (replaceTwo θ q.1.1 q.1.2 a b) q = visibilityMark p θ q := by
  have hset : visibilitySet p (replaceTwo θ q.1.1 q.1.2 a b) q = visibilitySet p θ q := by
    ext z
    constructor <;> intro h k hki hkj
    · simpa only [WeightedModel.scores, replaceTwo_other θ q.1.1 q.1.2 a b hki hkj] using h k hki hkj
    · simpa only [WeightedModel.scores, replaceTwo_other θ q.1.1 q.1.2 a b hki hkj] using h k hki hkj
  rw [visibilityMark, visibilityMark, hset]

lemma replaceTwo_weights_biases (θ : Fin K → Candidate d) (q : OrderedCandidatePair K)
    (wi wj : Space d) (ξ : ℝ × ℝ) :
    replacePairBiases (replaceTwo θ q.1.1 q.1.2 (wi,0) (wj,0)) q ξ =
      replaceTwo θ q.1.1 q.1.2 (wi,ξ.1) (wj,ξ.2) := by
  funext k
  by_cases hki : k = q.1.1
  · subst k
    simp
  by_cases hkj : k = q.1.2
  · subst k
    simp [replaceTwo_right, ne_of_lt q.2]
  rw [replacePairBiases_other _ _ _ hki hkj,
    replaceTwo_other _ _ _ _ _ hki hkj, replaceTwo_other _ _ _ _ _ hki hkj]

lemma selected_bias_count_eq_area (p : Probe d) (θ : Fin K → Candidate d)
    (q : OrderedCandidatePair K) (wi wj : Space d)
    (gi gj : ℝ → ℝ≥0∞) (hgi : Measurable gi) (hgj : Measurable gj)
    (hLN : LusinNovikovInput (Fin K → Candidate d) (ProbeParameter p)) :
    (∫⁻ bi : ℝ, ∫⁻ bj : ℝ, gi bi * gj bj *
      regularCount p q (replaceTwo θ q.1.1 q.1.2 (wi,bi) (wj,bj))) =
      ∫⁻ z in Ioo 0 p.length ×ˢ (univ : Set ℝ),
        (visibilityMark p θ q z *
          (gi (z.2 - inner ℝ wi (p.curve z.1)) * gj (z.2 - inner ℝ wj (p.curve z.1)))) *
          ENNReal.ofReal |inner ℝ (wi-wj) (deriv p.curve z.1)| := by
  let θw := replaceTwo θ q.1.1 q.1.2 (wi,0) (wj,0)
  let ρ : (ℝ × ℝ) → ℝ≥0∞ := fun ξ => gi ξ.1 * gj ξ.2
  have hρ : Measurable ρ := (hgi.comp measurable_fst).mul (hgj.comp measurable_snd)
  have hreg : Measurable (fun ξ : ℝ × ℝ =>
      regularCount p q (replaceTwo θ q.1.1 q.1.2 (wi,ξ.1) (wj,ξ.2))) :=
    (measurable_regularVisibleCount p q hLN).comp
      ((measurable_replaceTwo_pair θ q.1.1 q.1.2).comp
        ((measurable_const.prodMk measurable_fst).prodMk (measurable_const.prodMk measurable_snd)))
  have hae : ∀ᵐ ξ : ℝ × ℝ ∂volume,
      regularCount p q (replaceTwo θ q.1.1 q.1.2 (wi,ξ.1) (wj,ξ.2)) =
        ((pairSwitchSet (scores p (replacePairBiases θw q ξ)) p.length q).encard : ℝ≥0∞) := by
    filter_upwards [ae_not_exceptional_of_absolutelyContinuous p wi wj volume
      Measure.AbsolutelyContinuous.rfl] with ξ hξ
    rw [replaceTwo_weights_biases]
    apply regularVisibleCount_eq_pairSwitchCount p q _
    simpa only [replaceTwo_left, replaceTwo_right _ _ _ (ne_of_lt q.2),
      Prod.fst, Prod.snd, Prod.mk.eta] using hξ
  calc
    (∫⁻ bi : ℝ, ∫⁻ bj : ℝ, gi bi * gj bj *
      regularCount p q (replaceTwo θ q.1.1 q.1.2 (wi,bi) (wj,bj))) =
        ∫⁻ ξ : ℝ × ℝ, regularCount p q
          (replaceTwo θ q.1.1 q.1.2 (wi,ξ.1) (wj,ξ.2)) * ρ ξ := by
      rw [Measure.volume_eq_prod, lintegral_prod _ (hreg.mul hρ).aemeasurable]
      apply lintegral_congr
      intro bi
      apply lintegral_congr
      intro bj
      exact mul_comm _ _
    _ = ∫⁻ ξ, ((pairSwitchSet (scores p (replacePairBiases θw q ξ)) p.length q).encard : ℝ≥0∞) * ρ ξ := by
      apply lintegral_congr_ae
      filter_upwards [hae] with ξ hξ
      rw [hξ]
    _ = _ := by
      have h := lintegral_pairSwitchCount_by_bias p θw q ρ hρ
      simpa only [θw, replaceTwo_left, replaceTwo_right _ _ _ (ne_of_lt q.2),
        visibilityMark_replaceTwo, Prod.fst, Prod.snd, phi, ρ] using h

theorem selected_joint_count_eq_weight_area (p : Probe d) (θ : Fin K → Candidate d)
    (q : OrderedCandidatePair K) (mi mj : WeightedModel d)
    (hLN : LusinNovikovInput (Fin K → Candidate d) (ProbeParameter p)) :
    (∫⁻ ab, regularCount p q (replaceTwo θ q.1.1 q.1.2 ab.1 ab.2) ∂mi.joint.prod mj.joint) =
      ∫⁻ wi, (∫⁻ wj, (∫⁻ z : ℝ × ℝ in Ioo 0 p.length ×ˢ (univ : Set ℝ),
        (visibilityMark p θ q z *
          (mi.g wi (z.2 - inner ℝ wi (p.curve z.1)) *
            mj.g wj (z.2 - inner ℝ wj (p.curve z.1)))) *
          ENNReal.ofReal |inner ℝ (wi-wj) (deriv p.curve z.1)|) ∂mj.weights) ∂mi.weights := by
  rw [lintegral_independent_candidates_by_weights mi mj
    (f := fun ab => regularCount p q (replaceTwo θ q.1.1 q.1.2 ab.1 ab.2))
    ((measurable_regularVisibleCount p q hLN).comp (measurable_replaceTwo_pair θ q.1.1 q.1.2))]
  apply lintegral_congr
  intro wi
  apply lintegral_congr
  intro wj
  exact selected_bias_count_eq_area p θ q wi wj (mi.g wi) (mj.g wj)
    (mi.measurable_g.comp (measurable_const.prodMk measurable_id))
    (mj.measurable_g.comp (measurable_const.prodMk measurable_id)) hLN

def pairIntegrand (p : Probe d) (m : Fin K → WeightedModel d)
    (q : OrderedCandidatePair K) (z : ℝ × ℝ) : ℝ≥0∞ :=
  (∏ k ∈ (Finset.univ.erase q.1.1).erase q.1.2,
    (m k).scoreCDF (curveExtension p z.1) z.2) *
      mixedKernel (m q.1.1) (m q.1.2) (curveExtension p z.1) (deriv p.curve z.1) z.2

lemma measurable_pairIntegrand (p : Probe d) (m : Fin K → WeightedModel d)
    (q : OrderedCandidatePair K) : Measurable (pairIntegrand p m q) := by
  have hx : Measurable (fun z : ℝ × ℝ => curveExtension p z.1) :=
    (measurable_curveExtension p).comp measurable_fst
  have hu : Measurable (fun z : ℝ × ℝ => deriv p.curve z.1) :=
    (measurable_deriv p.curve).comp measurable_fst
  exact ((Finset.univ.erase q.1.1).erase q.1.2).measurable_fun_prod
    (fun k _ => (measurable_scoreCDF_joint (m k)).comp (hx.prodMk measurable_snd)) |>.mul
      ((measurable_mixedKernel (m q.1.1) (m q.1.2)).comp
        ((hx.prodMk hu).prodMk measurable_snd))

lemma lintegral_weightDensity (p : Probe d) (mi mj : WeightedModel d) (z : ℝ × ℝ) :
    (∫⁻ w, weightDensity p mi mj w z ∂mi.weights.prod mj.weights) =
      mixedKernel mi mj (curveExtension p z.1) (deriv p.curve z.1) z.2 := by
  haveI := mi.probability
  haveI := mj.probability
  have hm : Measurable (fun w : Space d × Space d => weightDensity p mi mj w z) :=
    (measurable_weightDensity p mi mj).comp (measurable_id.prodMk measurable_const)
  rw [lintegral_prod _ hm.aemeasurable, mixedKernel_eq_weights]
  apply lintegral_congr
  intro wi
  apply lintegral_congr
  intro wj
  simp only [weightDensity, mul_comm, mul_assoc]

/-- The actual random visible pair count, integrated under the heterogeneous
independent candidate laws, equals its Jacobian/slice intensity. -/
theorem expected_pairCount_eq_strip (p : Probe d) (m : Fin K → WeightedModel d)
    (q : OrderedCandidatePair K)
    (hLN : LusinNovikovInput (Fin K → Candidate d) (ProbeParameter p))
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    (∫⁻ θ, ((pairSwitchSet (scores p θ) p.length q).encard : ℝ≥0∞)
      ∂Measure.pi (fun k => (m k).joint)) =
        ∫⁻ z in Ioo 0 p.length ×ˢ (univ : Set ℝ), pairIntegrand p m q z := by
  haveI := (m q.1.1).probability
  haveI := (m q.1.2).probability
  let D : Set (ℝ × ℝ) := Ioo 0 p.length ×ˢ univ
  let μ := Measure.pi (fun k => (m k).joint)
  let ν := (m q.1.1).weights.prod (m q.1.2).weights
  have hV := measurable_globalMark p q
  have hR := measurable_weightDensity p (m q.1.1) (m q.1.2)
  calc
    _ = ∫⁻ θ, regularCount p q θ ∂μ :=
      (lintegral_regularVisibleCount_eq_pairSwitchCount p m q hUP).symm
    _ = ∫⁻ θ, ∫⁻ ab, regularCount p q (replaceTwo θ q.1.1 q.1.2 ab.1 ab.2)
        ∂(m q.1.1).joint.prod (m q.1.2).joint ∂μ :=
      lintegral_pi_eq_resample_pair _ _ _ (ne_of_lt q.2) _
        (measurable_regularVisibleCount p q hLN)
    _ = ∫⁻ θ, ∫⁻ wi, (∫⁻ wj, (∫⁻ z in D,
        (visibilityMark p θ q z *
          ((m q.1.1).g wi (z.2-inner ℝ wi (p.curve z.1)) *
            (m q.1.2).g wj (z.2-inner ℝ wj (p.curve z.1)))) *
          ENNReal.ofReal |inner ℝ (wi-wj) (deriv p.curve z.1)|)
          ∂(m q.1.2).weights) ∂(m q.1.1).weights ∂μ := by
      apply lintegral_congr
      intro θ
      exact selected_joint_count_eq_weight_area p θ q _ _ hLN
    _ = ∫⁻ θ, (∫⁻ w, (∫⁻ z in D, globalMark p θ q z *
        weightDensity p (m q.1.1) (m q.1.2) w z) ∂ν) ∂μ := by
      apply lintegral_congr
      intro θ
      have hm : Measurable (fun t : (Space d × Space d) × (ℝ × ℝ) =>
          globalMark p θ q t.2 * weightDensity p (m q.1.1) (m q.1.2) t.1 t.2) :=
        (hV.comp (measurable_const.prodMk measurable_snd)).mul hR
      rw [lintegral_prod _ hm.lintegral_prod_right'.aemeasurable]
      apply lintegral_congr
      intro wi
      apply lintegral_congr
      intro wj
      apply setLIntegral_congr_fun (measurableSet_Ioo.prod MeasurableSet.univ)
      intro z hz
      have hz' : z ∈ strip p := ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩
      dsimp only
      rw [globalMark_eq p θ q hz']
      simp only [weightDensity, curveExtension_eq p hz'.1, mul_assoc]
    _ = ∫⁻ z in D, (∫⁻ θ, globalMark p θ q z ∂μ) *
        (∫⁻ w, weightDensity p (m q.1.1) (m q.1.2) w z ∂ν) :=
      lintegral_factor_three μ ν (volume.restrict D) hV hR
    _ = _ := by
      apply lintegral_congr
      intro z
      rw [lintegral_globalMark, lintegral_weightDensity]
      rfl

/-- The open strip is converted to the source's closed arclength interval;
the endpoints have zero Lebesgue measure. -/
theorem expected_pairCount_eq_slices (p : Probe d) (m : Fin K → WeightedModel d)
    (q : OrderedCandidatePair K)
    (hLN : LusinNovikovInput (Fin K → Candidate d) (ProbeParameter p))
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    (∫⁻ θ, ((pairSwitchSet (scores p θ) p.length q).encard : ℝ≥0∞)
      ∂Measure.pi (fun k => (m k).joint)) =
        ∫⁻ s in Icc 0 p.length, ∫⁻ y,
          (∏ k ∈ (Finset.univ.erase q.1.1).erase q.1.2,
            (m k).scoreCDF (p.curve s) y) *
              mixedKernel (m q.1.1) (m q.1.2) (p.curve s) (deriv p.curve s) y := by
  rw [expected_pairCount_eq_strip p m q hLN hUP, Measure.volume_eq_prod,
    setLIntegral_prod _ (measurable_pairIntegrand p m q).aemeasurable,
    Measure.restrict_univ, restrict_Ioo_eq_restrict_Icc]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro s hs
  apply lintegral_congr
  intro y
  simp only [pairIntegrand, curveExtension_eq p hs]

/-- Exact heterogeneous visible-crossing formula (3.5), for arbitrary different
weighted candidate laws. Envelopes and moments are unnecessary for the identity. -/
theorem heterogeneous_crossing_identity (p : Probe d) (m : Fin K → WeightedModel d)
    (hLN : LusinNovikovInput (Fin K → Candidate d) (ProbeParameter p))
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    expectedSwitchCount (Measure.pi fun k => (m k).joint) (scores p) p.length =
      ∫⁻ s in Icc 0 p.length, ∫⁻ y,
        ∑ q : OrderedCandidatePair K,
          (∏ k ∈ (Finset.univ.erase q.1.1).erase q.1.2, (m k).scoreCDF (p.curve s) y) *
            mixedKernel (m q.1.1) (m q.1.2) (p.curve s) (deriv p.curve s) y := by
  have hm : Measurable (fun z : ℝ × ℝ => ∑ q : OrderedCandidatePair K,
      pairIntegrand p m q z) :=
    Finset.univ.measurable_fun_sum (fun q _ => measurable_pairIntegrand p m q)
  calc
    _ = ∑ q : OrderedCandidatePair K,
        ∫⁻ z in Ioo 0 p.length ×ˢ (univ : Set ℝ), pairIntegrand p m q z := by
      rw [expectedSwitchCount_eq_source_pairCounts p m hLN hUP]
      apply Finset.sum_congr rfl
      intro q _
      exact expected_pairCount_eq_strip p m q hLN hUP
    _ = ∫⁻ z in Ioo 0 p.length ×ˢ (univ : Set ℝ),
        ∑ q : OrderedCandidatePair K, pairIntegrand p m q z :=
      (lintegral_finset_sum Finset.univ (fun q _ => measurable_pairIntegrand p m q)).symm
    _ = _ := by
      rw [Measure.volume_eq_prod, setLIntegral_prod _ hm.aemeasurable,
        Measure.restrict_univ, restrict_Ioo_eq_restrict_Icc]
      apply setLIntegral_congr_fun measurableSet_Icc
      intro s hs
      apply lintegral_congr
      intro y
      simp only [pairIntegrand, curveExtension_eq p hs]

/-- The source's heterogeneous claim is a consequence of the proved identity,
with only the two explicitly stated classical descriptive-set-theory inputs. -/
theorem heterogeneous_exactCrossingClaim
    (hLN : ∀ p : Probe d, LusinNovikovInput (Fin K → Candidate d) (ProbeParameter p))
    (hUP : ∀ p : Probe d,
      BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    Paper35.Heterogeneous.ExactCrossingClaim d K := by
  intro m p
  rw [Paper35.Heterogeneous.Model.expectedCount,
    Paper35.Heterogeneous.Model.joint, heterogeneous_crossing_identity p m.candidate (hLN p) (hUP p)]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro s _
  apply lintegral_congr
  intro y
  exact sum_orderedCandidatePair K (fun i j =>
    m.visibility (p.curve s) y i j * m.kernel (p.curve s) (deriv p.curve s) y i j)

/-- Exact iid visible-crossing formula (3.7), retaining infinite expectations. -/
theorem iid_crossing_identity (m : WeightedModel d) (K : ℕ) (p : Probe d)
    (hLN : LusinNovikovInput (Fin K → Candidate d) (ProbeParameter p))
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    m.expectedCount K p = (K.choose 2 : ℝ≥0∞) *
      ∫⁻ s in Icc 0 p.length, ∫⁻ y,
        m.scoreCDF (p.curve s) y ^ (K-2) *
          m.crossingKernel (p.curve s) (deriv p.curve s) y := by
  change expectedSwitchCount (Measure.pi fun _ : Fin K => m.joint) (scores p) p.length = _
  rw [heterogeneous_crossing_identity p (fun _ => m) hLN hUP]
  have hp (s y : ℝ) :
      (∑ q : OrderedCandidatePair K,
        (∏ _k ∈ (Finset.univ.erase q.1.1).erase q.1.2, m.scoreCDF (p.curve s) y) *
          mixedKernel m m (p.curve s) (deriv p.curve s) y) =
        (K.choose 2 : ℝ≥0∞) * (m.scoreCDF (p.curve s) y ^ (K-2) *
          m.crossingKernel (p.curve s) (deriv p.curve s) y) := by
    calc
      _ = ∑ _q : OrderedCandidatePair K,
          m.scoreCDF (p.curve s) y ^ (K-2) *
            m.crossingKernel (p.curve s) (deriv p.curve s) y := by
        apply Finset.sum_congr rfl
        intro q _
        rw [prod_erase_pair_const q.1.1 q.1.2 (ne_of_lt q.2), mixedKernel_self]
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, card_orderedCandidatePair,
          nsmul_eq_mul]
  simp_rw [hp, lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]

/-- Discharges the original internal iid exact-crossing proof obligation. -/
theorem exactCrossingClaim
    (hLN : ∀ (K : ℕ) (p : Probe d),
      LusinNovikovInput (Fin K → Candidate d) (ProbeParameter p))
    (hUP : ∀ p : Probe d,
      BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    WeightedModel.ExactCrossingClaim (d := d) := by
  intro m K _ p
  exact iid_crossing_identity m K p (hLN K p) (hUP p)

end Paper35.Source.ExactCrossing


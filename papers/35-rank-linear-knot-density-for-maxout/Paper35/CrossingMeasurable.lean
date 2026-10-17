import Paper35.CrossingCount
import Paper35.VisibleCrossing
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Order.Group.Lattice

/-! Globally measurable extensions used only for Tonelli. Every extension is
proved equal to the original probe on its actual parameter domain. -/
noncomputable section
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ENNReal

namespace Paper35.Source.CrossingMeasurable
open WeightedModel CrossingJacobian CrossingCount VisibleCrossing
variable {d K : ℕ}

def curveExtension (p : Probe d) : ℝ → Space d :=
  Function.extend (Subtype.val : ProbeParameter p → ℝ) (fun s => p.curve s) (fun _ => 0)

lemma measurable_curveExtension (p : Probe d) : Measurable (curveExtension p) :=
  (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurable_extend
    (measurable_probe_curve p) measurable_const

lemma curveExtension_eq (p : Probe d) {s : ℝ} (hs : s ∈ Icc 0 p.length) :
    curveExtension p s = p.curve s :=
  Subtype.val_injective.extend_apply (fun t : ProbeParameter p => p.curve t)
    (fun _ => 0) ⟨s, hs⟩

attribute [irreducible] curveExtension

def visibilityGraph (q : OrderedCandidatePair K) :
    Set ((Fin K → Candidate d) × (Space d × ℝ)) :=
  {t | ∀ k, k ≠ q.1.1 → k ≠ q.1.2 → scoreValue t.2.1 (t.1 k) < t.2.2}

lemma measurableSet_visibilityGraph (q : OrderedCandidatePair K) :
    MeasurableSet (visibilityGraph (d := d) q) := by
  classical
  have hk (k : Fin K) : MeasurableSet {t : (Fin K → Candidate d) × (Space d × ℝ) |
      k ≠ q.1.1 → k ≠ q.1.2 → scoreValue t.2.1 (t.1 k) < t.2.2} := by
    by_cases hki : k = q.1.1
    · simp [hki]
    by_cases hkj : k = q.1.2
    · simp [hkj]
    have he : Measurable (fun t : (Fin K → Candidate d) × (Space d × ℝ) => t.1 k) :=
      (measurable_pi_apply k).comp measurable_fst
    have hs : Measurable (fun t : (Fin K → Candidate d) × (Space d × ℝ) =>
        scoreValue t.2.1 (t.1 k)) :=
      ((measurable_fst.comp he).inner (measurable_fst.comp measurable_snd)).add
        (measurable_snd.comp he)
    simpa [hki, hkj] using measurableSet_lt hs (measurable_snd.comp measurable_snd)
  convert MeasurableSet.iInter hk using 1
  ext t
  simp [visibilityGraph]

def visibilityAt (θ : Fin K → Candidate d) (q : OrderedCandidatePair K)
    (xy : Space d × ℝ) : ℝ≥0∞ :=
  (visibilityGraph q).indicator (fun _ => 1) (θ, xy)

lemma measurable_visibilityAt (q : OrderedCandidatePair K) :
    Measurable (fun t : (Fin K → Candidate d) × (Space d × ℝ) =>
      visibilityAt t.1 q t.2) :=
  measurable_const.indicator (measurableSet_visibilityGraph q)

attribute [irreducible] visibilityGraph visibilityAt

def globalMark (p : Probe d) (θ : Fin K → Candidate d) (q : OrderedCandidatePair K)
    (z : ℝ × ℝ) : ℝ≥0∞ := visibilityAt θ q (curveExtension p z.1, z.2)

lemma measurable_globalMark (p : Probe d) (q : OrderedCandidatePair K) :
    Measurable (fun t : (Fin K → Candidate d) × (ℝ × ℝ) => globalMark p t.1 q t.2) := by
  have hx : Measurable (fun t : (Fin K → Candidate d) × (ℝ × ℝ) => curveExtension p t.2.1) :=
    (measurable_curveExtension p).comp (measurable_fst.comp measurable_snd)
  have hy : Measurable (fun t : (Fin K → Candidate d) × (ℝ × ℝ) => t.2.2) :=
    measurable_snd.comp measurable_snd
  have ht : Measurable (fun t : (Fin K → Candidate d) × (ℝ × ℝ) => t.1) := measurable_fst
  have hm : Measurable (fun t : (Fin K → Candidate d) × (ℝ × ℝ) =>
      (t.1, (curveExtension p t.2.1, t.2.2))) := ht.prodMk (hx.prodMk hy)
  exact (measurable_visibilityAt (d := d) q).comp hm

lemma globalMark_eq (p : Probe d) (θ : Fin K → Candidate d) (q : OrderedCandidatePair K)
    {z : ℝ × ℝ} (hz : z ∈ strip p) : globalMark p θ q z = visibilityMark p θ q z := by
  classical
  have hevent : (θ, (curveExtension p z.1, z.2)) ∈ visibilityGraph q ↔
      z ∈ visibilitySet p θ q := by
    simp only [visibilityGraph, visibilitySet, mem_setOf_eq, scoreValue, scores,
      curveExtension_eq p hz.1]
  unfold globalMark visibilityAt visibilityMark
  by_cases h : z ∈ visibilitySet p θ q
  · rw [Set.indicator_of_mem (hevent.mpr h), Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (fun h' => h (hevent.mp h')), Set.indicator_of_notMem h]

/-- Integrating the remaining-candidate mark under the full independent product
law gives exactly its own CDF factors; selected unused coordinates have mass one. -/
theorem lintegral_globalMark (p : Probe d) (m : Fin K → WeightedModel d)
    (q : OrderedCandidatePair K) (z : ℝ × ℝ) :
    (∫⁻ θ, globalMark p θ q z ∂Measure.pi (fun k => (m k).joint)) =
      ∏ k ∈ (Finset.univ.erase q.1.1).erase q.1.2,
        (m k).scoreCDF (curveExtension p z.1) z.2 := by
  classical
  let P : Set (Fin K → Candidate d) :=
    {θ | (θ, (curveExtension p z.1, z.2)) ∈ visibilityGraph q}
  have hP : MeasurableSet P :=
    (measurableSet_visibilityGraph q).preimage (measurable_id.prodMk measurable_const)
  have hfun : (fun θ => globalMark p θ q z) = P.indicator (fun _ => 1) := by
    unfold globalMark visibilityAt
    rfl
  rw [hfun]
  change (∫⁻ θ, P.indicator 1 θ ∂Measure.pi (fun k => (m k).joint)) = _
  rw [lintegral_indicator_one hP]
  have hset : P = {θ | ∀ k ∈ (Finset.univ.erase q.1.1).erase q.1.2,
      scoreValue (curveExtension p z.1) (θ k) < z.2} := by
    ext θ
    simp only [P, visibilityGraph, mem_setOf_eq]
    constructor
    · intro h k hk
      exact h k (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1 (Finset.mem_erase.mp hk).1
    · intro h k hki hkj
      exact h k (by simp [hki, hkj])
  rw [hset]
  exact independent_strict_visibility_mass K m _ _ _

/-- The two conditional bias densities and the actual directional speed. -/
def weightDensity (p : Probe d) (mi mj : WeightedModel d)
    (w : Space d × Space d) (z : ℝ × ℝ) : ℝ≥0∞ :=
  (mi.g w.1 (z.2 - inner ℝ w.1 (curveExtension p z.1)) *
    mj.g w.2 (z.2 - inner ℝ w.2 (curveExtension p z.1))) *
      ENNReal.ofReal |inner ℝ (w.1-w.2) (deriv p.curve z.1)|

lemma measurable_weightDensity (p : Probe d) (mi mj : WeightedModel d) :
    Measurable (fun t : (Space d × Space d) × (ℝ × ℝ) => weightDensity p mi mj t.1 t.2) := by
  have hwi : Measurable (fun t : (Space d × Space d) × (ℝ × ℝ) => t.1.1) :=
    measurable_fst.comp measurable_fst
  have hwj : Measurable (fun t : (Space d × Space d) × (ℝ × ℝ) => t.1.2) :=
    measurable_snd.comp measurable_fst
  have hx : Measurable (fun t : (Space d × Space d) × (ℝ × ℝ) => curveExtension p t.2.1) :=
    (measurable_curveExtension p).comp (measurable_fst.comp measurable_snd)
  have hy : Measurable (fun t : (Space d × Space d) × (ℝ × ℝ) => t.2.2) :=
    measurable_snd.comp measurable_snd
  have hu : Measurable (fun t : (Space d × Space d) × (ℝ × ℝ) => deriv p.curve t.2.1) :=
    (measurable_deriv p.curve).comp (measurable_fst.comp measurable_snd)
  have hi := mi.measurable_g.comp (hwi.prodMk (hy.sub (hwi.inner hx)))
  have hj := mj.measurable_g.comp (hwj.prodMk (hy.sub (hwj.inner hx)))
  exact (hi.mul hj).mul (ENNReal.continuous_ofReal.measurable.comp ((((hwi.sub hwj).inner (𝕜 := ℝ) hu).abs)))

end Paper35.Source.CrossingMeasurable

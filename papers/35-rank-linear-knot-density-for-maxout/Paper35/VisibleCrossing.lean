import Mathlib.Probability.Independence.Basic
import Paper35.CrossingArea
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Paper35.SourceModel
import Paper35.Assembly
import Paper35.CDFPower
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Genuine conditional score laws and visibility marks for Lemma 3.1

This file proves the probability and density interfaces independently of the
multiplicity area formula. It does not assert that random switch counts already
satisfy that formula.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Paper35.VisibleCrossing
open Source Source.WeightedModel

variable {d : ℕ}

/-- The actual one-candidate score at the spatial point `x`. -/
def scoreValue (x : Space d) (θ : Candidate d) : ℝ := inner ℝ θ.1 x + θ.2

lemma measurable_scoreValue (x : Space d) : Measurable (scoreValue x) := by
  unfold scoreValue
  fun_prop

/-- The Lebesgue density of the score law, obtained from the specified
conditional bias representative, without conditioning on a zero-probability event. -/
def scoreDensity (m : WeightedModel d) (x : Space d) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ w, m.g w (y - inner ℝ w x) ∂m.weights

lemma measurable_shiftedDensity (m : WeightedModel d) (x : Space d) :
    Measurable (fun p : Space d × ℝ => m.g p.1 (p.2-inner ℝ p.1 x)) := by
  change Measurable ((Function.uncurry m.g) ∘ (fun p : Space d × ℝ =>
    (p.1,p.2-inner ℝ p.1 x)))
  exact m.measurable_g.comp (measurable_fst.prodMk (measurable_snd.sub (by fun_prop)))

lemma measurable_scoreDensity (m : WeightedModel d) (x : Space d) :
    Measurable (scoreDensity m x) := by
  haveI := m.probability
  exact (measurable_shiftedDensity m x).lintegral_prod_left

/-- The score pushforward integral, for every measurable nonnegative test.
This is the conditional-density translation followed by Tonelli. -/
theorem lintegral_scoreValue (m : WeightedModel d) (x : Space d)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ θ, f (scoreValue x θ) ∂m.joint) = ∫⁻ y, scoreDensity m x y * f y := by
  haveI := m.probability
  have htest : Measurable (fun θ : Candidate d => f (scoreValue x θ)) :=
    hf.comp (measurable_scoreValue x)
  have hg : Measurable (fun θ : Candidate d => m.g θ.1 θ.2) := by
    simpa only [Function.uncurry] using m.measurable_g
  rw [joint]
  have H := lintegral_withDensity_eq_lintegral_mul (m.weights.prod volume) hg htest
  simp only [Pi.mul_apply] at H
  rw [H, lintegral_prod _ (hg.mul htest).aemeasurable]
  have htranslate (w : Space d) :
      (∫⁻ b : ℝ, m.g w b * f (inner ℝ w x + b)) =
        ∫⁻ y : ℝ, m.g w (y-inner ℝ w x) * f y := by
    have H := lintegral_add_left_eq_self
      (μ := (volume : Measure ℝ))
      (fun y : ℝ => m.g w (y-inner ℝ w x) * f y) (inner ℝ w x)
    simpa only [add_sub_cancel_left] using H
  change (∫⁻ w, ∫⁻ b : ℝ, m.g w b * f (inner ℝ w x + b) ∂volume ∂m.weights) = _
  simp_rw [htranslate]
  rw [lintegral_lintegral_swap]
  · apply lintegral_congr
    intro y
    exact lintegral_mul_const _ ((m.measurable_g.comp
      (measurable_id.prodMk (measurable_const.sub (by fun_prop)))))
  · exact ((measurable_shiftedDensity m x).mul (hf.comp measurable_snd)).aemeasurable

/-- The score law has exactly the density prescribed in (3.1)--(3.3). -/
theorem scoreLaw_eq_withDensity (m : WeightedModel d) (x : Space d) :
    m.joint.map (scoreValue x) = volume.withDensity (scoreDensity m x) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_scoreValue x)]
  have H := lintegral_withDensity_eq_lintegral_mul volume (measurable_scoreDensity m x) hf
  simp only [Pi.mul_apply] at H
  rw [H]
  exact lintegral_scoreValue m x hf

/-- Strict and weak visibility have the same probability at every fixed
height because the conditional bias law makes every score law atomless. -/
theorem score_singleton_null (m : WeightedModel d) (x : Space d) (y : ℝ) :
    m.joint {θ | scoreValue x θ = y} = 0 := by
  have hmap := congrArg (fun ν : Measure ℝ => ν {y}) (scoreLaw_eq_withDensity m x)
  change (m.joint.map (scoreValue x)) {y} =
    (volume.withDensity (scoreDensity m x)) {y} at hmap
  rw [Measure.map_apply (measurable_scoreValue x) (measurableSet_singleton y)] at hmap
  have hz : (volume.withDensity (scoreDensity m x)) {y} = 0 := measure_singleton y
  rw [hz] at hmap
  change m.joint {θ | scoreValue x θ = y} = 0 at hmap
  exact hmap

lemma score_strict_eq_CDF (m : WeightedModel d) (x : Space d) (y : ℝ) :
    m.joint {θ | scoreValue x θ < y} = m.scoreCDF x y := by
  have hpartition : {θ | scoreValue x θ ≤ y} =
      {θ | scoreValue x θ < y} ∪ {θ | scoreValue x θ = y} := by
    ext θ
    exact (le_iff_lt_or_eq : scoreValue x θ ≤ y ↔ scoreValue x θ < y ∨ scoreValue x θ = y)
  unfold scoreCDF
  change m.joint {θ | scoreValue x θ < y} = m.joint {θ | scoreValue x θ ≤ y}
  rw [hpartition, measure_union]
  · simp [score_singleton_null]
  · apply Set.disjoint_left.mpr
    intro θ hlt heq
    exact (ne_of_lt hlt) heq
  · exact measurableSet_eq_fun (measurable_scoreValue x) measurable_const

lemma scoreDensity_normalized (m : WeightedModel d) (x : Space d) :
    (∫⁻ y, scoreDensity m x y) = 1 := by
  have H := lintegral_scoreValue m x (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ≥0∞)))
  simpa using H.symm

lemma scoreCDF_eq_densityLaw (m : WeightedModel d) (x : Space d) (y : ℝ) :
    m.scoreCDF x y = (volume.withDensity (scoreDensity m x)) (Iic y) := by
  rw [← scoreLaw_eq_withDensity, Measure.map_apply (measurable_scoreValue x) measurableSet_Iic]
  rfl

/-- Equation (3.3) gives the genuine height-density envelope. -/
lemma scoreDensity_le_average (m : WeightedModel d) (x : Space d) (y : ℝ) :
    scoreDensity m x y ≤ m.average := by
  apply lintegral_mono_ae
  filter_upwards [m.bound] with w hw
  exact hw (y-inner ℝ w x)

/-- The exact CDF normalization (4.6), now for the actual conditional score
law and the exact source CDF. -/
theorem scoreCDF_power_density (m : WeightedModel d) (x : Space d) (n : ℕ) :
    (∫⁻ y, m.scoreCDF x y^n * scoreDensity m x y) = (n+1 : ℝ≥0∞)⁻¹ := by
  have H := Paper35.CDFPower.lintegral_cdf_mass_pow_mul_density
    (measurable_scoreDensity m x).aemeasurable (scoreDensity_normalized m x) n
  simpa only [← scoreCDF_eq_densityLaw] using H

/-- Independence of an arbitrary finite collection of the other candidates
contributes exactly the corresponding CDF power, including the empty mark. -/
theorem iid_strict_visibility_mass (m : WeightedModel d) (K : ℕ)
    (x : Space d) (y : ℝ) (s : Finset (Fin K)) :
    m.iid K {θ | ∀ k ∈ s, scoreValue x (θ k) < y} = m.scoreCDF x y ^ s.card := by
  classical
  have hset : {θ : Fin K → Candidate d | ∀ k ∈ s, scoreValue x (θ k) < y} =
      Set.pi Set.univ (fun k => if k ∈ s then {θ | scoreValue x θ < y} else Set.univ) := by
    ext θ
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h k
      by_cases hk : k ∈ s <;> simp [hk, h k]
    · intro h k hk
      simpa only [if_pos hk, Set.mem_setOf_eq] using h k
  rw [hset, iid, Measure.pi_pi]
  have hmass (k : Fin K) : m.joint (if k ∈ s then {θ | scoreValue x θ < y} else univ) =
      if k ∈ s then m.scoreCDF x y else 1 := by
    split_ifs <;> simp [score_strict_eq_CDF]
  simp_rw [hmass]
  rw [Fintype.prod_ite_mem]
  simp

/-- The exact iid visibility mark in (3.7), for a specified distinct pair. -/
theorem iid_remaining_visibility_mass (m : WeightedModel d) (K : ℕ)
    (x : Space d) (y : ℝ) (i j : Fin K) (hij : i ≠ j) :
    m.iid K {θ | ∀ k, k ≠ i → k ≠ j → scoreValue x (θ k) < y} =
      m.scoreCDF x y ^ (K-2) := by
  classical
  have hevent : {θ : Fin K → Candidate d | ∀ k, k ≠ i → k ≠ j → scoreValue x (θ k) < y} =
      {θ | ∀ k ∈ (Finset.univ.erase i).erase j, scoreValue x (θ k) < y} := by
    ext θ
    simp only [Set.mem_setOf_eq, Finset.mem_erase, Finset.mem_univ, and_true]
    tauto
  rw [hevent, iid_strict_visibility_mass]
  congr 1
  rw [Finset.card_erase_of_mem (by simp [hij.symm]), Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin]
  omega

/-- A third independent candidate avoids every measurably selected spatial
point and height based on the other candidates. To apply this to every pair
crossing still requires a measurable countable enumeration of that pair's
crossings; that enumeration is not assumed to exist here. -/
theorem independent_score_avoids_selected_height {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (m : WeightedModel d) (x : Ω → Space d) (y : Ω → ℝ)
    (hx : Measurable x) (hy : Measurable y) :
    (ν.prod m.joint) {p : Ω × Candidate d | scoreValue (x p.1) p.2 = y p.1} = 0 := by
  have hs : MeasurableSet {p : Ω × Candidate d | scoreValue (x p.1) p.2 = y p.1} := by
    apply measurableSet_eq_fun _ (hy.comp measurable_fst)
    unfold scoreValue
    exact ((measurable_fst.comp measurable_snd).inner (hx.comp measurable_fst)).add
      (measurable_snd.comp measurable_snd)
  rw [Measure.prod_apply hs]
  have hnull (ω : Ω) : m.joint (Prod.mk ω ⁻¹'
      {p : Ω × Candidate d | scoreValue (x p.1) p.2 = y p.1}) = 0 := by
    exact score_singleton_null m (x ω) (y ω)
  simp only [hnull, lintegral_zero]

/-- In particular, two independent candidates have no fixed-location tie.
This includes either endpoint of the probe. -/
theorem independent_pair_fixed_tie_null (m : WeightedModel d) (x : Space d) :
    (m.joint.prod m.joint) {p : Candidate d × Candidate d |
      scoreValue x p.1 = scoreValue x p.2} = 0 := by
  have H := independent_score_avoids_selected_height m.joint m (fun _ : Candidate d => x)
    (scoreValue x) measurable_const (measurable_scoreValue x)
  have hset : {p : Candidate d × Candidate d | scoreValue x p.1 = scoreValue x p.2} =
      {p : Candidate d × Candidate d | scoreValue x p.2 = scoreValue x p.1} := by
    ext p
    exact eq_comm
  rw [hset]
  exact H

/-- Countably many measurably selected crossings remain null for an
independent third candidate. The existence of those selections remains a
separate geometric measurability obligation. -/
theorem independent_score_avoids_countable_heights {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (m : WeightedModel d) (x : ℕ → Ω → Space d) (y : ℕ → Ω → ℝ)
    (hx : ∀ n, Measurable (x n)) (hy : ∀ n, Measurable (y n)) :
    (ν.prod m.joint) {p : Ω × Candidate d | ∃ n, scoreValue (x n p.1) p.2 = y n p.1} = 0 := by
  have hset : {p : Ω × Candidate d | ∃ n, scoreValue (x n p.1) p.2 = y n p.1} =
      ⋃ n : ℕ, {p : Ω × Candidate d | scoreValue (x n p.1) p.2 = y n p.1} := by
    ext p
    simp
  rw [hset]
  exact measure_iUnion_null fun n => independent_score_avoids_selected_height ν m (x n) (y n) (hx n) (hy n)

end Paper35.VisibleCrossing


noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Paper35.VisibleCrossing
open Source Source.WeightedModel
variable {d : ℕ}

/-- Height densities are jointly measurable in the spatial point and height. -/
theorem measurable_scoreDensity_joint (m : WeightedModel d) :
    Measurable (fun p : Space d × ℝ => scoreDensity m p.1 p.2) := by
  haveI := m.probability
  have hg : Measurable (fun q : (Space d × ℝ) × Space d =>
      m.g q.2 (q.1.2 - inner ℝ q.2 q.1.1)) := by
    change Measurable ((Function.uncurry m.g) ∘ (fun q : (Space d × ℝ) × Space d =>
      (q.2,q.1.2-inner ℝ q.2 q.1.1)))
    exact m.measurable_g.comp (measurable_snd.prodMk
      ((measurable_snd.comp measurable_fst).sub
        (measurable_snd.inner (measurable_fst.comp measurable_fst))))
  exact hg.lintegral_prod_right

/-- The source score CDF is jointly measurable, with the exact joint law. -/
theorem measurable_scoreCDF_joint (m : WeightedModel d) :
    Measurable (fun p : Space d × ℝ => m.scoreCDF p.1 p.2) := by
  have hscore : Measurable (fun q : (Space d × ℝ) × Candidate d =>
      scoreValue q.1.1 q.2) := by
    unfold scoreValue
    exact ((measurable_fst.comp measurable_snd).inner
      (measurable_fst.comp measurable_fst)).add (measurable_snd.comp measurable_snd)
  have hm : Measurable (fun q : (Space d × ℝ) × Candidate d =>
      if scoreValue q.1.1 q.2 ≤ q.1.2 then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_le hscore (measurable_snd.comp measurable_fst))
      measurable_const measurable_const
  have heq (p : Space d × ℝ) : m.scoreCDF p.1 p.2 =
      ∫⁻ θ, (if scoreValue p.1 θ ≤ p.2 then (1 : ℝ≥0∞) else 0) ∂m.joint := by
    have hs : MeasurableSet {θ : Candidate d | scoreValue p.1 θ ≤ p.2} :=
      measurableSet_le (measurable_scoreValue p.1) measurable_const
    have H := lintegral_indicator_one (μ := m.joint) hs
    simp only [Set.indicator, Pi.one_apply, Set.mem_setOf_eq] at H
    exact H.symm
  simp_rw [heq]
  exact hm.lintegral_prod_right

/-- Fixed-slope/fixed-location R densities can be used in the score law
without any finite first-moment hypothesis. -/
lemma scoreDensity_finite (m : WeightedModel d) (x : Space d) (y : ℝ) :
    scoreDensity m x y ≠ ∞ :=
  ne_top_of_le_ne_top m.average_finite.ne (scoreDensity_le_average m x y)

end Paper35.VisibleCrossing


noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Paper35.VisibleCrossing
open Source Source.WeightedModel
variable {d : ℕ}

/-- Nonnegative integration against the genuine conditional candidate law. -/
theorem lintegral_joint (m : WeightedModel d) {f : Candidate d → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ θ, f θ ∂m.joint) = ∫⁻ w, ∫⁻ b : ℝ, m.g w b * f (w,b) ∂volume ∂m.weights := by
  haveI := m.probability
  have hg : Measurable (fun θ : Candidate d => m.g θ.1 θ.2) := by
    simpa only [Function.uncurry] using m.measurable_g
  rw [joint]
  have H := lintegral_withDensity_eq_lintegral_mul (m.weights.prod volume) hg hf
  simp only [Pi.mul_apply] at H
  rw [H, lintegral_prod _ (hg.mul hf).aemeasurable]

/-- Conditional-density disintegration of an actual independent pair, with
weights outside and the two biases inside as required by the area formula.
All equalities are nonnegative Tonelli equalities, including infinite values. -/
theorem lintegral_independent_pair_by_weights (m : WeightedModel d)
    {f : Candidate d × Candidate d → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p, f p ∂m.joint.prod m.joint) =
      ∫⁻ w, ∫⁻ w', ∫⁻ b : ℝ, ∫⁻ b' : ℝ,
        m.g w b * m.g w' b' * f ((w,b),(w',b')) ∂volume ∂volume ∂m.weights ∂m.weights := by
  haveI := m.probability
  have hg : Measurable (fun θ : Candidate d => m.g θ.1 θ.2) := by
    simpa only [Function.uncurry] using m.measurable_g
  let F : Candidate d × Candidate d → ℝ≥0∞ := fun p =>
    m.g p.1.1 p.1.2 * m.g p.2.1 p.2.2 * f p
  have hF : Measurable F := ((hg.comp measurable_fst).mul (hg.comp measurable_snd)).mul hf
  have H : (∫⁻ p, f p ∂m.joint.prod m.joint) =
      ∫⁻ p, F p ∂(m.weights.prod volume).prod (m.weights.prod volume) := by
    unfold joint
    rw [prod_withDensity hg hg]
    have H := lintegral_withDensity_eq_lintegral_mul
      ((m.weights.prod volume).prod (m.weights.prod volume))
      ((hg.comp measurable_fst).mul (hg.comp measurable_snd)) hf
    exact H
  rw [H, lintegral_prod _ hF.aemeasurable,
    lintegral_prod _ hF.lintegral_prod_right.aemeasurable]
  apply lintegral_congr
  intro w
  have hinner : (∫⁻ b : ℝ, ∫⁻ θ', F ((w,b),θ') ∂m.weights.prod volume) =
      ∫⁻ b : ℝ, ∫⁻ w', ∫⁻ b' : ℝ, F ((w,b),(w',b')) ∂volume ∂m.weights := by
    apply lintegral_congr
    intro b
    exact lintegral_prod _ (hF.comp measurable_prodMk_left).aemeasurable
  rw [hinner]
  have hthree : Measurable (fun q : (ℝ × Space d) × ℝ => F ((w,q.1.1),(q.1.2,q.2))) := by
    exact hF.comp ((measurable_const.prodMk (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  exact lintegral_lintegral_swap hthree.lintegral_prod_right.aemeasurable

/-- The same true disintegration for two heterogeneous independent candidates. -/
theorem lintegral_independent_candidates_by_weights (m m₂ : WeightedModel d)
    {f : Candidate d × Candidate d → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p, f p ∂m.joint.prod m₂.joint) =
      ∫⁻ w, ∫⁻ w', ∫⁻ b : ℝ, ∫⁻ b' : ℝ,
        m.g w b * m₂.g w' b' * f ((w,b),(w',b')) ∂volume ∂volume ∂m₂.weights ∂m.weights := by
  haveI := m.probability
  haveI := m₂.probability
  have hg : Measurable (fun θ : Candidate d => m.g θ.1 θ.2) := by
    simpa only [Function.uncurry] using m.measurable_g
  have hg₂ : Measurable (fun θ : Candidate d => m₂.g θ.1 θ.2) := by
    simpa only [Function.uncurry] using m₂.measurable_g
  let F : Candidate d × Candidate d → ℝ≥0∞ := fun p =>
    m.g p.1.1 p.1.2 * m₂.g p.2.1 p.2.2 * f p
  have hF : Measurable F := ((hg.comp measurable_fst).mul (hg₂.comp measurable_snd)).mul hf
  have H : (∫⁻ p, f p ∂m.joint.prod m₂.joint) =
      ∫⁻ p, F p ∂(m.weights.prod volume).prod (m₂.weights.prod volume) := by
    unfold joint
    rw [prod_withDensity hg hg₂]
    have H := lintegral_withDensity_eq_lintegral_mul
      ((m.weights.prod volume).prod (m₂.weights.prod volume))
      ((hg.comp measurable_fst).mul (hg₂.comp measurable_snd)) hf
    exact H
  rw [H, lintegral_prod _ hF.aemeasurable,
    lintegral_prod _ hF.lintegral_prod_right.aemeasurable]
  apply lintegral_congr
  intro w
  have hinner : (∫⁻ b : ℝ, ∫⁻ θ', F ((w,b),θ') ∂m₂.weights.prod volume) =
      ∫⁻ b : ℝ, ∫⁻ w', ∫⁻ b' : ℝ, F ((w,b),(w',b')) ∂volume ∂m₂.weights := by
    apply lintegral_congr
    intro b
    exact lintegral_prod _ (hF.comp measurable_prodMk_left).aemeasurable
  rw [hinner]
  have hthree : Measurable (fun q : (ℝ × Space d) × ℝ => F ((w,q.1.1),(q.1.2,q.2))) := by
    exact hF.comp ((measurable_const.prodMk (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  exact lintegral_lintegral_swap hthree.lintegral_prod_right.aemeasurable

/-- The visibility event is jointly measurable for locations and heights
selected using independent outer data. -/
lemma measurableSet_iid_random_visibility {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (x : Ω → Space d) (y : Ω → ℝ) (hx : Measurable x) (hy : Measurable y) :
    MeasurableSet {p : Ω × (Fin n → Candidate d) |
      ∀ k, scoreValue (x p.1) (p.2 k) < y p.1} := by
  have hs (k : Fin n) : MeasurableSet {p : Ω × (Fin n → Candidate d) |
      scoreValue (x p.1) (p.2 k) < y p.1} := by
    have heval : Measurable (fun p : Ω × (Fin n → Candidate d) => p.2 k) :=
      (measurable_pi_apply k).comp measurable_snd
    have hw : Measurable (fun p : Ω × (Fin n → Candidate d) => (p.2 k).1) := measurable_fst.comp heval
    have hb : Measurable (fun p : Ω × (Fin n → Candidate d) => (p.2 k).2) := measurable_snd.comp heval
    exact measurableSet_lt ((hw.inner (hx.comp measurable_fst)).add hb) (hy.comp measurable_fst)
  convert MeasurableSet.iInter hs using 1
  ext p
  simp

/-- Conditional visibility is computed by integration over a genuine product
law, not by conditioning on a pair equality of probability zero. -/
theorem iid_random_visibility_mass {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (m : WeightedModel d) (n : ℕ)
    (x : Ω → Space d) (y : Ω → ℝ) (hx : Measurable x) (hy : Measurable y) :
    (ν.prod (m.iid n)) {p : Ω × (Fin n → Candidate d) |
      ∀ k, scoreValue (x p.1) (p.2 k) < y p.1} =
        ∫⁻ ω, m.scoreCDF (x ω) (y ω)^n ∂ν := by
  rw [Measure.prod_apply (measurableSet_iid_random_visibility n x y hx hy)]
  apply lintegral_congr
  intro ω
  have H := iid_strict_visibility_mass m n (x ω) (y ω) Finset.univ
  simpa only [Finset.mem_univ, forall_true_left, Finset.card_univ, Fintype.card_fin] using H

/-- Independent heterogeneous candidates supply the exact product of their
own score CDFs on every selected set of remaining indices. -/
theorem independent_strict_visibility_mass (K : ℕ) (m : Fin K → WeightedModel d)
    (x : Space d) (y : ℝ) (s : Finset (Fin K)) :
    (Measure.pi (fun k => (m k).joint))
      {θ | ∀ k ∈ s, scoreValue x (θ k) < y} = ∏ k ∈ s, (m k).scoreCDF x y := by
  classical
  have hset : {θ : Fin K → Candidate d | ∀ k ∈ s, scoreValue x (θ k) < y} =
      Set.pi Set.univ (fun k => if k ∈ s then {θ | scoreValue x θ < y} else Set.univ) := by
    ext θ
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h k
      by_cases hk : k ∈ s <;> simp [hk, h k]
    · intro h k hk
      simpa only [if_pos hk, Set.mem_setOf_eq] using h k
  rw [hset, Measure.pi_pi]
  have hmass (k : Fin K) : (m k).joint (if k ∈ s then {θ | scoreValue x θ < y} else univ) =
      if k ∈ s then (m k).scoreCDF x y else 1 := by
    split_ifs <;> simp [score_strict_eq_CDF]
  simp_rw [hmass]
  exact Fintype.prod_ite_mem s (fun k => (m k).scoreCDF x y)

end Paper35.VisibleCrossing


noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Paper35.VisibleCrossing
open Source Source.WeightedModel
variable {d K : ℕ}

abbrev ProbeParameter (p : Probe d) : Type := {s : ℝ // s ∈ Icc (0 : ℝ) p.length}

/-- A probe is measurable on its actual compact parameter domain; no global
measurability of its arbitrary values outside that domain is inserted. -/
lemma measurable_probe_curve (p : Probe d) :
    Measurable (fun s : ProbeParameter p => p.curve s) := by
  exact (continuousOn_iff_continuous_restrict.mp p.lipschitz.continuousOn).measurable

set_option maxHeartbeats 400000 in
lemma measurable_probe_scoreCDF (m : WeightedModel d) (p : Probe d) :
    Measurable (fun q : ProbeParameter p × ℝ => m.scoreCDF (p.curve q.1) q.2) := by
  have hmap : Measurable (fun q : ProbeParameter p × ℝ => (p.curve q.1,q.2)) :=
    ((measurable_probe_curve p).comp measurable_fst).prodMk measurable_snd
  simpa only [Function.comp_apply] using (measurable_scoreCDF_joint m).comp hmap

lemma measurable_probe_scoreDensity (m : WeightedModel d) (p : Probe d) :
    Measurable (fun q : ProbeParameter p × ℝ => scoreDensity m (p.curve q.1) q.2) := by
  have hmap : Measurable (fun q : ProbeParameter p × ℝ => (p.curve q.1,q.2)) :=
    ((measurable_probe_curve p).comp measurable_fst).prodMk measurable_snd
  exact (measurable_scoreDensity_joint m).comp hmap

/-- The visibility event is Borel jointly in the common crossing parameter,
common height and all of the remaining independently sampled candidates. -/
lemma measurableSet_probe_visibility (p : Probe d) (i j : Fin K) :
    MeasurableSet {q : (ProbeParameter p × ℝ) × (Fin K → Candidate d) |
      ∀ k, k ≠ i → k ≠ j → scoreValue (p.curve q.1.1) (q.2 k) < q.1.2} := by
  classical
  have hs (k : Fin K) : MeasurableSet
      {q : (ProbeParameter p × ℝ) × (Fin K → Candidate d) |
        k ≠ i → k ≠ j → scoreValue (p.curve q.1.1) (q.2 k) < q.1.2} := by
    by_cases hki : k = i
    · simp [hki]
    by_cases hkj : k = j
    · simp [hkj]
    have hscore : Measurable (fun q : (ProbeParameter p × ℝ) × (Fin K → Candidate d) =>
        scoreValue (p.curve q.1.1) (q.2 k)) := by
      unfold scoreValue
      have heval : Measurable (fun q : (ProbeParameter p × ℝ) × (Fin K → Candidate d) => q.2 k) :=
        (measurable_pi_apply k).comp measurable_snd
      have hw : Measurable (fun q : (ProbeParameter p × ℝ) × (Fin K → Candidate d) => (q.2 k).1) :=
        measurable_fst.comp heval
      have hb : Measurable (fun q : (ProbeParameter p × ℝ) × (Fin K → Candidate d) => (q.2 k).2) :=
        measurable_snd.comp heval
      exact (hw.inner ((measurable_probe_curve p).comp (measurable_fst.comp measurable_fst))).add hb
    simpa [hki, hkj] using
      measurableSet_lt hscore (measurable_snd.comp measurable_fst)
  convert MeasurableSet.iInter hs using 1
  ext q
  simp

end Paper35.VisibleCrossing


/-!
# Explicit standard Lusin–Novikov input and measurable section counts

External input: A. S. Kechris, Classical Descriptive Set Theory, GTM 156,
Springer (1995), Theorem 18.10, p. 123, DOI 10.1007/978-1-4612-4190-4.
For standard Borel spaces X,Y and Borel R ⊆ X×Y with all vertical sections
countable, R is a countable union of Borel partial-function graphs. We use the
equivalent disjoint-graph form (remove the finitely many previous graphs).
A primary-author statement, citing precisely Kechris 18.10, is Theorem 1.4 in
Clemens–Lecomte–Miller, “Dichotomy theorems for families of non-cofinal essential
complexity”, https://webusers.imj-prg.fr/~dominique.lecomte/articles/treeable-1.pdf.

No axiom is declared: `LusinNovikovInput` is an explicit generic theorem input.
Everything from an enumeration to the actual maxout regular graph is proved.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Paper35.VisibleCrossing

section Generic
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A countable disjoint Borel partial-function enumeration of a relation. -/
structure BorelGraphEnumeration (R : Set (X × Y)) where
  domain : ℕ → Set X
  measurable_domain : ∀ n, MeasurableSet (domain n)
  value : ∀ n, domain n → Y
  measurable_value : ∀ n, Measurable (value n)
  covers : ∀ x y, (x,y) ∈ R ↔ ∃ n, ∃ hx : x ∈ domain n, value n ⟨x,hx⟩ = y
  disjoint : ∀ n m (x : X) (hn : x ∈ domain n) (hm : x ∈ domain m),
    value n ⟨x,hn⟩ = value m ⟨x,hm⟩ → n = m

/-- The ENNReal cardinality of a vertical section, including infinite ones. -/
def sectionCount (R : Set (X × Y)) (x : X) : ℝ≥0∞ := ({y | (x,y) ∈ R}.encard : ℝ≥0∞)

namespace BorelGraphEnumeration
variable {R : Set (X × Y)}

private def sectionEquiv (e : BorelGraphEnumeration R) (x : X) : {n : ℕ | x ∈ e.domain n} ≃ {y : Y | (x,y) ∈ R} :=
  Equiv.ofBijective (fun n => ⟨e.value n.1 ⟨x,n.2⟩,
    (e.covers x _).2 ⟨n.1,n.2,rfl⟩⟩) (by
      constructor
      · intro n m h
        apply Subtype.ext
        exact e.disjoint n.1 m.1 x n.2 m.2 (congrArg Subtype.val h)
      · intro y
        obtain ⟨n,hn,hny⟩ := (e.covers x y.1).1 y.2
        exact ⟨⟨n,hn⟩, Subtype.ext hny⟩)

/-- The actual section cardinal is the sum of the indicators of the Borel
enumeration domains, rather than a substitute counting variable. -/
theorem sectionCount_eq_tsum (e : BorelGraphEnumeration R) (x : X) :
    sectionCount R x = ∑' n, (e.domain n).indicator (fun _ => (1 : ℝ≥0∞)) x := by
  classical
  calc
    sectionCount R x = ∑' _y : {y : Y | (x,y) ∈ R}, (1 : ℝ≥0∞) :=
      (ENNReal.tsum_set_one _).symm
    _ = ∑' _n : {n : ℕ | x ∈ e.domain n}, (1 : ℝ≥0∞) :=
      ((e.sectionEquiv x).tsum_eq (fun _ => (1 : ℝ≥0∞))).symm
    _ = ∑' n, (e.domain n).indicator (fun _ => (1 : ℝ≥0∞)) x := by
      have H := tsum_subtype {n : ℕ | x ∈ e.domain n} (fun _ : ℕ => (1 : ℝ≥0∞))
      exact H.trans (tsum_congr fun n => by
        by_cases hn : x ∈ e.domain n <;> simp [Set.indicator, hn])

theorem measurable_sectionCount (e : BorelGraphEnumeration R) : Measurable (sectionCount R) := by
  have heq : sectionCount R = fun x => ∑' n, (e.domain n).indicator (fun _ => (1 : ℝ≥0∞)) x :=
    funext (sectionCount_eq_tsum e)
  rw [heq]
  exact Measurable.ennreal_tsum fun n => measurable_const.indicator (e.measurable_domain n)

/-- Tonelli for the genuine section count; no finiteness assumption is needed. -/
theorem lintegral_sectionCount (e : BorelGraphEnumeration R) (μ : Measure X) :
    (∫⁻ x, sectionCount R x ∂μ) = ∑' n, μ (e.domain n) := by
  simp_rw [sectionCount_eq_tsum e]
  rw [lintegral_tsum (fun n => (measurable_const.indicator (e.measurable_domain n)).aemeasurable)]
  congr 1
  funext n
  have H := lintegral_indicator_one (μ := μ) (e.measurable_domain n)
  simpa only [Pi.one_apply] using H
end BorelGraphEnumeration

/-- The precise standard-Borel Lusin–Novikov enumeration theorem used here.
This external input is generic in the relation and contains no maxout objects. -/
def LusinNovikovInput (X Y : Type*) [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] : Prop :=
  ∀ R : Set (X × Y), MeasurableSet R → (∀ x, {y | (x,y) ∈ R}.Countable) →
    Nonempty (BorelGraphEnumeration R)

theorem measurable_sectionCount_of_LusinNovikov [StandardBorelSpace X] [StandardBorelSpace Y]
    (hLN : LusinNovikovInput X Y) {R : Set (X × Y)}
    (hR : MeasurableSet R) (hc : ∀ x, {y | (x,y) ∈ R}.Countable) :
    Measurable (sectionCount R) := by
  obtain ⟨e⟩ := hLN R hR hc
  exact e.measurable_sectionCount
end Generic

section RegularGraph
open Source Source.WeightedModel
variable {d K : ℕ}

/-- Actual regular visible pair crossings, as a graph in all candidate
parameters and the compact probe parameter subtype. Endpoints are excluded. -/
def regularVisibleGraph (p : Probe d) (q : OrderedCandidatePair K) :
    Set ((Fin K → Candidate d) × ProbeParameter p) :=
  {z | 0 < (z.2 : ℝ) ∧ (z.2 : ℝ) < p.length ∧
    VisiblePair (WeightedModel.scores p z.1) z.2 q ∧
    DifferentiableAt ℝ p.curve z.2 ∧
    inner ℝ ((z.1 q.1.1).1 - (z.1 q.1.2).1) (deriv p.curve z.2) ≠ 0}

lemma measurable_regularScore (p : Probe d) (k : Fin K) :
    Measurable (fun z : (Fin K → Candidate d) × ProbeParameter p =>
      WeightedModel.scores p z.1 k z.2) := by
  have heval : Measurable (fun z : (Fin K → Candidate d) × ProbeParameter p => z.1 k) :=
    (measurable_pi_apply k).comp measurable_fst
  have hw : Measurable (fun z : (Fin K → Candidate d) × ProbeParameter p => (z.1 k).1) :=
    measurable_fst.comp heval
  have hb : Measurable (fun z : (Fin K → Candidate d) × ProbeParameter p => (z.1 k).2) :=
    measurable_snd.comp heval
  exact (hw.inner ((measurable_probe_curve p).comp measurable_snd)).add hb

lemma measurableSet_visiblePair_graph (p : Probe d) (q : OrderedCandidatePair K) :
    MeasurableSet {z : (Fin K → Candidate d) × ProbeParameter p |
      VisiblePair (WeightedModel.scores p z.1) z.2 q} := by
  classical
  have heq := measurableSet_eq_fun (measurable_regularScore p q.1.1)
    (measurable_regularScore p q.1.2)
  have hrest (k : Fin K) : MeasurableSet {z : (Fin K → Candidate d) × ProbeParameter p |
      k ≠ q.1.1 → k ≠ q.1.2 →
      WeightedModel.scores p z.1 k z.2 < WeightedModel.scores p z.1 q.1.1 z.2} := by
    by_cases hi : k = q.1.1
    · simp [hi]
    by_cases hj : k = q.1.2
    · simp [hj]
    simpa [hi,hj] using measurableSet_lt (measurable_regularScore p k)
      (measurable_regularScore p q.1.1)
  convert heq.inter (MeasurableSet.iInter hrest) using 1
  ext z
  simp only [VisiblePair, mem_setOf_eq, mem_inter_iff, mem_iInter]

/-- Borel regularity of the genuine all-parameter visible crossing graph. -/
theorem measurableSet_regularVisibleGraph (p : Probe d) (q : OrderedCandidatePair K) :
    MeasurableSet (regularVisibleGraph p q) := by
  have ht : Measurable (fun z : (Fin K → Candidate d) × ProbeParameter p => (z.2 : ℝ)) :=
    measurable_subtype_coe.comp measurable_snd
  have hD : MeasurableSet {z : (Fin K → Candidate d) × ProbeParameter p |
      DifferentiableAt ℝ p.curve z.2} :=
    ht (measurableSet_of_differentiableAt ℝ p.curve)
  have hi : Measurable (fun z : (Fin K → Candidate d) × ProbeParameter p => (z.1 q.1.1).1) :=
    measurable_fst.comp ((measurable_pi_apply q.1.1).comp measurable_fst)
  have hj : Measurable (fun z : (Fin K → Candidate d) × ProbeParameter p => (z.1 q.1.2).1) :=
    measurable_fst.comp ((measurable_pi_apply q.1.2).comp measurable_fst)
  have hinner : Measurable (fun z : (Fin K → Candidate d) × ProbeParameter p =>
      inner ℝ ((z.1 q.1.1).1 - (z.1 q.1.2).1) (deriv p.curve z.2)) :=
    (hi.sub hj).inner ((measurable_deriv p.curve).comp ht)
  have htrans : MeasurableSet {z : (Fin K → Candidate d) × ProbeParameter p |
      inner ℝ ((z.1 q.1.1).1 - (z.1 q.1.2).1) (deriv p.curve z.2) ≠ 0} :=
    (measurableSet_eq_fun hinner (measurable_const : Measurable (fun _ => (0 : ℝ)))).compl
  exact (measurableSet_lt measurable_const ht).inter
    ((measurableSet_lt ht measurable_const).inter
      ((measurableSet_visiblePair_graph p q).inter (hD.inter htrans)))

/-- The regular graph is a subset of the actual visible-pair switch set,
using the already-proved derivative sign-change theorem. -/
theorem regularVisibleGraph_mem_pairSwitchSet (p : Probe d) (q : OrderedCandidatePair K)
    (θ : Fin K → Candidate d) (s : ProbeParameter p)
    (hs : (θ,s) ∈ regularVisibleGraph p q) :
    (s : ℝ) ∈ pairSwitchSet (WeightedModel.scores p θ) p.length q := by
  obtain ⟨hs0,hsL,hvis,hdiff,htrans⟩ := hs
  have hi : HasDerivAt (WeightedModel.scores p θ q.1.1)
      (inner ℝ (θ q.1.1).1 (deriv p.curve s)) s := by
    simpa only [WeightedModel.scores, inner_zero_left, zero_add, add_zero] using
      (((hasDerivAt_const (s : ℝ) (θ q.1.1).1).inner ℝ hdiff.hasDerivAt).add_const
        (θ q.1.1).2)
  have hj : HasDerivAt (WeightedModel.scores p θ q.1.2)
      (inner ℝ (θ q.1.2).1 (deriv p.curve s)) s := by
    simpa only [WeightedModel.scores, inner_zero_left, zero_add, add_zero] using
      (((hasDerivAt_const (s : ℝ) (θ q.1.2).1).inner ℝ hdiff.hasDerivAt).add_const
        (θ q.1.2).2)
  have hne : inner ℝ (θ q.1.1).1 (deriv p.curve s) ≠
      inner ℝ (θ q.1.2).1 (deriv p.curve s) := by
    intro h
    exact htrans (by rw [inner_sub_left, h, sub_self])
  exact mem_pairSwitchSet_of_visiblePair_transverse hs0 hsL hvis hi hj hne

/-- Countability is proved for actual sections, not included in the model. -/
theorem regularVisibleGraph_sections_countable (p : Probe d) (q : OrderedCandidatePair K)
    (θ : Fin K → Candidate d) : {s : ProbeParameter p | (θ,s) ∈ regularVisibleGraph p q}.Countable := by
  apply ((pairSwitchSet_countable (WeightedModel.scores p θ) p.length q).preimage
    Subtype.val_injective).mono
  intro s hs
  exact regularVisibleGraph_mem_pairSwitchSet p q θ s hs

/-- Therefore the genuine regular visible-pair count is measurable, conditional
only on the explicitly published generic Lusin–Novikov theorem. -/
theorem measurable_regularVisibleCount (p : Probe d) (q : OrderedCandidatePair K)
    (hLN : LusinNovikovInput (Fin K → Candidate d) (ProbeParameter p)) :
    Measurable (sectionCount (regularVisibleGraph p q)) := by
  exact measurable_sectionCount_of_LusinNovikov hLN (measurableSet_regularVisibleGraph p q)
    (regularVisibleGraph_sections_countable p q)

/-- Outside the geometric null bias set, the regular graph's section is in
bijection with the exact source pair-switch set. -/
theorem regularVisibleCount_eq_pairSwitchCount (p : Probe d) (q : OrderedCandidatePair K)
    (θ : Fin K → Candidate d)
    (hgood : ((θ q.1.1).2,(θ q.1.2).2) ∉
      Source.CrossingArea.exceptionalBiases p (θ q.1.1).1 (θ q.1.2).1) :
    sectionCount (regularVisibleGraph p q) θ =
      ((pairSwitchSet (WeightedModel.scores p θ) p.length q).encard : ℝ≥0∞) := by
  have himage : (Subtype.val : ProbeParameter p → ℝ) ''
      {s : ProbeParameter p | (θ,s) ∈ regularVisibleGraph p q} =
        pairSwitchSet (WeightedModel.scores p θ) p.length q := by
    ext s
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact regularVisibleGraph_mem_pairSwitchSet p q θ t ht
    · intro hs
      let t : ProbeParameter p := ⟨s,hs.1.le,hs.2.1.le⟩
      have heq : s ∈ Source.CrossingArea.pairEqualityTimes p (θ q.1.1).1 (θ q.1.2).1
          (θ q.1.1).2 (θ q.1.2).2 := ⟨⟨hs.1,hs.2.1⟩,hs.2.2.1.1⟩
      obtain ⟨hdiff,htrans⟩ := Source.CrossingArea.pairEquality_transverse_of_not_exceptional p
        (θ q.1.1).1 (θ q.1.2).1 (θ q.1.1).2 (θ q.1.2).2 hgood heq
      exact ⟨t,⟨hs.1,hs.2.1,hs.2.2.1,hdiff,htrans⟩,rfl⟩
  have H := (Subtype.val_injective : Function.Injective (Subtype.val : ProbeParameter p → ℝ)).encard_image
    {s : ProbeParameter p | (θ,s) ∈ regularVisibleGraph p q}
  rw [himage] at H
  exact congrArg (fun n : ℕ∞ => (n : ℝ≥0∞)) H.symm

/-- The remaining measurability transfer uses precisely the geometric a.e.
null-bias exclusion; it does not assume measurable source counts. -/
theorem aemeasurable_pairSwitchCount_of_ae_not_exceptional (p : Probe d)
    (q : OrderedCandidatePair K) (μ : Measure (Fin K → Candidate d))
    (hLN : LusinNovikovInput (Fin K → Candidate d) (ProbeParameter p))
    (hgood : ∀ᵐ θ ∂μ, ((θ q.1.1).2,(θ q.1.2).2) ∉
      Source.CrossingArea.exceptionalBiases p (θ q.1.1).1 (θ q.1.2).1) :
    AEMeasurable (fun θ => ((pairSwitchSet (WeightedModel.scores p θ) p.length q).encard : ℝ≥0∞)) μ := by
  apply (measurable_regularVisibleCount p q hLN).aemeasurable.congr
  filter_upwards [hgood] with θ hθ
  exact regularVisibleCount_eq_pairSwitchCount p q θ hθ
end RegularGraph

end Paper35.VisibleCrossing


/-!
# Joint exceptional-bias nullity

Explicit external descriptive-set-theory input: Kechris, Classical Descriptive
Set Theory (1995), Theorem 21.10 (Lusin), and the standard fact that a Borel
projection is analytic. For standard Borel X,Y, a Borel R ⊆ X×Y has projection
measurable in the completion of every sigma-finite Borel measure on X.
`BorelProjectionNullMeasurableInput` supplies only that generic null-measurability;
all source-graph construction, section nullity and Fubini nullity below are proved.
No external input states nullity or mentions maxout.
-/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal
namespace Paper35.VisibleCrossing

/-- Generic analytic-projection universal measurability, specialized to Borel
relations but quantified over every sigma-finite Borel measure. -/
def BorelProjectionNullMeasurableInput (X Y : Type*) [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] : Prop :=
  ∀ R : Set (X × Y), MeasurableSet R → ∀ μ : Measure X, SigmaFinite μ →
    NullMeasurableSet (Prod.fst '' R) μ

/-- Completed-product Fubini: the measurability hypothesis cannot be omitted.
Here it is discharged for the source event by the generic projection input. -/
theorem product_null_of_nullMeasurable_sections {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [SFinite ν]
    {E : Set (X × Y)} (hE : NullMeasurableSet E (μ.prod ν))
    (hsections : ∀ x, ν (Prod.mk x ⁻¹' E) = 0) : (μ.prod ν) E = 0 := by
  let T := toMeasurable (μ.prod ν) E
  have hT : MeasurableSet T := measurableSet_toMeasurable _ _
  have hae : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, T (x,y) = E (x,y) :=
    ae_ae_of_ae_prod hE.toMeasurable_ae_eq
  have hnullT : (μ.prod ν) T = 0 := by
    apply (measure_prod_null hT).2
    filter_upwards [hae] with x hx
    have heq : (Prod.mk x ⁻¹' T) =ᵐ[ν] (Prod.mk x ⁻¹' E) := hx
    exact (measure_congr heq).trans (hsections x)
  exact (measure_congr hE.toMeasurable_ae_eq).symm.trans hnullT

open Source Source.WeightedModel Source.CrossingJacobian Source.CrossingArea
variable {d : ℕ}
abbrev WeightPair (d : ℕ) := Space d × Space d
abbrev BiasPair := ℝ × ℝ

def exceptionalBiasEvent (p : Probe d) : Set (WeightPair d × BiasPair) :=
  {z | z.2 ∈ exceptionalBiases p z.1.1 z.1.2}

/-- A Borel graph witnessing exactly the bad event. Common height is eliminated
using the first score; no quantification over a zero-probability equality law. -/
def exceptionalBiasWitness (p : Probe d) : Set ((WeightPair d × BiasPair) × ProbeParameter p) :=
  {q | inner ℝ q.1.1.1 (p.curve q.2) + q.1.2.1 =
        inner ℝ q.1.1.2 (p.curve q.2) + q.1.2.2 ∧
    (¬DifferentiableAt ℝ p.curve q.2 ∨
      inner ℝ (q.1.1.1-q.1.1.2) (deriv p.curve q.2) = 0)}

theorem measurableSet_exceptionalBiasWitness (p : Probe d) :
    MeasurableSet (exceptionalBiasWitness p) := by
  have ht : Measurable (fun q : (WeightPair d × BiasPair) × ProbeParameter p => (q.2 : ℝ)) :=
    measurable_subtype_coe.comp measurable_snd
  have hγ : Measurable (fun q : (WeightPair d × BiasPair) × ProbeParameter p => p.curve q.2) :=
    (measurable_probe_curve p).comp measurable_snd
  have hwi : Measurable (fun q : (WeightPair d × BiasPair) × ProbeParameter p => q.1.1.1) :=
    measurable_fst.comp (measurable_fst.comp measurable_fst)
  have hwj : Measurable (fun q : (WeightPair d × BiasPair) × ProbeParameter p => q.1.1.2) :=
    measurable_snd.comp (measurable_fst.comp measurable_fst)
  have hbi : Measurable (fun q : (WeightPair d × BiasPair) × ProbeParameter p => q.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hbj : Measurable (fun q : (WeightPair d × BiasPair) × ProbeParameter p => q.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have heq := measurableSet_eq_fun ((hwi.inner hγ).add hbi) ((hwj.inner hγ).add hbj)
  have hbad : MeasurableSet {q : (WeightPair d × BiasPair) × ProbeParameter p |
      ¬DifferentiableAt ℝ p.curve q.2} :=
    (ht (measurableSet_of_differentiableAt ℝ p.curve)).compl
  have hzero : MeasurableSet {q : (WeightPair d × BiasPair) × ProbeParameter p |
      inner ℝ (q.1.1.1-q.1.1.2) (deriv p.curve q.2) = 0} :=
    measurableSet_eq_fun ((hwi.sub hwj).inner ((measurable_deriv p.curve).comp ht)) measurable_const
  exact heq.inter (hbad.union hzero)

theorem exceptionalBiasEvent_iff (p : Probe d) (w : WeightPair d) (b : BiasPair) :
    (w,b) ∈ exceptionalBiasEvent p ↔ ∃ s : ProbeParameter p,
      ((w,b),s) ∈ exceptionalBiasWitness p := by
  constructor
  · intro h
    rcases h with ⟨z,hz,hφ⟩ | ⟨z,hz,hφ⟩
    · let s : ProbeParameter p := ⟨z.1,hz.1.1⟩
      have hi := congrArg Prod.fst hφ
      have hj := congrArg Prod.snd hφ
      change z.2-inner ℝ w.1 (p.curve z.1) = b.1 at hi
      change z.2-inner ℝ w.2 (p.curve z.1) = b.2 at hj
      exact ⟨s,⟨by change inner ℝ w.1 (p.curve z.1)+b.1=inner ℝ w.2 (p.curve z.1)+b.2; linarith,
        Or.inl hz.2.1.2⟩⟩
    · let s : ProbeParameter p := ⟨z.1,hz.1.1.1⟩
      have hi := congrArg Prod.fst hφ
      have hj := congrArg Prod.snd hφ
      change z.2-inner ℝ w.1 (p.curve z.1) = b.1 at hi
      change z.2-inner ℝ w.2 (p.curve z.1) = b.2 at hj
      exact ⟨s,⟨by change inner ℝ w.1 (p.curve z.1)+b.1=inner ℝ w.2 (p.curve z.1)+b.2; linarith,
        Or.inr hz.2⟩⟩
  · rintro ⟨s,heq,hbad⟩
    let z : ℝ × ℝ := (s,inner ℝ w.1 (p.curve s)+b.1)
    have hs : z ∈ strip p := ⟨s.2,mem_univ _⟩
    have hφ : phi p w.1 w.2 z = b := by
      apply Prod.ext
      · change (inner ℝ w.1 (p.curve s)+b.1)-inner ℝ w.1 (p.curve s)=b.1
        ring
      · change (inner ℝ w.1 (p.curve s)+b.1)-inner ℝ w.2 (p.curve s)=b.2
        linarith
    rcases hbad with hbad | hzero
    · exact Or.inl ⟨z,⟨hs,⟨⟨s.2,hbad⟩,mem_univ _⟩⟩,hφ⟩
    · by_cases hd : DifferentiableAt ℝ p.curve s
      · exact Or.inr ⟨z,⟨⟨hs,fun hz => hz.1.2 hd⟩,hzero⟩,hφ⟩
      · exact Or.inl ⟨z,⟨hs,⟨⟨s.2,hd⟩,mem_univ _⟩⟩,hφ⟩

theorem exceptionalBiasEvent_eq_projection (p : Probe d) :
    exceptionalBiasEvent p = Prod.fst '' exceptionalBiasWitness p := by
  ext z
  constructor
  · intro h
    obtain ⟨s,hs⟩ := (exceptionalBiasEvent_iff p z.1 z.2).1 h
    exact ⟨(z,s),hs,rfl⟩
  · rintro ⟨⟨w,s⟩,hs,h⟩
    subst z
    exact (exceptionalBiasEvent_iff p w.1 w.2).2 ⟨s,hs⟩

/-- The source joint bad event has product measure zero. The external input
provides only completion measurability; section nullity comes from the proven
geometric area/Sard argument. -/
theorem exceptionalBiasEvent_null (p : Probe d) (μ : Measure (WeightPair d)) [SigmaFinite μ]
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    (μ.prod (volume : Measure BiasPair)) (exceptionalBiasEvent p) = 0 := by
  have hmeas : NullMeasurableSet (exceptionalBiasEvent p) (μ.prod (volume : Measure BiasPair)) := by
    rw [exceptionalBiasEvent_eq_projection]
    exact hUP _ (measurableSet_exceptionalBiasWitness p) _ inferInstance
  apply product_null_of_nullMeasurable_sections μ volume hmeas
  intro w
  exact exceptionalBiases_null p w.1 w.2

/-- Regroup two actual candidates as their weight pair and bias pair. -/
def regroupCandidates (z : Candidate d × Candidate d) : WeightPair d × BiasPair :=
  ((z.1.1,z.2.1),(z.1.2,z.2.2))

lemma measurable_regroupCandidates : Measurable (regroupCandidates (d := d)) := by
  exact ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)).prodMk
    ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))

/-- The true independent pair law after weight/bias regrouping has the product
of its two conditional bias densities, even for singular weight laws. -/
theorem map_regroupCandidates (m m₂ : WeightedModel d) :
    (m.joint.prod m₂.joint).map regroupCandidates =
      ((m.weights.prod m₂.weights).prod (volume : Measure BiasPair)).withDensity
        (fun z => m.g z.1.1 z.2.1 * m₂.g z.1.2 z.2.2) := by
  haveI := m.probability
  haveI := m₂.probability
  have hg : Measurable (fun z : WeightPair d × BiasPair =>
      m.g z.1.1 z.2.1 * m₂.g z.1.2 z.2.2) := by
    have h₁ : Measurable (fun z : WeightPair d × BiasPair => m.g z.1.1 z.2.1) := by
      change Measurable ((Function.uncurry m.g) ∘ fun z : WeightPair d × BiasPair => (z.1.1,z.2.1))
      exact m.measurable_g.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))
    have h₂ : Measurable (fun z : WeightPair d × BiasPair => m₂.g z.1.2 z.2.2) := by
      change Measurable ((Function.uncurry m₂.g) ∘ fun z : WeightPair d × BiasPair => (z.1.2,z.2.2))
      exact m₂.measurable_g.comp ((measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.comp measurable_snd))
    exact h₁.mul h₂
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf measurable_regroupCandidates]
  change (∫⁻ z, (f ∘ regroupCandidates) z ∂m.joint.prod m₂.joint) = _
  rw [lintegral_independent_candidates_by_weights m m₂ (hf.comp measurable_regroupCandidates)]
  have H := lintegral_withDensity_eq_lintegral_mul
    ((m.weights.prod m₂.weights).prod (volume : Measure BiasPair)) hg hf
  simp only [Pi.mul_apply] at H
  rw [H, lintegral_prod _ (hg.mul hf).aemeasurable,
    lintegral_prod _ (hg.mul hf).lintegral_prod_right.aemeasurable]
  apply lintegral_congr
  intro w
  apply lintegral_congr
  intro w'
  rw [Measure.volume_eq_prod]
  have hfix : Measurable (fun y : BiasPair => m.g w y.1 * m₂.g w' y.2 * f ((w,w'),y)) := by
    simpa only [Function.comp_apply] using (hg.mul hf).comp
      (measurable_const.prodMk measurable_id : Measurable (fun y : BiasPair => ((w,w'),y)))
  have Hbias := lintegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun y : BiasPair => m.g w y.1 * m₂.g w' y.2 * f ((w,w'),y)) hfix.aemeasurable
  simpa only [Function.comp_apply, regroupCandidates] using Hbias.symm

/-- The generic analytic-projection input plus actual conditional densities
exclude the geometric bad bias pairs under the actual independent pair law. -/
theorem independent_pair_exceptional_null (p : Probe d) (m m₂ : WeightedModel d)
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    (m.joint.prod m₂.joint) {z : Candidate d × Candidate d |
      (z.1.2,z.2.2) ∈ exceptionalBiases p z.1.1 z.2.1} = 0 := by
  haveI := m.probability
  haveI := m₂.probability
  have hz := exceptionalBiasEvent_null p (m.weights.prod m₂.weights) hUP
  have hmap : ((m.joint.prod m₂.joint).map regroupCandidates) (exceptionalBiasEvent p) = 0 := by
    rw [map_regroupCandidates]
    exact withDensity_absolutelyContinuous _ _ hz
  exact preimage_null_of_map_null measurable_regroupCandidates.aemeasurable hmap

/-- The selected coordinate pair in the actual heterogeneous finite product
has exactly the independent product of its own two candidate laws. -/
theorem map_selectedCandidates {K : ℕ} (m : Fin K → WeightedModel d)
    (i j : Fin K) (hij : i ≠ j) :
    (Measure.pi (fun k => (m k).joint)).map (fun θ => (θ i,θ j)) =
      (m i).joint.prod (m j).joint := by
  have hind := ProbabilityTheory.iIndepFun_pi
    (μ := fun k : Fin K => (m k).joint) (X := fun _ => (id : Candidate d → Candidate d))
    (fun _ => measurable_id.aemeasurable)
  have H := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable).1 (hind.indepFun hij)
  rw [(measurePreserving_eval (fun k : Fin K => (m k).joint) i).map_eq,
    (measurePreserving_eval (fun k : Fin K => (m k).joint) j).map_eq] at H
  exact H

/-- Actual joint good-event conclusion for all candidate parameters. This is
proved, rather than inserted as an extra source hypothesis. -/
theorem ae_selectedPair_not_exceptional {K : ℕ} (p : Probe d)
    (m : Fin K → WeightedModel d) (q : OrderedCandidatePair K)
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    ∀ᵐ θ ∂Measure.pi (fun k => (m k).joint),
      ((θ q.1.1).2,(θ q.1.2).2) ∉ exceptionalBiases p (θ q.1.1).1 (θ q.1.2).1 := by
  have hnull := independent_pair_exceptional_null p (m q.1.1) (m q.1.2) hUP
  rw [← map_selectedCandidates m q.1.1 q.1.2 (ne_of_lt q.2)] at hnull
  have H := preimage_null_of_map_null
    (((measurable_pi_apply q.1.1).prodMk (measurable_pi_apply q.1.2)).aemeasurable) hnull
  simpa only [ae_iff, Classical.not_not] using H

/-- Actual source pair counts are a.e. measurable under the genuine full
heterogeneous product law, using only the two explicit generic DST inputs. -/
theorem aemeasurable_pairSwitchCount {K : ℕ} (p : Probe d) (m : Fin K → WeightedModel d)
    (q : OrderedCandidatePair K)
    (hLN : LusinNovikovInput (Fin K → Candidate d) (ProbeParameter p))
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    AEMeasurable (fun θ => ((pairSwitchSet (scores p θ) p.length q).encard : ℝ≥0∞))
      (Measure.pi fun k => (m k).joint) :=
  aemeasurable_pairSwitchCount_of_ae_not_exceptional p q _ hLN
    (ae_selectedPair_not_exceptional p m q hUP)

/-- The measurable regular count and the exact source count have the same
integral under the actual full parameter law. -/
theorem lintegral_regularVisibleCount_eq_pairSwitchCount {K : ℕ}
    (p : Probe d) (m : Fin K → WeightedModel d) (q : OrderedCandidatePair K)
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    (∫⁻ θ, sectionCount (regularVisibleGraph p q) θ ∂Measure.pi (fun k => (m k).joint)) =
      ∫⁻ θ, ((pairSwitchSet (scores p θ) p.length q).encard : ℝ≥0∞)
        ∂Measure.pi (fun k => (m k).joint) := by
  apply lintegral_congr_ae
  filter_upwards [ae_selectedPair_not_exceptional p m q hUP] with θ hθ
  exact regularVisibleCount_eq_pairSwitchCount p q θ hθ

/-- The exact pathwise pair partition now passes through expectation for the
actual random source counts, without a separate count-measurability premise. -/
theorem expectedSwitchCount_eq_source_pairCounts {K : ℕ}
    (p : Probe d) (m : Fin K → WeightedModel d)
    (hLN : LusinNovikovInput (Fin K → Candidate d) (ProbeParameter p))
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    expectedSwitchCount (Measure.pi fun k => (m k).joint) (scores p) p.length =
      ∑ q : OrderedCandidatePair K, ∫⁻ θ,
        ((pairSwitchSet (scores p θ) p.length q).encard : ℝ≥0∞)
          ∂Measure.pi (fun k => (m k).joint) := by
  exact expectedSwitchCount_eq_sum_pairSwitchSet _ _ _ (fun q =>
    aemeasurable_pairSwitchCount p m q hLN hUP)

end Paper35.VisibleCrossing

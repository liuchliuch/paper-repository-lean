import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Conditional absolute continuity avoids the singular arrangement

This file proves the measure-theoretic content of Lemma 4.2.  The history variable may
contain the whole pre-noise history and all oracle randomness.  The hypothesis is
absolute continuity of the actual regular conditional noise distribution, rather than
an assumed non-hitting property of the next iterate.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped MeasureTheory ENNReal

namespace Paper32

/-- The singular arrangement (3.4), on the paper's actual two-dimensional space. -/
def singularArrangement : Set (ℝ × ℝ) :=
  {z | z.1 = 0 ∨ z.2 = 0 ∨ |z.2| = 2 * |z.1|}

theorem measurableSet_singularArrangement : MeasurableSet singularArrangement := by
  exact ((measurableSet_eq_fun measurable_fst measurable_const).union
    ((measurableSet_eq_fun measurable_snd measurable_const).union
      (measurableSet_eq_fun (continuous_abs.measurable.comp measurable_snd)
        (measurable_const.mul (continuous_abs.measurable.comp measurable_fst)))))

/-- The two oblique branches in (3.4) are the lines `y = 2x` and `y = -2x`. -/
theorem mem_singularArrangement_iff (z : ℝ × ℝ) :
    z ∈ singularArrangement ↔
      z.1 = 0 ∨ z.2 = 0 ∨ z.2 = 2 * z.1 ∨ z.2 = -(2 * z.1) := by
  have h : |z.2| = 2 * |z.1| ↔ z.2 = 2 * z.1 ∨ z.2 = -(2 * z.1) := by
    have habs : |2 * z.1| = 2 * |z.1| := by rw [abs_mul]; norm_num
    rw [← habs, abs_eq_abs]
  exact or_congr_right (or_congr_right h)

private theorem volume_graph_eq_zero (f : ℝ → ℝ) (hf : Measurable f) :
    (volume : Measure (ℝ × ℝ)) {z | z.2 = f z.1} = 0 := by
  change (volume.prod volume) {z | z.2 = f z.1} = 0
  apply (Measure.measure_prod_null (μ := volume) (ν := volume)
    (measurableSet_eq_fun measurable_snd (hf.comp measurable_fst))).mpr
  filter_upwards [] with x
  change volume {y : ℝ | y = f x} = 0
  simp

/-- The finite union of axes and the lines `y = ±2x` has planar Lebesgue measure zero. -/
theorem volume_singularArrangement : (volume : Measure (ℝ × ℝ)) singularArrangement = 0 := by
  have hx : (volume : Measure (ℝ × ℝ)) {z | z.1 = 0} = 0 := by
    change (volume.prod volume) {z : ℝ × ℝ | z.1 = 0} = 0
    apply (Measure.measure_prod_null (μ := volume) (ν := volume)
      (measurableSet_eq_fun measurable_fst measurable_const)).mpr
    filter_upwards [show ∀ᵐ x : ℝ ∂volume, x ≠ 0 by simp [ae_iff]] with x hx
    simp [hx]
  have hset : singularArrangement = {z : ℝ × ℝ | z.1 = 0} ∪
      {z : ℝ × ℝ | z.2 = 0} ∪ {z : ℝ × ℝ | z.2 = 2 * z.1} ∪
      {z : ℝ × ℝ | z.2 = -(2 * z.1)} := by
    ext z
    simp only [mem_singularArrangement_iff, mem_union, mem_setOf_eq]
    tauto
  rw [hset]
  exact measure_union_null (measure_union_null (measure_union_null hx
    (volume_graph_eq_zero (fun _ => 0) measurable_const))
    (volume_graph_eq_zero (fun x => 2 * x) (by fun_prop)))
    (volume_graph_eq_zero (fun x => -(2 * x)) (by fun_prop))

/-- Every nonzero scalar homothety followed by a translation preserves Lebesgue nullity. -/
theorem volume_affine_preimage_null (b : ℝ × ℝ) {a : ℝ} (ha : a ≠ 0)
    {s : Set (ℝ × ℝ)} (hs : volume s = 0) :
    volume ((fun u : ℝ × ℝ => b - a • u) ⁻¹' s) = 0 := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) := by
    change Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod (volume : Measure ℝ))
    infer_instance
  have hsmul : Measure.QuasiMeasurePreserving (fun u : ℝ × ℝ => (-a) • u)
      volume volume := Measure.quasiMeasurePreserving_smul volume (neg_ne_zero.mpr ha)
  have hadd := (measurePreserving_add_left (volume : Measure (ℝ × ℝ)) b).quasiMeasurePreserving
  convert (hadd.comp hsmul).preimage_null hs using 1;
    simp [Function.comp_def, sub_eq_add_neg, neg_smul]

/-- In particular, the history-dependent affine preimage of the singular arrangement is null. -/
theorem volume_affine_preimage_singularArrangement (b : ℝ × ℝ) {a : ℝ} (ha : a ≠ 0) :
    volume ((fun u : ℝ × ℝ => b - a • u) ⁻¹' singularArrangement) = 0 :=
  volume_affine_preimage_null b ha volume_singularArrangement

/-- The direct conditional-hit condition in Remark 4.3 also suffices.  The set
inside the conditional measure depends on the realized pre-noise history. -/
theorem ae_affine_avoidance_of_condDistrib_null
    {Ω History : Type*} [MeasurableSpace Ω] [MeasurableSpace History]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (H : Ω → History) (ν : Ω → ℝ × ℝ)
    (z w : History → ℝ × ℝ) (a : ℝ)
    (hH : Measurable H) (hν : Measurable ν)
    (hz : Measurable z) (hw : Measurable w)
    (hnull : ∀ᵐ h ∂μ.map H, condDistrib ν H μ h
      ((fun u : ℝ × ℝ => z h - a • (w h + u)) ⁻¹' singularArrangement) = 0) :
    ∀ᵐ ω ∂μ, z (H ω) - a • (w (H ω) + ν ω) ∉ singularArrangement := by
  have hm : Measurable (fun p : History × (ℝ × ℝ) => z p.1 - a • (w p.1 + p.2)) := by
    fun_prop
  have hfiber : ∀ᵐ h ∂μ.map H, ∀ᵐ u ∂condDistrib ν H μ h,
      z h - a • (w h + u) ∉ singularArrangement := by
    filter_upwards [hnull] with h hh
    exact measure_eq_zero_iff_ae_notMem.mp hh
  have hjoint : ∀ᵐ p ∂(μ.map H ⊗ₘ condDistrib ν H μ),
      z p.1 - a • (w p.1 + p.2) ∉ singularArrangement :=
    Measure.ae_compProd_of_ae_ae (measurableSet_singularArrangement.preimage hm).compl hfiber
  rw [compProd_map_condDistrib hν.aemeasurable] at hjoint
  exact (ae_map_iff (hH.prodMk hν).aemeasurable
    (measurableSet_singularArrangement.preimage hm).compl).mp hjoint

/-- Conditional absolute continuity gives one-step avoidance for arbitrary pre-noise
history-dependent state and oracle.  `condDistrib ν H μ` is mathlib's regular
conditional distribution of the current noise given the history. -/
theorem ae_affine_avoidance_of_condDistrib
    {Ω History : Type*} [MeasurableSpace Ω] [MeasurableSpace History]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (H : Ω → History) (ν : Ω → ℝ × ℝ)
    (z w : History → ℝ × ℝ) (a : ℝ)
    (hH : Measurable H) (hν : Measurable ν)
    (hz : Measurable z) (hw : Measurable w) (ha : a ≠ 0)
    (hac : ∀ᵐ h ∂μ.map H, condDistrib ν H μ h ≪ (volume : Measure (ℝ × ℝ))) :
    ∀ᵐ ω ∂μ, z (H ω) - a • (w (H ω) + ν ω) ∉ singularArrangement := by
  have hnull (h : History) :
      volume ((fun u : ℝ × ℝ => z h - a • (w h + u)) ⁻¹' singularArrangement) = 0 := by
    have heq : (fun u : ℝ × ℝ => z h - a • (w h + u)) =
        (fun u : ℝ × ℝ => (z h - a • w h) - a • u) := by
      funext u
      rw [smul_add, sub_add_eq_sub_sub]
    rw [heq]
    exact volume_affine_preimage_singularArrangement (z h - a • w h) ha
  have hm : Measurable (fun p : History × (ℝ × ℝ) => z p.1 - a • (w p.1 + p.2)) := by
    fun_prop
  have hfiber : ∀ᵐ h ∂μ.map H, ∀ᵐ u ∂condDistrib ν H μ h,
      z h - a • (w h + u) ∉ singularArrangement := by
    filter_upwards [hac] with h hh
    exact measure_eq_zero_iff_ae_notMem.mp (hh (hnull h))
  have hjoint : ∀ᵐ p ∂(μ.map H ⊗ₘ condDistrib ν H μ),
      z p.1 - a • (w p.1 + p.2) ∉ singularArrangement :=
    Measure.ae_compProd_of_ae_ae (measurableSet_singularArrangement.preimage hm).compl hfiber
  rw [compProd_map_condDistrib hν.aemeasurable] at hjoint
  exact (ae_map_iff (hH.prodMk hν).aemeasurable
    (measurableSet_singularArrangement.preimage hm).compl).mp hjoint

/-- A formulation with conditional absolute continuity asserted almost surely on
the original sample space, as in (2.8). -/
theorem ae_affine_avoidance_of_condDistrib_path_ac
    {Ω History : Type*} [MeasurableSpace Ω] [MeasurableSpace History]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (H : Ω → History) (ν : Ω → ℝ × ℝ)
    (z w : History → ℝ × ℝ) (a : ℝ)
    (hH : Measurable H) (hν : Measurable ν)
    (hz : Measurable z) (hw : Measurable w) (ha : a ≠ 0)
    (hac : ∀ᵐ ω ∂μ, condDistrib ν H μ (H ω) ≪ (volume : Measure (ℝ × ℝ))) :
    ∀ᵐ ω ∂μ, z (H ω) - a • (w (H ω) + ν ω) ∉ singularArrangement := by
  have hm : Measurable (fun p : History × (ℝ × ℝ) => z p.1 - a • (w p.1 + p.2)) := by
    fun_prop
  have hmeas := Kernel.measurable_kernel_prodMk_left (κ := condDistrib ν H μ)
    (measurableSet_singularArrangement.preimage hm)
  apply ae_affine_avoidance_of_condDistrib_null μ H ν z w a hH hν hz hw
  apply (ae_map_iff hH.aemeasurable ((measurableSet_singleton (0 : ℝ≥0∞)).preimage hmeas)).mpr
  filter_upwards [hac] with ω hω
  apply hω
  have heq : (fun u : ℝ × ℝ => z (H ω) - a • (w (H ω) + u)) =
      (fun u : ℝ × ℝ => (z (H ω) - a • w (H ω)) - a • u) := by
    funext u
    rw [smul_add, sub_add_eq_sub_sub]
  change volume ((fun u : ℝ × ℝ => z (H ω) - a • (w (H ω) + u)) ⁻¹'
    singularArrangement) = 0
  rw [heq]
  exact volume_affine_preimage_singularArrangement (z (H ω) - a • w (H ω)) ha

/-- Countable intersection yields simultaneous avoidance at every positive time.
The oracle may depend on the complete pre-noise history at each step. -/
theorem ae_forall_positive_avoidance_of_condDistrib
    {Ω : Type*} {History : ℕ → Type*}
    [MeasurableSpace Ω] [∀ k, MeasurableSpace (History k)]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (H : ∀ k, Ω → History k) (ν : ℕ → Ω → ℝ × ℝ)
    (zHist wHist : ∀ k, History k → ℝ × ℝ) (a : ℕ → ℝ)
    (z : ℕ → Ω → ℝ × ℝ)
    (hH : ∀ k, Measurable (H k)) (hν : ∀ k, Measurable (ν k))
    (hz : ∀ k, Measurable (zHist k)) (hw : ∀ k, Measurable (wHist k))
    (ha : ∀ k, a k ≠ 0)
    (hac : ∀ k, ∀ᵐ h ∂μ.map (H k),
      condDistrib (ν k) (H k) μ h ≪ (volume : Measure (ℝ × ℝ)))
    (hrec : ∀ k, ∀ᵐ ω ∂μ,
      z (k + 1) ω = zHist k (H k ω) - a k • (wHist k (H k ω) + ν k ω)) :
    ∀ᵐ ω ∂μ, ∀ k ≥ 1, z k ω ∉ singularArrangement := by
  have hk (k : ℕ) : ∀ᵐ ω ∂μ, z (k + 1) ω ∉ singularArrangement := by
    filter_upwards [hrec k, ae_affine_avoidance_of_condDistrib μ (H k) (ν k)
      (zHist k) (wHist k) (a k) (hH k) (hν k) (hz k) (hw k) (ha k) (hac k)]
      with ω hrecω hav
    rwa [hrecω]
  filter_upwards [ae_all_iff.mpr hk] with ω hω
  intro k hpos
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hpos))
  exact hω j

/-- The outcome viewed only through a chosen pre-noise sigma field. -/
structure PreNoiseView (Ω : Type*) (m : MeasurableSpace Ω) where
  outcome : Ω

instance {Ω : Type*} (m : MeasurableSpace Ω) : MeasurableSpace (PreNoiseView Ω m) :=
  m.comap PreNoiseView.outcome

/-- Observation of the current outcome through the pre-noise sigma field. -/
def preNoiseObservation {Ω : Type*} (m : MeasurableSpace Ω) (ω : Ω) : PreNoiseView Ω m := ⟨ω⟩

/-- Conditioning on the observation means exactly conditioning on `m`. -/
theorem comap_preNoiseObservation {Ω : Type*} (m : MeasurableSpace Ω) :
    (inferInstance : MeasurableSpace (PreNoiseView Ω m)).comap (preNoiseObservation m) = m := by
  change (m.comap PreNoiseView.outcome).comap (preNoiseObservation m) = m
  rw [MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_id

theorem measurable_preNoiseObservation {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) :
    @Measurable Ω (PreNoiseView Ω m) mΩ inferInstance (preNoiseObservation m) := by
  apply Measurable.of_comap_le
  rw [comap_preNoiseObservation]
  exact hm

/-- Exact filtered-space form of Lemma 4.2.  Monotonicity of the sigma fields is
unnecessary for this lemma: only measurability before sampling the current noise is
used.  In particular, one may take `m k = ℱ k` for any filtration `ℱ`. -/
theorem ae_forall_positive_avoidance_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ k, m k ≤ mΩ)
    (z w noise : ℕ → Ω → ℝ × ℝ) (a : ℕ → ℝ)
    (hz : ∀ k, Measurable[m k] (z k)) (hw : ∀ k, Measurable[m k] (w k))
    (hnoise : ∀ k, Measurable (noise k)) (ha : ∀ k, a k ≠ 0)
    (hac : ∀ k, ∀ᵐ ω ∂μ,
      condDistrib (noise k) (preNoiseObservation (m k)) μ
        (preNoiseObservation (m k) ω) ≪ (volume : Measure (ℝ × ℝ)))
    (hrec : ∀ k, ∀ᵐ ω ∂μ, z (k + 1) ω = z k ω - a k • (w k ω + noise k ω)) :
    ∀ᵐ ω ∂μ, ∀ k ≥ 1, z k ω ∉ singularArrangement := by
  have hk (k : ℕ) : ∀ᵐ ω ∂μ, z (k + 1) ω ∉ singularArrangement := by
    have hv : @Measurable (PreNoiseView Ω (m k)) Ω _ (m k)
        PreNoiseView.outcome := Measurable.of_comap_le le_rfl
    have hav := ae_affine_avoidance_of_condDistrib_path_ac μ
      (preNoiseObservation (m k)) (noise k)
      (z k ∘ PreNoiseView.outcome) (w k ∘ PreNoiseView.outcome) (a k)
      (measurable_preNoiseObservation (m k) (hm k)) (hnoise k)
      ((hz k).comp hv) ((hw k).comp hv) (ha k) (hac k)
    filter_upwards [hrec k, hav] with ω hr hω
    rwa [hr]
  filter_upwards [ae_all_iff.mpr hk] with ω hω
  intro k hpos
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hpos))
  exact hω j

/-- The coordinatewise support bound in (2.8) and the open tilt box give the strict
error bound used in (4.3). -/
theorem error_coordinates_lt {noise tilt : ℝ × ℝ}
    (hnoise : |noise.1| ≤ 1 / 100 ∧ |noise.2| ≤ 1 / 100)
    (htilt : |tilt.1| < 1 / 100 ∧ |tilt.2| < 1 / 100) :
    |(noise - tilt).1| < 1 / 50 ∧ |(noise - tilt).2| < 1 / 50 := by
  constructor
  · calc
      |(noise - tilt).1| ≤ |noise.1| + |tilt.1| := by simpa using (abs_sub_le noise.1 0 tilt.1)
      _ < (1 : ℝ) / 100 + 1 / 100 := add_lt_add_of_le_of_lt hnoise.1 htilt.1
      _ = 1 / 50 := by norm_num
  · calc
      |(noise - tilt).2| ≤ |noise.2| + |tilt.2| := by simpa using (abs_sub_le noise.2 0 tilt.2)
      _ < (1 : ℝ) / 100 + 1 / 100 := add_lt_add_of_le_of_lt hnoise.2 htilt.2
      _ = 1 / 50 := by norm_num

/-- Coordinatewise almost-sure support bounds hold simultaneously over the countable
noise process, hence so does the strict tilted-error bound. -/
theorem ae_forall_error_coordinates_lt
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (noise : ℕ → Ω → ℝ × ℝ) (tilt : ℝ × ℝ)
    (hnoise : ∀ k, ∀ᵐ ω ∂μ,
      |(noise k ω).1| ≤ 1 / 100 ∧ |(noise k ω).2| ≤ 1 / 100)
    (htilt : |tilt.1| < 1 / 100 ∧ |tilt.2| < 1 / 100) :
    ∀ᵐ ω ∂μ, ∀ k,
      |(noise k ω - tilt).1| < 1 / 50 ∧ |(noise k ω - tilt).2| < 1 / 50 := by
  filter_upwards [ae_all_iff.mpr hnoise] with ω hω k
  exact error_coordinates_lt (hω k) htilt

/-- Independence of the current noise and the pre-noise history makes its actual
regular conditional law equal to its ordinary distribution. -/
theorem condDistrib_ae_eq_const_of_indep
    {Ω History E : Type*} [MeasurableSpace Ω] [MeasurableSpace History]
    [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (H : Ω → History) (noise : Ω → E)
    (hH : Measurable H) (hnoise : Measurable noise) (hindep : IndepFun H noise μ) :
    condDistrib noise H μ =ᵐ[μ.map H] Kernel.const History (μ.map noise) := by
  apply condDistrib_ae_eq_of_measure_eq_compProd H hnoise.aemeasurable
  rw [Measure.compProd_const]
  exact (indepFun_iff_map_prod_eq_prod_map_map hH.aemeasurable hnoise.aemeasurable).mp hindep

theorem condDistrib_absolutelyContinuous_of_indep
    {Ω History : Type*} [MeasurableSpace Ω] [MeasurableSpace History]
    (μ : Measure Ω) [IsFiniteMeasure μ] (H : Ω → History) (noise : Ω → ℝ × ℝ)
    (hH : Measurable H) (hnoise : Measurable noise) (hindep : IndepFun H noise μ)
    (hac : μ.map noise ≪ (volume : Measure (ℝ × ℝ))) :
    ∀ᵐ h ∂μ.map H, condDistrib noise H μ h ≪ (volume : Measure (ℝ × ℝ)) := by
  filter_upwards [condDistrib_ae_eq_const_of_indep μ H noise hH hnoise hindep] with h hh
  simpa only [hh, Kernel.const_apply] using hac

/-- The closed Euclidean disk, expressed in the paper's `(x,y)` coordinates. -/
def euclideanDisk (r : ℝ) : Set (ℝ × ℝ) := {z | z.1 ^ 2 + z.2 ^ 2 ≤ r ^ 2}

theorem measurableSet_euclideanDisk (r : ℝ) : MeasurableSet (euclideanDisk r) := by
  exact (isClosed_le (by fun_prop) continuous_const).measurableSet

theorem euclideanDisk_coordinate_bounds {r : ℝ} (hr : 0 ≤ r) {z : ℝ × ℝ}
    (hz : z ∈ euclideanDisk r) : |z.1| ≤ r ∧ |z.2| ≤ r := by
  constructor
  · apply (sq_le_sq₀ (abs_nonneg z.1) hr).mp
    rw [sq_abs]
    exact le_trans (by linarith [sq_nonneg z.2]) hz
  · apply (sq_le_sq₀ (abs_nonneg z.2) hr).mp
    rw [sq_abs]
    exact le_trans (by linarith [sq_nonneg z.1]) hz

private theorem volume_square (r : ℝ) :
    (volume : Measure (ℝ × ℝ)) (Icc (-r) r ×ˢ Icc (-r) r) =
      ENNReal.ofReal (2 * r) * ENNReal.ofReal (2 * r) := by
  change (volume.prod volume) (Icc (-r) r ×ˢ Icc (-r) r) = _
  simp only [Measure.prod_prod, Real.volume_Icc]
  congr 2 <;> ring

theorem volume_euclideanDisk_ne_top {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (ℝ × ℝ)) (euclideanDisk r) ≠ ∞ := by
  apply ne_top_of_le_ne_top (b := ENNReal.ofReal (2 * r) * ENNReal.ofReal (2 * r))
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · rw [← volume_square r]
    apply measure_mono
    intro z hz
    obtain ⟨hx, hy⟩ := euclideanDisk_coordinate_bounds hr hz
    exact ⟨abs_le.mp hx, abs_le.mp hy⟩

theorem volume_euclideanDisk_pos {r : ℝ} (hr : 0 < r) :
    0 < (volume : Measure (ℝ × ℝ)) (euclideanDisk r) := by
  have hs : Icc (-(r / 2)) (r / 2) ×ˢ Icc (-(r / 2)) (r / 2) ⊆ euclideanDisk r := by
    intro z hz
    have hx : |z.1| ≤ r / 2 := abs_le.mpr hz.1
    have hy : |z.2| ≤ r / 2 := abs_le.mpr hz.2
    have hx2 := (sq_le_sq₀ (abs_nonneg z.1) (by positivity : 0 ≤ r / 2)).mpr hx
    have hy2 := (sq_le_sq₀ (abs_nonneg z.2) (by positivity : 0 ≤ r / 2)).mpr hy
    rw [sq_abs] at hx2 hy2
    change z.1 ^ 2 + z.2 ^ 2 ≤ r ^ 2
    nlinarith [sq_nonneg r]
  apply lt_of_lt_of_le _ (measure_mono hs)
  rw [volume_square]
  positivity

/-- The actual uniform disk law, normalized restriction of planar Lebesgue measure. -/
noncomputable def uniformDiskLaw (r : ℝ) : Measure (ℝ × ℝ) :=
  ProbabilityTheory.cond volume (euclideanDisk r)

theorem uniformDiskLaw_isProbability {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (uniformDiskLaw r) :=
  cond_isProbabilityMeasure_of_finite (ne_of_gt (volume_euclideanDisk_pos hr))
    (volume_euclideanDisk_ne_top hr.le)

theorem uniformDiskLaw_absolutelyContinuous (r : ℝ) :
    uniformDiskLaw r ≪ (volume : Measure (ℝ × ℝ)) := cond_absolutelyContinuous

/-- A genuinely uniformly distributed disk perturbation has the coordinate support
bound needed in Theorem 2.2. -/
theorem ae_coordinate_bounds_of_uniformDisk
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (noise : Ω → ℝ × ℝ)
    (hnoise : Measurable noise) {r : ℝ} (hr : 0 ≤ r)
    (huniform : pdf.IsUniform noise (euclideanDisk r) μ volume) :
    ∀ᵐ ω ∂μ, |(noise ω).1| ≤ r ∧ |(noise ω).2| ≤ r := by
  have hmem : ∀ᵐ u ∂μ.map noise, u ∈ euclideanDisk r := by
    rw [huniform]
    exact ae_cond_mem (measurableSet_euclideanDisk r)
  filter_upwards [ae_of_ae_map hnoise.aemeasurable hmem] with ω hω
  exact euclideanDisk_coordinate_bounds hr hω

/-- Uniform disk noise independent of the full pre-noise history satisfies exactly
the conditional absolute continuity assumption in Lemma 4.2. -/
theorem condDistrib_absolutelyContinuous_of_indep_uniformDisk
    {Ω History : Type*} [MeasurableSpace Ω] [MeasurableSpace History]
    (μ : Measure Ω) [IsFiniteMeasure μ] (H : Ω → History) (noise : Ω → ℝ × ℝ)
    (hH : Measurable H) (hnoise : Measurable noise) (hindep : IndepFun H noise μ)
    {r : ℝ} (huniform : pdf.IsUniform noise (euclideanDisk r) μ volume) :
    ∀ᵐ h ∂μ.map H, condDistrib noise H μ h ≪ (volume : Measure (ℝ × ℝ)) :=
  condDistrib_absolutelyContinuous_of_indep μ H noise hH hnoise hindep
    huniform.absolutelyContinuous

/-- The finite vector of perturbations sampled strictly before time `k`. -/
def noisePast {Ω E : Type*} (noise : ℕ → Ω → E) (k : ℕ) (ω : Ω) :
    Fin k → E := fun i => noise i ω

theorem measurable_noisePast {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (noise : ℕ → Ω → E) (hnoise : ∀ k, Measurable (noise k)) (k : ℕ) :
    Measurable (noisePast noise k) := by
  exact measurable_pi_lambda _ (fun i => hnoise i)

/-- Genuine mutual independence implies that the present perturbation is independent
of the entire finite past vector, rather than merely pairwise independent. -/
theorem indepFun_noisePast_current {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (noise : ℕ → Ω → E)
    (hnoise : ∀ k, Measurable (noise k)) (hiid : iIndepFun noise μ) (k : ℕ) :
    IndepFun (noisePast noise k) (noise k) μ := by
  have hd : Disjoint (Finset.range k) {k} := by simp
  have hi := hiid.indepFun_finset (Finset.range k) {k} hd hnoise
  have hleft : Measurable (fun f : (i : Finset.range k) → E =>
      fun j : Fin k => f ⟨j, Finset.mem_range.mpr j.isLt⟩) := by fun_prop
  have hright : Measurable (fun f : (i : ({k} : Finset ℕ)) → E =>
      f ⟨k, by simp⟩) := by fun_prop
  exact hi.comp hleft hright

/-- The natural pre-noise sigma field generated by the finite past. -/
def noisePastSigma {Ω E : Type*} [MeasurableSpace E] (noise : ℕ → Ω → E) (k : ℕ) : MeasurableSpace Ω :=
  (inferInstance : MeasurableSpace (Fin k → E)).comap (noisePast noise k)

/-- An observation through the sigma field generated by `H` carries exactly the same
independence from the present noise as `H` itself. -/
theorem indepFun_preNoiseObservation_of_indep
    {Ω History E : Type*} [MeasurableSpace Ω] [mHistory : MeasurableSpace History]
    [MeasurableSpace E]
    (μ : Measure Ω) (H : Ω → History) (noise : Ω → E)
    (hindep : IndepFun H noise μ) :
    IndepFun (preNoiseObservation (mHistory.comap H)) noise μ := by
  rw [IndepFun_iff_Indep, comap_preNoiseObservation]
  exact (IndepFun_iff_Indep H noise μ).mp hindep

/-- Iid uniform disk perturbations satisfy the conditional absolute continuity
hypothesis on the actual natural pre-noise sigma field. -/
theorem iid_uniformDisk_conditional_absolutelyContinuous
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (noise : ℕ → Ω → ℝ × ℝ) (hnoise : ∀ k, Measurable (noise k))
    (hiid : iIndepFun noise μ) {r : ℝ}
    (huniform : ∀ k, pdf.IsUniform (noise k) (euclideanDisk r) μ volume) :
    ∀ k, ∀ᵐ ω ∂μ,
      condDistrib (noise k) (preNoiseObservation (noisePastSigma noise k)) μ
        (preNoiseObservation (noisePastSigma noise k) ω) ≪ (volume : Measure (ℝ × ℝ)) := by
  intro k
  have hobs := measurable_preNoiseObservation (noisePastSigma noise k)
    (measurable_noisePast noise hnoise k).comap_le
  have hi := indepFun_preNoiseObservation_of_indep μ (noisePast noise k) (noise k)
    (indepFun_noisePast_current μ noise hnoise hiid k)
  have hcond := condDistrib_absolutelyContinuous_of_indep_uniformDisk μ
    (preNoiseObservation (noisePastSigma noise k)) (noise k) hobs (hnoise k) hi (huniform k)
  exact ae_of_ae_map hobs.aemeasurable hcond

/-- The support bound for a countable uniform disk noise process. -/
theorem ae_forall_uniformDisk_coordinate_bounds
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (noise : ℕ → Ω → ℝ × ℝ) (hnoise : ∀ k, Measurable (noise k))
    {r : ℝ} (hr : 0 ≤ r)
    (huniform : ∀ k, pdf.IsUniform (noise k) (euclideanDisk r) μ volume) :
    ∀ᵐ ω ∂μ, ∀ k, |(noise k ω).1| ≤ r ∧ |(noise k ω).2| ≤ r :=
  ae_all_iff.mpr (fun k => ae_coordinate_bounds_of_uniformDisk μ (noise k) (hnoise k) hr (huniform k))

/-- Absolute continuity of a joint law with respect to product Lebesgue measure
implies absolute continuity of its first two-dimensional marginal.  The coordinates
need not be independent. -/
theorem absolutelyContinuous_fst_of_prod
    {E : Type*} [MeasurableSpace E] (ρ : Measure E)
    (μ : Measure ((ℝ × ℝ) × E))
    (hac : μ ≪ (volume : Measure (ℝ × ℝ)).prod ρ) :
    μ.map Prod.fst ≪ (volume : Measure (ℝ × ℝ)) := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hs0
  rw [Measure.map_apply measurable_fst hs]
  apply hac
  rw [show (Prod.fst : (ℝ × ℝ) × E → ℝ × ℝ) ⁻¹' s = s ×ˢ univ by ext; simp]
  apply le_antisymm _ (zero_le _)
  simpa only [hs0, zero_mul] using
    (Measure.prod_prod_le (μ := (volume : Measure (ℝ × ℝ))) (ν := ρ) s univ)

/-- In particular a uniform law on a Euclidean ball in a separable coordinate
embedding has an absolutely continuous first planar marginal; the result holds for
any measurable support set and therefore does not require coordinate independence. -/
theorem uniform_first_marginal_absolutelyContinuous
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (ρ : Measure E) (noise : Ω → (ℝ × ℝ) × E)
    (hnoise : Measurable noise) (s : Set ((ℝ × ℝ) × E))
    (huniform : pdf.IsUniform noise s μ ((volume : Measure (ℝ × ℝ)).prod ρ)) :
    μ.map (fun ω => (noise ω).1) ≪ (volume : Measure (ℝ × ℝ)) := by
  have h := absolutelyContinuous_fst_of_prod ρ (μ.map noise) huniform.absolutelyContinuous
  rwa [Measure.map_map measurable_fst hnoise] at h

end Paper32

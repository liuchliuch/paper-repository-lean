import Paper35.SourceModel
import Paper35.Assembly
import Paper35.Crossing
import Paper35.VisibleCrossing
import Paper35.VisibilityKernel
import Paper35.Deep
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace Paper35.Heterogeneous
open Source Source.WeightedModel

/-- The mutually independent, potentially different candidate laws in Theorem 2.6.
The constant envelope and the first moment are exactly its source hypotheses. -/
structure Model (d K : ℕ) where
  candidate : Fin K → WeightedModel d
  B : Fin K → ℝ≥0
  constantEnvelope : ∀ i, ∀ᵐ w ∂(candidate i).weights, (candidate i).b₀ w = B i
  firstMoment : ∀ i, Integrable (fun w => ‖w‖) (candidate i).weights

namespace Model
variable {d K : ℕ}
def joint (m : Model d K) : Measure (Fin K → Candidate d) :=
  Measure.pi (fun i => (m.candidate i).joint)
instance (m : Model d K) : IsProbabilityMeasure m.joint := by
  unfold joint
  infer_instance

def expectedCount (m : Model d K) (p : Probe d) : ℝ≥0∞ :=
  expectedSwitchCount m.joint (WeightedModel.scores p) p.length

def mass (m : Model d K) (x u : Space d) (y : ℝ) (i : Fin K) : ℝ≥0∞ :=
  (m.candidate i).slopeSlice x u y univ

def centeredSlice (m : Model d K) (x u : Space d) (y c : ℝ) (i : Fin K) : ℝ≥0∞ :=
  ∫⁻ a, ENNReal.ofReal |a-c| ∂(m.candidate i).slopeSlice x u y

def centeredMoment (m : Model d K) (u : Space d) (c : ℝ) (i : Fin K) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal |inner ℝ w u-c| ∂(m.candidate i).weights

def kernel (m : Model d K) (x u : Space d) (y : ℝ) (i j : Fin K) : ℝ≥0∞ :=
  ∫⁻ a, ∫⁻ b, ENNReal.ofReal |a-b|
    ∂(m.candidate j).slopeSlice x u y ∂(m.candidate i).slopeSlice x u y

def visibility (m : Model d K) (x : Space d) (y : ℝ) (i j : Fin K) : ℝ≥0∞ :=
  ∏ k ∈ (Finset.univ.erase i).erase j, (m.candidate k).scoreCDF x y

/-- Triangle inequality for the actual heterogeneous slope-height slice measures (4.11). -/
theorem kernel_le_centered (m : Model d K) (x u : Space d) (y c : ℝ) (i j : Fin K) :
    m.kernel x u y i j ≤ m.centeredSlice x u y c i * m.mass x u y j +
      m.mass x u y i * m.centeredSlice x u y c j := by
  let ν := (m.candidate i).slopeSlice x u y
  let η := (m.candidate j).slopeSlice x u y
  have ha : Measurable (fun a : ℝ => ENNReal.ofReal |a-c|) := by fun_prop
  change (∫⁻ a, ∫⁻ b, ENNReal.ofReal |a-b| ∂η ∂ν) ≤ _
  calc
    _ ≤ ∫⁻ a, ∫⁻ b, ENNReal.ofReal |a-c| + ENNReal.ofReal |b-c| ∂η ∂ν := by
      apply lintegral_mono
      intro a
      apply lintegral_mono
      intro b
      change ENNReal.ofReal |a-b| ≤ ENNReal.ofReal |a-c| + ENNReal.ofReal |b-c|
      rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      simpa [abs_sub_comm] using abs_sub_le a c b
    _ = _ := by
      simp_rw [lintegral_add_left measurable_const, lintegral_const]
      rw [lintegral_add_left (ha.mul_const (η univ)), lintegral_mul_const _ ha]
      simp only [Model.centeredSlice, Model.mass, ν, η]
      rw [lintegral_const]
      simp only [mul_comm]

theorem centeredSlice_le_envelope (m : Model d K) (x u : Space d) (y c : ℝ) (i : Fin K) :
    m.centeredSlice x u y c i ≤ (m.B i : ℝ≥0∞) * m.centeredMoment u c i := by
  have hp : Measurable (fun w : Space d => inner ℝ w u) := by fun_prop
  have hg : Measurable (fun w => (m.candidate i).g w (y-inner ℝ w x)) :=
    (m.candidate i).measurable_g.comp (measurable_id.prodMk (measurable_const.sub (by fun_prop)))
  unfold centeredSlice WeightedModel.slopeSlice
  rw [lintegral_map (by fun_prop) hp,
    lintegral_withDensity_eq_lintegral_mul _ hg (by fun_prop)]
  calc
    _ ≤ ∫⁻ w, (m.B i : ℝ≥0∞) * ENNReal.ofReal |inner ℝ w u-c| ∂(m.candidate i).weights := by
      apply lintegral_mono_ae
      filter_upwards [(m.candidate i).bound, m.constantEnvelope i] with w hw hb
      apply mul_le_mul_right'
      rw [← hb]
      exact hw _
    _ = _ := lintegral_const_mul _ (by fun_prop)

theorem visibility_comm (m : Model d K) (x : Space d) (y : ℝ) (i j : Fin K) :
    m.visibility x y i j = m.visibility x y j i := by
  simp only [visibility, Finset.erase_right_comm]

/-- The slice mass is precisely the actual score density, independently of the direction. -/
theorem mass_eq_scoreDensity (m : Model d K) (x u : Space d) (y : ℝ) (i : Fin K) :
    m.mass x u y i = VisibleCrossing.scoreDensity (m.candidate i) x y := by
  unfold mass WeightedModel.slopeSlice
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp only [preimage_univ]
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rfl

def pairIntensity (m : Model d K) (x u : Space d) (y : ℝ) : ℝ≥0∞ :=
  ∑ i, ∑ j, if i < j then m.visibility x y i j * m.kernel x u y i j else 0

/-- The derivative density of the product of the other candidates' CDFs. -/
def leaveOneDensity (m : Model d K) (x u : Space d) (y : ℝ) (i : Fin K) : ℝ≥0∞ :=
  ∑ j, if i ≠ j then m.mass x u y j * m.visibility x y i j else 0

end Model

/-- The purely algebraic orientation step in (4.12). Every unordered pair
contributes its two orientations, so each candidate is charged once. -/
theorem sum_orientations {K : ℕ} (a : Fin K → Fin K → ℝ≥0∞) :
    (∑ i, ∑ j, if i < j then (a i j + a j i) else 0) =
      ∑ i, ∑ j, if i ≠ j then a i j else 0 := by
  classical
  have hsplit (i j : Fin K) :
      (if i < j then a i j + a j i else 0) =
        (if i < j then a i j else 0) + (if i < j then a j i else 0) := by
    split_ifs <;> simp
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if i < j then a j i else 0)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [hij, hij.ne, hij.not_gt]
  · subst j
    simp
  · simp [hij, hij.ne', hij.not_gt]

namespace Model
variable {d K : ℕ}

/-- The source-oriented pair sum (4.12), proved directly on the actual slice measures. -/
theorem pairIntensity_le_oriented (m : Model d K) (x u : Space d) (y c : ℝ) :
    m.pairIntensity x u y ≤ ∑ i, m.centeredSlice x u y c i * m.leaveOneDensity x u y i := by
  classical
  let a : Fin K → Fin K → ℝ≥0∞ := fun i j =>
    m.centeredSlice x u y c i * (m.mass x u y j * m.visibility x y i j)
  calc
    _ ≤ ∑ i, ∑ j, if i < j then (a i j + a j i) else 0 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i < j
      · simp only [if_pos hij]
        have h := mul_le_mul_left' (m.kernel_le_centered x u y c i j) (m.visibility x y i j)
        convert h using 1
        simp only [a, m.visibility_comm x y j i, mul_add]
        ring
      · simp only [if_neg hij, le_refl]
    _ = ∑ i, ∑ j, if i ≠ j then a i j else 0 := sum_orientations a
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [leaveOneDensity, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i ≠ j <;> simp [hij, a]

/-- The conditional-density envelope yields a candidate-additive integrand. -/
theorem pairIntensity_le_envelopes (m : Model d K) (x u : Space d) (y c : ℝ) :
    m.pairIntensity x u y ≤
      ∑ i, ((m.B i : ℝ≥0∞) * m.centeredMoment u c i) * m.leaveOneDensity x u y i := by
  apply (m.pairIntensity_le_oriented x u y c).trans
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_right' (m.centeredSlice_le_envelope x u y c i) _

end Model

/-- Classical absolutely-continuous product/FTC input, in density form.
For every finite nonempty set of independent real probability densities, the
sum of the leave-one-out CDF products times the selected density has mass one.
This is the usual density formula for the maximum, obtained by the finite
product rule and the Lebesgue fundamental theorem of calculus (Folland,
Real Analysis, 2nd ed., Corollary 3.33 and Theorem 3.35). This input contains
no switching, slopes, Maxout, or proposed inequality. -/
def MaxDensityFormula : Prop :=
  ∀ {n : ℕ} (h : Fin n → ℝ → ℝ≥0∞),
    (∀ i, Measurable (h i)) → (∀ i, (∫⁻ y, h i y) = 1) →
      ∀ t : Finset (Fin n), t.Nonempty →
        (∫⁻ y, ∑ j ∈ t, h j y * ∏ k ∈ t.erase j,
          (volume.withDensity (h k)) (Iic y)) = 1

namespace Model
variable {d K : ℕ}

theorem leaveOneDensity_normalized (ext : MaxDensityFormula) (m : Model d K)
    (hK : 2 ≤ K) (x u : Space d) (i : Fin K) :
    (∫⁻ y, m.leaveOneDensity x u y i) = 1 := by
  classical
  have ht : (Finset.univ.erase i).Nonempty := by
    apply Finset.card_pos.mp
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  have H := ext (fun j => VisibleCrossing.scoreDensity (m.candidate j) x)
    (fun j => VisibleCrossing.measurable_scoreDensity _ _)
    (fun j => VisibleCrossing.scoreDensity_normalized _ _) (Finset.univ.erase i) ht
  convert H using 1
  apply lintegral_congr
  intro y
  rw [leaveOneDensity, ← Finset.sum_filter]
  have hs : Finset.univ.filter (fun j => i ≠ j) = Finset.univ.erase i := by
    ext j
    simp [ne_comm]
  rw [hs]
  apply Finset.sum_congr rfl
  intro j hj
  rw [m.mass_eq_scoreDensity]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  exact VisibleCrossing.scoreCDF_eq_densityLaw _ _ _

theorem measurable_leaveOneDensity (m : Model d K) (x u : Space d) (i : Fin K) :
    Measurable (fun y => m.leaveOneDensity x u y i) := by
  classical
  unfold leaveOneDensity
  apply Finset.measurable_sum
  intro j _
  by_cases hij : i ≠ j
  · have hm : Measurable (fun y => m.mass x u y j) := by
      simp_rw [m.mass_eq_scoreDensity]
      exact VisibleCrossing.measurable_scoreDensity _ _
    have hprod : Measurable (fun y => m.visibility x y i j) := by
      unfold visibility
      apply Finset.measurable_prod
      intro k _
      exact VisibilityKernel.measurable_scoreCDF (m.candidate k) x
    simpa only [if_pos hij] using hm.mul hprod
  · simpa only [if_neg hij] using (measurable_const : Measurable (fun _ : ℝ => (0 : ℝ≥0∞)))

/-- Candidate-additive visibility estimate for every common projected reference c.
The sole external input is the standard maximum-density normalization. -/
theorem integrated_pairIntensity_le (ext : MaxDensityFormula) (m : Model d K)
    (hK : 2 ≤ K) (x u : Space d) (c : ℝ) :
    (∫⁻ y, m.pairIntensity x u y) ≤
      ∑ i, (m.B i : ℝ≥0∞) * m.centeredMoment u c i := by
  calc
    _ ≤ ∫⁻ y, ∑ i, ((m.B i : ℝ≥0∞) * m.centeredMoment u c i) *
        m.leaveOneDensity x u y i :=
      lintegral_mono (fun y => m.pairIntensity_le_envelopes x u y c)
    _ = ∑ i, ∫⁻ y, ((m.B i : ℝ≥0∞) * m.centeredMoment u c i) *
        m.leaveOneDensity x u y i := by
      rw [lintegral_finset_sum _ (fun i _ =>
        (m.measurable_leaveOneDensity x u i).const_mul _)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [lintegral_const_mul _ (m.measurable_leaveOneDensity x u i),
        m.leaveOneDensity_normalized ext hK x u i, mul_one]

/-- The optimal common reference can be chosen separately at each tangent. -/
theorem integrated_pairIntensity_le_iInf (ext : MaxDensityFormula) (m : Model d K)
    (hK : 2 ≤ K) (x u : Space d) :
    (∫⁻ y, m.pairIntensity x u y) ≤
      ⨅ c : ℝ, ∑ i, (m.B i : ℝ≥0∞) * m.centeredMoment u c i :=
  le_iInf (fun c => m.integrated_pairIntensity_le ext hK x u c)

/-- The covariance estimate (2.13) for an actual scalar projection.
Square integrability is precisely the optional finite covariance hypothesis. -/
theorem centeredMoment_le_covariance (m : Model d K) (u : Space d) (c : ℝ) (i : Fin K)
    (hW : MemLp (fun w => w) 2 (m.candidate i).weights) :
    m.centeredMoment u c i ≤ ENNReal.ofReal (Real.sqrt
      (ProbabilityTheory.variance (fun w => inner ℝ w u) (m.candidate i).weights +
        ((∫ w, inner ℝ w u ∂(m.candidate i).weights)-c)^2)) := by
  let μ := (m.candidate i).weights
  letI : IsProbabilityMeasure μ := (m.candidate i).probability
  let X : Space d → ℝ := fun w => inner ℝ w u
  have hX : MemLp X 2 μ := by
    have ht : MemLp (fun w : Space d => inner ℝ u w) 2 μ := hW.const_inner u
    simpa only [X, real_inner_comm] using ht
  have hY : MemLp (fun w => X w-c) 2 μ := hX.sub (memLp_const c)
  have hA : MemLp (fun w => |X w-c|) 2 μ := hY.norm
  have hsq := Paper35.Deep.mean_square_le_second_moment μ (fun w => |X w-c|) hA
  have hvar := ProbabilityTheory.variance_eq_sub hY
  simp only [Pi.pow_apply] at hvar
  have hmean : (∫ w, X w-c ∂μ) = (∫ w, X w ∂μ)-c := by
    rw [integral_sub (hX.integrable (by norm_num)) (integrable_const c), integral_const]
    simp
  have heq : (∫ w, |X w-c|^2 ∂μ) =
      ProbabilityTheory.variance X μ + ((∫ w, X w ∂μ)-c)^2 := by
    simp_rw [sq_abs]
    rw [← hmean, ← ProbabilityTheory.variance_sub_const hX.aestronglyMeasurable c]
    linarith [hvar]
  rw [heq] at hsq
  apply le_trans ?_ (ENNReal.ofReal_le_ofReal (Real.le_sqrt_of_sq_le hsq))
  unfold centeredMoment
  change (∫⁻ w, ENNReal.ofReal |X w-c| ∂μ) ≤ ENNReal.ofReal (∫ w, |X w-c| ∂μ)
  exact le_of_eq (ofReal_integral_eq_lintegral_ofReal (hA.integrable (by norm_num))
    (Filter.Eventually.of_forall (fun w => abs_nonneg _))).symm

end Model

/-- The original heterogeneous visible-crossing identity (3.5), retained as
an internal proof dependency, not labelled as an external classical theorem. -/
def ExactCrossingClaim (d K : ℕ) : Prop :=
  ∀ (m : Model d K) (p : Probe d), m.expectedCount p =
    ∫⁻ s in Icc 0 p.length, ∫⁻ y, m.pairIntensity (p.curve s) (deriv p.curve s) y

/-- Theorem 2.6 follows from the actual visible-crossing identity and the
classical maximum-density formula. All candidate-additive estimates above
are proved, rather than assumptions of this theorem. -/
theorem expectedCount_le_common_reference {d K : ℕ} (ext : MaxDensityFormula)
    (hcross : ExactCrossingClaim d K) (m : Model d K) (hK : 2 ≤ K) (p : Probe d) :
    m.expectedCount p ≤ ∫⁻ s in Icc 0 p.length,
      ⨅ c : ℝ, ∑ i, (m.B i : ℝ≥0∞) * m.centeredMoment (deriv p.curve s) c i := by
  rw [hcross m p]
  exact lintegral_mono (fun s => m.integrated_pairIntensity_le_iInf ext hK _ _)

/-- The optional covariance improvement (2.13), with the same common scalar c. -/
theorem common_reference_covariance {d K : ℕ} (m : Model d K) (u : Space d)
    (hW : ∀ i, MemLp (fun w => w) 2 (m.candidate i).weights) :
    (⨅ c : ℝ, ∑ i, (m.B i : ℝ≥0∞) * m.centeredMoment u c i) ≤
      ⨅ c : ℝ, ∑ i, (m.B i : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt
        (ProbabilityTheory.variance (fun w => inner ℝ w u) (m.candidate i).weights +
          ((∫ w, inner ℝ w u ∂(m.candidate i).weights)-c)^2)) := by
  apply iInf_mono
  intro c
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_left' (m.centeredMoment_le_covariance u c i (hW i)) _

/-- An arclength probe has speed at most one at every interior parameter;
deriv is zero at nondifferentiable points, so no extra differentiability
hypothesis is needed for this upper bound. -/
theorem probe_speed_le_one {d : ℕ} (p : Probe d) {s : ℝ} (hs : s ∈ Ioo 0 p.length) :
    ‖deriv p.curve s‖ ≤ 1 :=
  norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hs.1 hs.2) p.lipschitz

namespace Model
variable {d K : ℕ}

def firstMomentBound (m : Model d K) : ℝ≥0∞ :=
  ∑ i, (m.B i : ℝ≥0∞) * ∫⁻ w, ENNReal.ofReal ‖w‖ ∂(m.candidate i).weights

theorem firstMomentBound_ne_top (m : Model d K) : m.firstMomentBound ≠ ∞ := by
  apply ENNReal.sum_ne_top.mpr
  intro i _
  apply ENNReal.mul_ne_top ENNReal.coe_ne_top
  rw [← ofReal_integral_eq_lintegral_ofReal (m.firstMoment i)
    (Filter.Eventually.of_forall (fun w => norm_nonneg w))]
  exact ENNReal.ofReal_ne_top

theorem centeredMoment_zero_le_norm (m : Model d K) (u : Space d) (hu : ‖u‖ ≤ 1) (i : Fin K) :
    m.centeredMoment u 0 i ≤ ∫⁻ w, ENNReal.ofReal ‖w‖ ∂(m.candidate i).weights := by
  apply lintegral_mono
  intro w
  simp only [sub_zero]
  apply ENNReal.ofReal_le_ofReal
  calc
    |inner ℝ w u| ≤ ‖w‖ * ‖u‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left hu (norm_nonneg w)
    _ = ‖w‖ := mul_one _

/-- The finite-first-moment assertion following Lemma 3.1, for the
heterogeneous source hypotheses, once its actual crossing identity is used. -/
theorem expectedCount_finite (ext : MaxDensityFormula) (hcross : ExactCrossingClaim d K)
    (m : Model d K) (hK : 2 ≤ K) (p : Probe d) : m.expectedCount p < ∞ := by
  have hb : m.expectedCount p ≤ ENNReal.ofReal p.length * m.firstMomentBound := by
    rw [hcross m p, ← restrict_Ioo_eq_restrict_Icc]
    calc
      _ ≤ ∫⁻ s in Ioo 0 p.length, m.firstMomentBound := by
        apply setLIntegral_mono' measurableSet_Ioo
        intro s hs
        apply (m.integrated_pairIntensity_le ext hK (p.curve s) (deriv p.curve s) 0).trans
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_left' (m.centeredMoment_zero_le_norm _ (probe_speed_le_one p hs) i) _
      _ = _ := by simp [Real.volume_Ioo, mul_comm]
  exact lt_of_le_of_lt hb (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lt_top_iff_ne_top.mpr m.firstMomentBound_ne_top))
end Model

end Paper35.Heterogeneous

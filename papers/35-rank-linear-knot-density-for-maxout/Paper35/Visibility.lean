import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The density-splitting argument in Lemma 4.1

This file proves the sharp opposite-mass estimate (4.7)--(4.8), including
its measure-theoretic application to conditional density kernels, and
the scalar and Gini layer-cake identities (also without first moments).
The score-CDF integration and the final assembly for the original
visible-crossing kernel R(y) are not asserted here.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Paper35.Visibility

/-- The sharp balancing step in (4.7)--(4.8). -/
theorem opposite_mass_bound {B p T U H : ℝ}
    (hB : 0 ≤ B) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hleft : H ≤ B * p * (T - U))
    (hright : H ≤ B * (1 - p) * U) :
    H ≤ B * T * p * (1 - p) := by
  by_cases hU : U ≤ p * T
  · calc
      H ≤ B * (1 - p) * U := hright
      _ ≤ B * (1 - p) * (p * T) :=
        mul_le_mul_of_nonneg_left hU (mul_nonneg hB (sub_nonneg.mpr hp1))
      _ = B * T * p * (1 - p) := by ring
  · have hTU : T - U ≤ (1 - p) * T := by linarith
    calc
      H ≤ B * p * (T - U) := hleft
      _ ≤ B * p * ((1 - p) * T) :=
        mul_le_mul_of_nonneg_left hTU (mul_nonneg hB hp0)
      _ = B * T * p * (1 - p) := by ring

/-- At the CDF normalization `T = 1/(n+1)`, the sharp factor is `1/(n+1)`. -/
theorem opposite_mass_rank_bound {B p U H : ℝ} (n : ℕ)
    (hB : 0 ≤ B) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hleft : H ≤ B * p * ((1 / (n + 1 : ℝ)) - U))
    (hright : H ≤ B * (1 - p) * U) :
    H ≤ B / (n + 1 : ℝ) * p * (1 - p) := by
  simpa [div_eq_mul_inv] using opposite_mass_bound hB hp0 hp1 hleft hright

/-- Opposite-side conditional score masses. The kernel is evaluated at the
fixed score height before applying this definition. -/
def upperMass {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A g : α → ℝ) (r : ℝ) : ℝ :=
  ∫ w in {w | r < A w}, g w ∂μ

def lowerMass {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A g : α → ℝ) (r : ℝ) : ℝ :=
  ∫ w in {w | A w ≤ r}, g w ∂μ

/-- The tilted tail is the envelope-weighted tail normalized by the total
envelope mass.  Thus `B * tiltedTail` is exactly the envelope mass of the
upper set, rather than an arbitrary parameter in the sharp estimate. -/
def tiltedTail {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A b : α → ℝ) (B r : ℝ) : ℝ :=
  upperMass μ A b r / B

/-- The actual envelope tilt from (2.5), represented by a measure with
Radon--Nikodym density `b/B`. -/
def tiltedLaw {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (b : α → ℝ) (B : ℝ) : Measure α :=
  μ.withDensity (fun w => ENNReal.ofReal (b w / B))

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Normalizing the envelope produces an actual probability law. -/
theorem tiltedLaw_isProbability {b : α → ℝ} {B : ℝ}
    (hb : Integrable b μ) (hb0 : ∀ w, 0 ≤ b w)
    (hB : 0 < B) (hBint : ∫ w, b w ∂μ = B) :
    IsProbabilityMeasure (tiltedLaw μ b B) := by
  constructor
  rw [tiltedLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (hb.div_const B)
    (Filter.Eventually.of_forall (fun w => div_nonneg (hb0 w) hB.le))]
  simp [integral_div, hBint, hB.ne']

/-- The normalized envelope tail is precisely the upper-tail probability
under the tilted law, as required by (4.2) and (4.5). -/
theorem tiltedTail_eq_tiltedLaw_real {A b : α → ℝ} {B : ℝ}
    (hA : Measurable A) (hb : Measurable b) (hb0 : ∀ w, 0 ≤ b w)
    (hB : 0 < B) (r : ℝ) :
    tiltedTail μ A b B r = (tiltedLaw μ b B).real {w | r < A w} := by
  have hs : MeasurableSet {w | r < A w} := measurableSet_lt measurable_const hA
  rw [← setIntegral_one_eq_measureReal]
  unfold tiltedLaw
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    ((hb.div_const B).ennreal_ofReal.aemeasurable.restrict)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (fun _ => (1 : ℝ)) hs]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (hb0 _) hB.le), smul_eq_mul, mul_one]
  rw [integral_div]
  rfl


lemma upperMass_add_lowerMass {A g : α → ℝ} (hA : Measurable A)
    (hg : Integrable g μ) (r : ℝ) :
    upperMass μ A g r + lowerMass μ A g r = ∫ w, g w ∂μ := by
  have hs : MeasurableSet {w | r < A w} := measurableSet_lt measurable_const hA
  have hc : {w | r < A w}ᶜ = {w | A w ≤ r} := by ext w; simp
  simpa [upperMass, lowerMass, hc] using integral_add_compl hs hg

lemma upperMass_nonneg {A g : α → ℝ} (hg : ∀ w, 0 ≤ g w) (r : ℝ) :
    0 ≤ upperMass μ A g r := integral_nonneg hg

lemma lowerMass_nonneg {A g : α → ℝ} (hg : ∀ w, 0 ≤ g w) (r : ℝ) :
    0 ≤ lowerMass μ A g r := integral_nonneg hg

/-- A density kernel dominated by an integrable envelope is integrable. -/
lemma kernel_integrable {g b : α → ℝ} (hb : Integrable b μ)
    (hgm : AEStronglyMeasurable g μ) (hg0 : ∀ᵐ w ∂μ, 0 ≤ g w)
    (hgb : ∀ᵐ w ∂μ, g w ≤ b w) : Integrable g μ := by
  apply hb.mono' hgm
  filter_upwards [hg0, hgb] with w h0 hle
  simpa [Real.norm_eq_abs, abs_of_nonneg h0] using hle

/-- The actual density-kernel bound on the upper projected-slope set. -/
lemma upperMass_le_envelope {A g b : α → ℝ}
    (hg : Integrable g μ) (hb : Integrable b μ)
    (hgb : ∀ᵐ w ∂μ, g w ≤ b w) (r : ℝ) :
    upperMass μ A g r ≤ upperMass μ A b r := by
  exact integral_mono_ae hg.integrableOn hb.integrableOn (ae_restrict_of_ae hgb)

lemma lowerMass_le_envelope {A g b : α → ℝ}
    (hg : Integrable g μ) (hb : Integrable b μ)
    (hgb : ∀ᵐ w ∂μ, g w ≤ b w) (r : ℝ) :
    lowerMass μ A g r ≤ lowerMass μ A b r := by
  exact integral_mono_ae hg.integrableOn hb.integrableOn (ae_restrict_of_ae hgb)

/-- Both bounds (4.5), with a genuine normalized envelope-weighted tail. -/
theorem density_split_bounds {A g b : α → ℝ} {B : ℝ}
    (hA : Measurable A) (hg : Integrable g μ) (hb : Integrable b μ)
    (hb0 : ∀ w, 0 ≤ b w) (hgb : ∀ᵐ w ∂μ, g w ≤ b w)
    (hB : 0 < B) (hBint : ∫ w, b w ∂μ = B) (r : ℝ) :
    let p := tiltedTail μ A b B r
    0 ≤ p ∧ p ≤ 1 ∧
    upperMass μ A g r ≤ B * p ∧
    lowerMass μ A g r ≤ B * (1 - p) := by
  dsimp only
  have hu0 := upperMass_nonneg (μ := μ) (A := A) hb0 r
  have hl0 := lowerMass_nonneg (μ := μ) (A := A) hb0 r
  have hsum := upperMass_add_lowerMass (μ := μ) hA hb r
  rw [hBint] at hsum
  have hp : B * tiltedTail μ A b B r = upperMass μ A b r := by
    dsimp [tiltedTail]
    exact mul_div_cancel₀ _ hB.ne'
  refine ⟨div_nonneg hu0 hB.le, ?_, ?_, ?_⟩
  · apply (div_le_one hB).2
    linarith
  · rw [hp]
    exact upperMass_le_envelope hg hb hgb r
  · calc
      lowerMass μ A g r ≤ lowerMass μ A b r := lowerMass_le_envelope hg hb hgb r
      _ = B * (1 - tiltedTail μ A b B r) := by nlinarith [hp]

/-- Analytic opposite-mass estimate: `ν` may be the measure having density
`F(y)^n` with respect to Lebesgue measure.  It proves the factor `p(1-p)`
from pointwise bounds on the two genuine density masses and their total
weighted integral. -/
theorem integrated_opposite_mass_bound {β : Type*} [MeasurableSpace β]
    {ν : Measure β} {qplus qminus : β → ℝ} {B p T : ℝ}
    (hB : 0 ≤ B) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hplus : Integrable qplus ν) (hminus : Integrable qminus ν)
    (hplus0 : ∀ᵐ y ∂ν, 0 ≤ qplus y)
    (hminus0 : ∀ᵐ y ∂ν, 0 ≤ qminus y)
    (hplusB : ∀ᵐ y ∂ν, qplus y ≤ B * p)
    (hminusB : ∀ᵐ y ∂ν, qminus y ≤ B * (1 - p))
    (hT : ∫ y, (qplus y + qminus y) ∂ν = T) :
    Integrable (fun y => qplus y * qminus y) ν ∧
    (∫ y, qplus y * qminus y ∂ν) ≤ B * T * p * (1 - p) := by
  have hpB : 0 ≤ B * p := mul_nonneg hB hp0
  have hmpB : 0 ≤ B * (1 - p) := mul_nonneg hB (sub_nonneg.mpr hp1)
  have hprod : Integrable (fun y => qplus y * qminus y) ν := by
    apply (hminus.const_mul (B * p)).mono'
      (hplus.aestronglyMeasurable.mul hminus.aestronglyMeasurable)
    filter_upwards [hplus0, hminus0, hplusB] with y hy0 hmy0 hyB
    change ‖qplus y * qminus y‖ ≤ B * p * qminus y
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hy0 hmy0)]
    exact mul_le_mul_of_nonneg_right hyB hmy0
  have hleft : (∫ y, qplus y * qminus y ∂ν) ≤
      B * p * (T - ∫ y, qplus y ∂ν) := by
    have h := integral_mono_ae hprod (hminus.const_mul (B * p)) (by
      filter_upwards [hminus0, hplusB] with y hmy0 hyB
      exact mul_le_mul_of_nonneg_right hyB hmy0)
    rw [integral_const_mul] at h
    rw [integral_add hplus hminus] at hT
    have heq : ∫ y, qminus y ∂ν = T - ∫ y, qplus y ∂ν := by linarith
    rwa [heq] at h
  have hright : (∫ y, qplus y * qminus y ∂ν) ≤
      B * (1 - p) * ∫ y, qplus y ∂ν := by
    have h := integral_mono_ae hprod (hplus.const_mul (B * (1 - p))) (by
      filter_upwards [hplus0, hminusB] with y hpy0 hmyB
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hmyB hpy0)
    simpa [integral_const_mul] using h
  exact ⟨hprod, opposite_mass_bound hB hp0 hp1 hleft hright⟩

/-- The integrated estimate applied to the actual split conditional density
kernel. The only normalization supplied separately is the total score
mass under `ν` (equation (4.6) when `ν(dy)=F(y)^n dy`). -/
theorem conditional_density_opposite_bound {A b : α → ℝ}
    {g : α → ℝ → ℝ} {ν : Measure ℝ} {B T : ℝ}
    (hA : Measurable A) (hb : Integrable b μ) (hb0 : ∀ w, 0 ≤ b w)
    (hB : 0 < B) (hBint : ∫ w, b w ∂μ = B)
    (hgi : ∀ y, Integrable (fun w => g w y) μ)
    (hg0 : ∀ w y, 0 ≤ g w y)
    (hgb : ∀ y, ∀ᵐ w ∂μ, g w y ≤ b w) (r : ℝ)
    (hplus : Integrable (fun y => upperMass μ A (fun w => g w y) r) ν)
    (hminus : Integrable (fun y => lowerMass μ A (fun w => g w y) r) ν)
    (hT : ∫ y, (∫ w, g w y ∂μ) ∂ν = T) :
    let p := tiltedTail μ A b B r
    (∫ y, upperMass μ A (fun w => g w y) r *
      lowerMass μ A (fun w => g w y) r ∂ν) ≤ B * T * p * (1 - p) := by
  have hbounds (y : ℝ) :=
    density_split_bounds hA (hgi y) hb hb0 (hgb y) hB hBint r
  have hnorm : (∫ y, upperMass μ A (fun w => g w y) r +
      lowerMass μ A (fun w => g w y) r ∂ν) = T := by
    calc
      _ = ∫ y, (∫ w, g w y ∂μ) ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => upperMass_add_lowerMass hA (hgi y) r
      _ = T := hT
  exact (integrated_opposite_mass_bound hB.le (hbounds 0).1 (hbounds 0).2.1
    hplus hminus
    (Filter.Eventually.of_forall fun y => upperMass_nonneg (fun w => hg0 w y) r)
    (Filter.Eventually.of_forall fun y => lowerMass_nonneg (fun w => hg0 w y) r)
    (Filter.Eventually.of_forall fun y => (hbounds y).2.2.1)
    (Filter.Eventually.of_forall fun y => (hbounds y).2.2.2) hnorm).2

/-- One orientation of the pointwise layer-cake formula. -/
theorem oriented_layer_cake (a b : ℝ) :
    (∫⁻ r : ℝ, (Ico a b).indicator (fun _ => (1 : ℝ≥0∞)) r) =
      ENNReal.ofReal (b - a) := by
  rw [lintegral_indicator measurableSet_Ico]
  simp [Real.volume_Ico]

/-- The exact scalar layer-cake identity used in Lemma 4.1. It includes
both orientations and uses Lebesgue measure on the threshold parameter. -/
theorem scalar_layer_cake (a b : ℝ) :
    (∫⁻ r : ℝ, (Ico a b).indicator (fun _ => (1 : ℝ≥0∞)) r +
      (Ico b a).indicator (fun _ => (1 : ℝ≥0∞)) r) =
      ENNReal.ofReal |a - b| := by
  rw [lintegral_add_left (measurable_const.indicator measurableSet_Ico),
    oriented_layer_cake, oriented_layer_cake]
  by_cases hab : a ≤ b
  · rw [ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr hab), add_zero,
      abs_of_nonpos (sub_nonpos.mpr hab)]
    congr 1
    ring
  · have hba : b ≤ a := le_of_not_ge hab
    rw [ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr hba), zero_add,
      abs_of_nonneg (sub_nonneg.mpr hba)]

/-- The separation mark for one orientation of a slope pair. -/
def separation (z : ℝ × ℝ) (r : ℝ) : ℝ≥0∞ :=
  (Ico z.1 z.2).indicator (fun _ => 1) r

lemma measurable_separation : Measurable (Function.uncurry separation) := by
  classical
  have hs : MeasurableSet {p : (ℝ × ℝ) × ℝ | p.1.1 ≤ p.2 ∧ p.2 < p.1.2} :=
    (measurableSet_le measurable_fst.fst measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst.snd)
  change Measurable ({p : (ℝ × ℝ) × ℝ | p.1.1 ≤ p.2 ∧ p.2 < p.1.2}.indicator
    (fun _ => (1 : ℝ≥0∞)))
  exact measurable_const.indicator hs

/-- Tonelli turns one orientation of the scalar layer cake into a product
of opposite-tail masses.  No moment assumption is used. -/
theorem oriented_pair_layer_cake (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (z.2 - z.1) ∂μ.prod ν) =
      ∫⁻ r : ℝ, μ (Iic r) * ν (Ioi r) := by
  calc
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (z.2 - z.1) ∂μ.prod ν) =
        ∫⁻ z : ℝ × ℝ, ∫⁻ r : ℝ, separation z r ∂volume ∂μ.prod ν := by
      apply lintegral_congr
      intro z
      exact (oriented_layer_cake z.1 z.2).symm
    _ = ∫⁻ r : ℝ, ∫⁻ z : ℝ × ℝ, separation z r ∂μ.prod ν :=
      lintegral_lintegral_swap measurable_separation.aemeasurable
    _ = ∫⁻ r : ℝ, μ (Iic r) * ν (Ioi r) := by
      apply lintegral_congr
      intro r
      have heq : (fun z : ℝ × ℝ => separation z r) =
          (Iic r ×ˢ Ioi r).indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext z
        simp only [separation, Set.indicator, Set.mem_Ico, Set.mem_prod,
          Set.mem_Iic, Set.mem_Ioi]
      rw [heq, lintegral_indicator (measurableSet_Iic.prod measurableSet_Ioi)]
      simp [Measure.prod_prod]

/-- The nonnegative Gini mean-difference layer cake for an arbitrary law,
including laws without a first moment. -/
theorem gini_layer_cake (μ : Measure ℝ) [SFinite μ] :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal |z.1 - z.2| ∂μ.prod μ) =
      2 * ∫⁻ r : ℝ, μ (Iic r) * μ (Ioi r) := by
  have habs (a b : ℝ) : ENNReal.ofReal |a - b| =
      ENNReal.ofReal (b - a) + ENNReal.ofReal (a - b) := by
    by_cases hab : a ≤ b
    · rw [ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr hab), add_zero,
        abs_of_nonpos (sub_nonpos.mpr hab)]
      congr 1
      ring
    · have hba : b ≤ a := le_of_not_ge hab
      rw [ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr hba), zero_add,
        abs_of_nonneg (sub_nonneg.mpr hba)]
  calc
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal |z.1 - z.2| ∂μ.prod μ) =
        ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (z.2 - z.1) + ENNReal.ofReal (z.1 - z.2)
          ∂μ.prod μ := by
      apply lintegral_congr
      intro z
      exact habs z.1 z.2
    _ = (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (z.2 - z.1) ∂μ.prod μ) +
        ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (z.1 - z.2) ∂μ.prod μ :=
      lintegral_add_left (measurable_snd.sub measurable_fst).ennreal_ofReal _
    _ = (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (z.2 - z.1) ∂μ.prod μ) +
        ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (z.2 - z.1) ∂μ.prod μ := by
      congr 1
      exact lintegral_prod_swap (μ := μ) (ν := μ)
        (fun z : ℝ × ℝ => ENNReal.ofReal (z.2 - z.1))
    _ = 2 * ∫⁻ r : ℝ, μ (Iic r) * μ (Ioi r) := by
      rw [oriented_pair_layer_cake]
      exact (two_mul _).symm

/-- For a probability law, the two opposite-tail masses are `p` and `1-p`.
This is the last equality in (4.9), with no moment finiteness assumption. -/
theorem gini_layer_cake_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal |z.1 - z.2| ∂μ.prod μ) =
      2 * ∫⁻ r : ℝ, μ (Ioi r) * (1 - μ (Ioi r)) := by
  rw [gini_layer_cake]
  congr 1
  apply lintegral_congr
  intro r
  have hc : μ (Iic r) = 1 - μ (Ioi r) := by
    rw [← compl_Ioi, measure_compl measurableSet_Ioi (measure_ne_top μ _), measure_univ]
  rw [hc, mul_comm]

end Paper35.Visibility

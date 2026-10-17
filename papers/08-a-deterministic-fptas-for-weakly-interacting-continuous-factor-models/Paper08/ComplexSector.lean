import Paper08.Integral
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Ring.Pow

/-! # Phase transport and anchored integral projection

The relation records an actual exponential path, without choosing a global
argument or a logarithm. The integral lower bound uses a single anchor and
orthogonal projection; no half-angle geometry is involved.
-/
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory
namespace Paper08.ComplexSector

/-- An actual exponential displacement with bounded change of phase. -/
def Phase (a b : ℂ) (θ : ℝ) : Prop :=
  ∃ w : ℂ, b = a * Complex.exp w ∧ |w.im| ≤ θ

lemma phase_refl (a : ℂ) : Phase a a 0 := by
  exact ⟨0, by simp, by simp⟩

lemma Phase.mono {a b : ℂ} {θ η : ℝ} (h : Phase a b θ) (hθη : θ ≤ η) : Phase a b η := by
  obtain ⟨w, hw, hθ⟩ := h
  exact ⟨w, hw, hθ.trans hθη⟩

lemma Phase.trans {a b c : ℂ} {θ η : ℝ} (hab : Phase a b θ) (hbc : Phase b c η) :
    Phase a c (θ + η) := by
  obtain ⟨u, hu, hθ⟩ := hab
  obtain ⟨v, hv, hη⟩ := hbc
  refine ⟨u + v, ?_, ?_⟩
  · rw [hv, hu, Complex.exp_add]
    ring
  · simpa only [Complex.add_im] using (abs_add_le u.im v.im).trans (add_le_add hθ hη)

lemma Phase.mul {a b c d : ℂ} {θ η : ℝ} (hab : Phase a b θ) (hcd : Phase c d η) :
    Phase (a * c) (b * d) (θ + η) := by
  obtain ⟨u, hu, hθ⟩ := hab
  obtain ⟨v, hv, hη⟩ := hcd
  refine ⟨u + v, ?_, ?_⟩
  · rw [hu, hv, Complex.exp_add]
    ring
  · simpa only [Complex.add_im] using (abs_add_le u.im v.im).trans (add_le_add hθ hη)

lemma phase_of_norm_log {a b w : ℂ} {θ : ℝ} (hb : b = a * Complex.exp w) (hw : ‖w‖ ≤ θ) :
    Phase a b θ := ⟨w, hb, (Complex.abs_im_le_norm w).trans hw⟩

lemma exp_phase (u v : ℂ) : Phase (Complex.exp u) (Complex.exp v) |(v - u).im| := by
  refine ⟨v - u, ?_, le_rfl⟩
  rw [← Complex.exp_add]
  congr 1
  ring

lemma exp_base_phase (w : ℂ) : Phase 1 (Complex.exp w) ‖w‖ := by
  exact phase_of_norm_log (by simp) le_rfl

/-- Unit rotation taking a nonzero anchor to the positive real axis. -/
def rotation (a : ℂ) : ℂ := conj a / (‖a‖ : ℂ)

lemma norm_rotation {a : ℂ} (ha : a ≠ 0) : ‖rotation a‖ = 1 := by
  have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  simp [rotation, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg a), hn]

lemma rotation_mul_anchor {a : ℂ} (ha : a ≠ 0) : rotation a * a = (‖a‖ : ℂ) := by
  have hn : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr ha
  calc
    rotation a * a = (conj a * a) / (‖a‖ : ℂ) := by unfold rotation; ring
    _ = (‖a‖ : ℂ) ^ 2 / (‖a‖ : ℂ) := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      push_cast
      rfl
    _ = (‖a‖ : ℂ) := by field_simp

lemma cos_phase_le {t θ : ℝ} (ht : |t| ≤ θ) (hθ : θ ≤ 1) : Real.cos θ ≤ Real.cos t := by
  have hπ : θ ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
  simpa only [Real.cos_abs] using Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg t) hπ ht

/-- The pointwise projection inequality from an actual bounded exponential
phase displacement. -/
theorem anchor_projection {a b : ℂ} {θ : ℝ} (ha : a ≠ 0) (hphase : Phase a b θ)
    (hθ : θ ≤ 1) : Real.cos θ * ‖b‖ ≤ (rotation a * b).re := by
  obtain ⟨w, hw, him⟩ := hphase
  have hc := cos_phase_le him hθ
  calc
    Real.cos θ * ‖b‖ = Real.cos θ * (‖a‖ * Real.exp w.re) := by rw [hw, norm_mul, Complex.norm_exp]
    _ ≤ Real.cos w.im * (‖a‖ * Real.exp w.re) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (rotation a * b).re := by
      rw [hw, ← mul_assoc (rotation a) a (Complex.exp w), rotation_mul_anchor ha]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_re]
      ring

lemma cos_ge_half {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : (1 : ℝ) / 2 ≤ Real.cos θ := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := θ)
  have hsq : θ ^ 2 ≤ 1 := by nlinarith
  linarith

lemma cos_pos {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : 0 < Real.cos θ :=
  lt_of_lt_of_le (by norm_num) (cos_ge_half hθ0 hθ1)

/-- Anchored projection commutes with the actual Bochner integral. Only
integrability and an almost-everywhere phase bound are required. -/
theorem integral_projection_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℂ} {a : ℂ} {θ : ℝ} (hg : Integrable g μ) (ha : a ≠ 0)
    (hphase : ∀ᵐ x ∂μ, Phase a (g x) θ) (hθ : θ ≤ 1) :
    Real.cos θ * (∫ x, ‖g x‖ ∂μ) ≤ ‖∫ x, g x ∂μ‖ := by
  have hrot : Integrable (fun x => rotation a * g x) μ := hg.const_mul _
  have hreal : Integrable (fun x => (rotation a * g x).re) μ := hrot.re
  have hmono : (∫ x, Real.cos θ * ‖g x‖ ∂μ) ≤ ∫ x, (rotation a * g x).re ∂μ := by
    apply integral_mono_ae (hg.norm.const_mul _) hreal
    exact hphase.mono (fun x hx => anchor_projection ha hx hθ)
  rw [integral_const_mul] at hmono
  have heq : (∫ x, (rotation a * g x).re ∂μ) = (rotation a * ∫ x, g x ∂μ).re := by
    have hh := integral_re hrot
    simpa only [RCLike.re_eq_complex_re, integral_const_mul] using hh
  rw [heq] at hmono
  apply hmono.trans
  calc
    _ ≤ ‖rotation a * ∫ x, g x ∂μ‖ := Complex.re_le_norm _
    _ = ‖∫ x, g x ∂μ‖ := by rw [norm_mul, norm_rotation ha, one_mul]

/-- The norm integral of an a.e. nonzero integrable function on a genuine
probability space is strictly positive. -/
lemma integral_norm_pos {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {g : α → ℂ} (hg : Integrable g μ) (hnz : ∀ᵐ x ∂μ, g x ≠ 0) :
    0 < ∫ x, ‖g x‖ ∂μ := by
  have hs : (Function.support (fun x => ‖g x‖) : Set α) =ᵐ[μ] Set.univ := by
    filter_upwards [hnz] with x hx
    apply propext
    change (‖g x‖ ≠ 0 ↔ True)
    simp [norm_ne_zero_iff, hx]
  have hm := measure_congr hs
  apply (integral_pos_iff_support_of_nonneg (fun x => norm_nonneg (g x)) hg.norm).mpr
  rw [hm, measure_univ]
  norm_num

/-- Quantitative non-cancellation and nonvanishing on a probability space. -/
theorem integral_nonzero {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {g : α → ℂ} {a : ℂ} {θ : ℝ} (hg : Integrable g μ) (ha : a ≠ 0)
    (hnz : ∀ᵐ x ∂μ, g x ≠ 0) (hphase : ∀ᵐ x ∂μ, Phase a (g x) θ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Real.cos θ * (∫ x, ‖g x‖ ∂μ) ≤ ‖∫ x, g x ∂μ‖ ∧ (∫ x, g x ∂μ) ≠ 0 := by
  have hb := integral_projection_bound hg ha hphase hθ1
  have hpos := mul_pos (cos_pos hθ0 hθ1) (integral_norm_pos hg hnz)
  refine ⟨hb, ?_⟩
  exact norm_pos_iff.mp (hpos.trans_le hb)

/-- The exact numerical threshold used by the zero-free induction. -/
def angle (k : ℕ) : ℝ := 1 / Real.sqrt k

lemma angle_nonneg (k : ℕ) : 0 ≤ angle k := by unfold angle; positivity

lemma angle_le_one {k : ℕ} (hk : 1 ≤ k) : angle k ≤ 1 := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : (1 : ℝ) ≤ Real.sqrt k := (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg k)).mpr (by simpa using hkr)
  unfold angle
  exact (div_le_one (by positivity : (0 : ℝ) < Real.sqrt k)).mpr hs

lemma cos_angle_pos {k : ℕ} (hk : 1 ≤ k) : 0 < Real.cos (angle k) :=
  cos_pos (angle_nonneg k) (angle_le_one hk)

/-- Bernoulli's inequality proves cos(1/sqrt(k))^k ≥ 1/2 directly. -/
theorem cos_angle_pow_ge_half {k : ℕ} (hk : 1 ≤ k) :
    (1 : ℝ) / 2 ≤ Real.cos (angle k) ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkone : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsq : angle k ^ 2 = 1 / (k : ℝ) := by
    unfold angle
    rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
  have hinv : (1 : ℝ) / (2 * k) ≤ 1 / 2 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * k) (by norm_num : (0 : ℝ) < 2)).mpr
    nlinarith
  have hbase : 0 ≤ (1 : ℝ) - 1 / (2 * k) := by linarith
  have hcos : (1 : ℝ) - 1 / (2 * k) ≤ Real.cos (angle k) := by
    calc
      _ = 1 - angle k ^ 2 / 2 := by rw [hsq]; field_simp <;> ring
      _ ≤ _ := Real.one_sub_sq_div_two_le_cos
  have hb := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ -(1 / (2 * k : ℝ))) k
  have heq : (1 : ℝ) + (k : ℝ) * (-(1 / (2 * k : ℝ))) = 1 / 2 := by
    field_simp <;> ring
  rw [heq] at hb
  exact hb.trans (pow_le_pow_left₀ hbase hcos k)

lemma Phase.symm {a b : ℂ} {θ : ℝ} (h : Phase a b θ) : Phase b a θ := by
  obtain ⟨w, hw, hθ⟩ := h
  refine ⟨-w, ?_, ?_⟩
  · calc
      a = a * (Complex.exp w * Complex.exp (-w)) := by rw [← Complex.exp_add]; simp
      _ = b * Complex.exp (-w) := by rw [hw]; ring
  · simpa using hθ

lemma Phase.nonzero_iff {a b : ℂ} {θ : ℝ} (h : Phase a b θ) : b ≠ 0 ↔ a ≠ 0 := by
  obtain ⟨w, hw, _⟩ := h
  rw [hw]
  simp [Complex.exp_ne_zero]

theorem phase_prod {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (a b : ι → ℂ) (θ : ι → ℝ) (h : ∀ i ∈ S, Phase (a i) (b i) (θ i)) :
    Phase (∏ i ∈ S, a i) (∏ i ∈ S, b i) (∑ i ∈ S, θ i) := by
  induction S using Finset.induction_on with
  | empty => simpa using phase_refl (1 : ℂ)
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- The same probability-space result with its anchor selected from the
actual nonzero function. -/
theorem probability_integral_pairwise {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {g : α → ℂ} {θ : ℝ}
    (hg : Integrable g μ) (hnz : ∀ x, g x ≠ 0) (hphase : ∀ x y, Phase (g x) (g y) θ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Real.cos θ * (∫ x, ‖g x‖ ∂μ) ≤ ‖∫ x, g x ∂μ‖ ∧ (∫ x, g x ∂μ) ≠ 0 := by
  obtain ⟨x0, hx0⟩ := (Filter.Eventually.of_forall hnz : ∀ᵐ x ∂μ, g x ≠ 0).exists
  exact integral_nonzero hg hx0 (Filter.Eventually.of_forall hnz)
    (Filter.Eventually.of_forall (hphase x0)) hθ0 hθ1

/-- A cube integral is an actual probability-space integral; pointwise sector
conditions are required only on the original cube. -/
theorem cube_integral_nonzero_of_integrable {n : ℕ} {g : (Fin n → ℝ) → ℂ} {θ : ℝ}
    (hg : IntegrableOn g (Integral.cube n))
    (hnz : ∀ x ∈ Integral.cube n, g x ≠ 0)
    (hphase : ∀ x ∈ Integral.cube n, ∀ y ∈ Integral.cube n, Phase (g x) (g y) θ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Real.cos θ * (∫ x in Integral.cube n, ‖g x‖) ≤ ‖∫ x in Integral.cube n, g x‖ ∧
      (∫ x in Integral.cube n, g x) ≠ 0 := by
  let μ := volume.restrict (Integral.cube n)
  letI : IsProbabilityMeasure μ := ⟨by simp [μ, Integral.volume_cube]⟩
  let x0 : Fin n → ℝ := fun _ => 0
  have hx0 : x0 ∈ Integral.cube n := by simp [Integral.mem_cube, x0]
  have hnzae : ∀ᵐ x ∂μ, g x ≠ 0 := by
    filter_upwards [ae_restrict_mem (Integral.measurableSet_cube n)] with x hx
    exact hnz x hx
  have hphaseae : ∀ᵐ x ∂μ, Phase (g x0) (g x) θ := by
    filter_upwards [ae_restrict_mem (Integral.measurableSet_cube n)] with x hx
    exact hphase x0 hx0 x hx
  exact integral_nonzero hg (hnz x0 hx0) hnzae hphaseae hθ0 hθ1

/-- Continuous nonzero functions on the actual cube cannot cancel when all
actual phase displacements lie in the stated sector. -/
theorem cube_integral_nonzero {n : ℕ} {g : (Fin n → ℝ) → ℂ} {θ : ℝ}
    (hg : ContinuousOn g (Integral.cube n))
    (hnz : ∀ x ∈ Integral.cube n, g x ≠ 0)
    (hphase : ∀ x ∈ Integral.cube n, ∀ y ∈ Integral.cube n, Phase (g x) (g y) θ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Real.cos θ * (∫ x in Integral.cube n, ‖g x‖) ≤ ‖∫ x in Integral.cube n, g x‖ ∧
      (∫ x in Integral.cube n, g x) ≠ 0 := by
  exact cube_integral_nonzero_of_integrable
    (hg.integrableOn_compact (isCompact_univ_pi (fun _ => isCompact_Icc))) hnz hphase hθ0 hθ1

/-- Unit-interval version for one-coordinate partial integration. -/
theorem unitInterval_integral_nonzero {g : ℝ → ℂ} {θ : ℝ}
    (hg : ContinuousOn g (Set.Icc 0 1)) (hnz : ∀ x ∈ Set.Icc (0 : ℝ) 1, g x ≠ 0)
    (hphase : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, Phase (g x) (g y) θ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Real.cos θ * (∫ x in Set.Icc (0 : ℝ) 1, ‖g x‖) ≤ ‖∫ x in Set.Icc (0 : ℝ) 1, g x‖ ∧
      (∫ x in Set.Icc (0 : ℝ) 1, g x) ≠ 0 := by
  let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
  letI : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Icc]⟩
  have hnzae : ∀ᵐ x ∂μ, g x ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hnz x hx
  have hphaseae : ∀ᵐ x ∂μ, Phase (g 0) (g x) θ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hphase 0 (by norm_num) x hx
  exact integral_nonzero (hg.integrableOn_compact isCompact_Icc) (hnz 0 (by norm_num))
    hnzae hphaseae hθ0 hθ1

/-- At most k integrations lose at most the same fixed factor. -/
theorem cos_angle_pow_ge_half_of_le {k s : ℕ} (hk : 1 ≤ k) (hs : s ≤ k) :
    (1 : ℝ) / 2 ≤ Real.cos (angle k) ^ s := by
  have hp : Real.cos (angle k) ^ (k - s) ≤ 1 :=
    pow_le_one₀ (cos_angle_pos hk).le (Real.cos_le_one _)
  calc
    (1 : ℝ) / 2 ≤ Real.cos (angle k) ^ k := cos_angle_pow_ge_half hk
    _ = Real.cos (angle k) ^ s * Real.cos (angle k) ^ (k - s) := by rw [← pow_add, Nat.add_sub_of_le hs]
    _ ≤ Real.cos (angle k) ^ s * 1 := mul_le_mul_of_nonneg_left hp (pow_nonneg (cos_angle_pos hk).le s)
    _ = _ := mul_one _

theorem div_cos_angle_pow_le_two {k s : ℕ} (hk : 1 ≤ k) (hs : s ≤ k) :
    1 / Real.cos (angle k) ^ s ≤ 2 := by
  apply (div_le_iff₀ (pow_pos (cos_angle_pos hk) s)).mpr
  nlinarith [cos_angle_pow_ge_half_of_le hk hs]

/-- Arbitrary-domain probability-space interface for partial integrals.
The measure need only be concentrated almost everywhere on D. -/
theorem probability_integral_on_domain {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {D : Set α} {g : α → ℂ} {θ : ℝ}
    (hg : Integrable g μ) (hD : ∀ᵐ x ∂μ, x ∈ D)
    (hnz : ∀ x ∈ D, g x ≠ 0)
    (hphase : ∀ x ∈ D, ∀ y ∈ D, Phase (g x) (g y) θ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Real.cos θ * (∫ x, ‖g x‖ ∂μ) ≤ ‖∫ x, g x ∂μ‖ ∧ (∫ x, g x ∂μ) ≠ 0 := by
  obtain ⟨x0, hx0⟩ := hD.exists
  exact integral_nonzero hg (hnz x0 hx0) (hD.mono (fun x hx => hnz x hx))
    (hD.mono (fun y hy => hphase x0 hx0 y hy)) hθ0 hθ1

/-- Strong norm-log displacements, as furnished by a logarithmic path,
imply the weaker phase promise used by projection. -/
theorem probability_integral_on_domain_of_norm_log {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {D : Set α} {g : α → ℂ} {θ : ℝ}
    (hg : Integrable g μ) (hD : ∀ᵐ x ∂μ, x ∈ D)
    (hnz : ∀ x ∈ D, g x ≠ 0)
    (hlog : ∀ x ∈ D, ∀ y ∈ D, ∃ w : ℂ, g y = g x * Complex.exp w ∧ ‖w‖ ≤ θ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Real.cos θ * (∫ x, ‖g x‖ ∂μ) ≤ ‖∫ x, g x ∂μ‖ ∧ (∫ x, g x ∂μ) ≠ 0 := by
  apply probability_integral_on_domain hg hD hnz _ hθ0 hθ1
  intro x hx y hy
  obtain ⟨w, hw, hnorm⟩ := hlog x hx y hy
  exact phase_of_norm_log hw hnorm

end Paper08.ComplexSector

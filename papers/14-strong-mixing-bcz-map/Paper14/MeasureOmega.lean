import Paper14.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
/-!
# Measure of `Ω`, `Y_r`, and the `(c,θ)` coordinates

Paper anchors: Ex9 (`m(Y_r)=r²`), E13 (`dm = 2c^{-3} dc dθ`, `m(c>K)=K^{-2}`).

The normalized measure is `m = 2 • volume|_Ω`.  Vertical slices of `Ω` have
length `a` at abscissa `a`, so `volume Ω = ∫₀¹ a da = 1/2` and `m Ω = 1`.
-/
open MeasureTheory Filter Topology Set
open scoped ENNReal Real
open intervalIntegral
namespace Paper14

/-! ## Measurability -/

lemma measurableSet_Omega : MeasurableSet Omega := by
  have h : Omega = {x : ℝ × ℝ | 0 < x.1 ∧ 0 < x.2 ∧ 1 < x.1 + x.2}
      ∩ {x : ℝ × ℝ | x.1 ≤ 1 ∧ x.2 ≤ 1} := by
    ext x
    simp only [Omega, mem_setOf_eq, mem_inter_iff]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨⟨h1, h3, h5⟩, h2, h4⟩
    · rintro ⟨⟨h1, h3, h5⟩, h2, h4⟩
      exact ⟨h1, h2, h3, h4, h5⟩
  have h1 : IsOpen {x : ℝ × ℝ | 0 < x.1 ∧ 0 < x.2 ∧ 1 < x.1 + x.2} := by
    have h' : {x : ℝ × ℝ | 0 < x.1 ∧ 0 < x.2 ∧ 1 < x.1 + x.2}
        = {x | 0 < x.1} ∩ {x | 0 < x.2} ∩ {x | (1:ℝ) < x.1 + x.2} := by
      ext x; simp [and_assoc]
    rw [h']
    exact ((isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_const continuous_snd)).inter
      (isOpen_lt continuous_const (continuous_fst.add continuous_snd))
  have h2 : IsClosed {x : ℝ × ℝ | x.1 ≤ 1 ∧ x.2 ≤ 1} := by
    have h' : {x : ℝ × ℝ | x.1 ≤ 1 ∧ x.2 ≤ 1}
        = {x | x.1 ≤ 1} ∩ {x | x.2 ≤ 1} := by
      ext x; simp
    rw [h']
    exact (isClosed_le continuous_fst continuous_const).inter
      (isClosed_le continuous_snd continuous_const)
  rw [h]
  exact h1.measurableSet.inter h2.measurableSet

lemma measurableSet_Farey {u : ℝ} :
    MeasurableSet {x : ℝ × ℝ | 0 < x.1 ∧ x.1 ≤ u ∧ 1 - x.1 < x.2 ∧ x.2 ≤ 1} := by
  have h : {x : ℝ × ℝ | 0 < x.1 ∧ x.1 ≤ u ∧ 1 - x.1 < x.2 ∧ x.2 ≤ 1}
      = {x : ℝ × ℝ | 0 < x.1 ∧ 1 - x.1 < x.2} ∩ {x | x.1 ≤ u ∧ x.2 ≤ 1} := by
    ext x; simp [and_assoc, and_left_comm]
  have h1 : IsOpen {x : ℝ × ℝ | 0 < x.1 ∧ 1 - x.1 < x.2} := by
    have h' : {x : ℝ × ℝ | 0 < x.1 ∧ 1 - x.1 < x.2}
        = {x | 0 < x.1} ∩ {x | (1:ℝ) - x.1 < x.2} := by
      ext x; simp
    rw [h']
    exact (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt (continuous_const.sub continuous_fst) continuous_snd)
  have h2 : IsClosed {x : ℝ × ℝ | x.1 ≤ u ∧ x.2 ≤ 1} := by
    have h' : {x : ℝ × ℝ | x.1 ≤ u ∧ x.2 ≤ 1}
        = {x | x.1 ≤ u} ∩ {x | x.2 ≤ 1} := by
      ext x; simp
    rw [h']
    exact (isClosed_le continuous_fst continuous_const).inter
      (isClosed_le continuous_snd continuous_const)
  rw [h]
  exact h1.measurableSet.inter h2.measurableSet

lemma measurableSet_tailC {K : ℝ} :
    MeasurableSet {x : ℝ × ℝ | 0 < x.1 ∧ x.1 < K ∧ 1 - x.1 < x.2 ∧ x.2 ≤ 1} := by
  have h : {x : ℝ × ℝ | 0 < x.1 ∧ x.1 < K ∧ 1 - x.1 < x.2 ∧ x.2 ≤ 1}
      = {x : ℝ × ℝ | 0 < x.1 ∧ 1 - x.1 < x.2} ∩ {x | x.1 < K ∧ x.2 ≤ 1} := by
    ext x; simp [and_assoc, and_left_comm]
  have h1 : IsOpen {x : ℝ × ℝ | 0 < x.1 ∧ 1 - x.1 < x.2} := by
    have h' : {x : ℝ × ℝ | 0 < x.1 ∧ 1 - x.1 < x.2}
        = {x | 0 < x.1} ∩ {x | (1:ℝ) - x.1 < x.2} := by
      ext x; simp
    rw [h']
    exact (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt (continuous_const.sub continuous_fst) continuous_snd)
  have h2 : MeasurableSet {x : ℝ × ℝ | x.1 < K ∧ x.2 ≤ 1} := by
    have h' : {x : ℝ × ℝ | x.1 < K ∧ x.2 ≤ 1}
        = {x | x.1 < K} ∩ {x | x.2 ≤ 1} := by
      ext x; simp
    rw [h']
    exact (isOpen_lt continuous_fst continuous_const).measurableSet.inter
      (isClosed_le continuous_snd continuous_const).measurableSet
  rw [h]
  exact h1.measurableSet.inter h2

lemma measurableSet_Yr (r : ℝ) : MeasurableSet (Yr r) :=
  measurableSet_Omega.inter
    (isClosed_le continuous_fst continuous_const).measurableSet

lemma measurableSet_line_fst (c : ℝ) : MeasurableSet {x : ℝ × ℝ | x.1 = c} := by
  have h : {x : ℝ × ℝ | x.1 = c} = Prod.fst ⁻¹' ({c} : Set ℝ) := by
    ext x; simp
  rw [h]
  exact continuous_fst.measurable (measurableSet_singleton c)

/-! ## Characterization of slices -/

lemma mem_Omega_iff {x : ℝ × ℝ} :
    x ∈ Omega ↔ 0 < x.1 ∧ x.1 ≤ 1 ∧ 1 - x.1 < x.2 ∧ x.2 ≤ 1 := by
  conv_lhs => rw [← x.eta]
  rw [mem_Omega]
  constructor
  · rintro ⟨ha0, ha1, hb0, hb1, hab⟩
    exact ⟨ha0, ha1, by linarith, hb1⟩
  · rintro ⟨ha0, ha1, hb, hb1⟩
    exact ⟨ha0, ha1, by linarith, hb1, by linarith⟩

lemma volume_line_fst (c : ℝ) : volume {x : ℝ × ℝ | x.1 = c} = 0 := by
  have h : {x : ℝ × ℝ | x.1 = c} = ({c} : Set ℝ) ×ˢ univ := by
    ext x
    simp only [mem_setOf_eq, mem_prod, mem_singleton_iff, mem_univ, and_true]
  rw [h, Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, zero_mul]

/-! ## A one-dimensional integral -/

lemma integral_id_Ioc {u : ℝ} (hu : 0 ≤ u) : (∫ a in Ioc (0:ℝ) u, a) = u ^ 2 / 2 := by
  rw [← intervalIntegral.integral_of_le hu]
  rw [integral_id]
  ring

lemma ofReal_one_half : ENNReal.ofReal (1/2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
  have h : (1/2:ℝ) = (2:ℝ)⁻¹ := by ring
  rw [h, ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2), ENNReal.ofReal_ofNat]

lemma two_mul_ofReal_half {v : ℝ} : (2:ℝ≥0∞) * ENNReal.ofReal (v / 2) = ENNReal.ofReal v := by
  rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by rw [ENNReal.ofReal_ofNat],
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

/-! ## Area of the closed Farey triangle -/

/-- For `0 ≤ u ≤ 1`, the region `{0 < a ≤ u, 1-a < b ≤ 1}` has volume `u²/2`. -/
lemma volume_Farey_le {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    volume {x : ℝ × ℝ | 0 < x.1 ∧ x.1 ≤ u ∧ 1 - x.1 < x.2 ∧ x.2 ≤ 1}
      = ENNReal.ofReal (u ^ 2 / 2) := by
  -- `hu1` is not needed for the integral identity, but keeps the geometric range explicit.
  have _ := hu1
  have hs : MeasurableSet {x : ℝ × ℝ | 0 < x.1 ∧ x.1 ≤ u ∧ 1 - x.1 < x.2 ∧ x.2 ≤ 1} :=
    measurableSet_Farey
  rw [Measure.volume_eq_prod, Measure.prod_apply hs]
  have hslice : ∀ a : ℝ,
      volume (Prod.mk a ⁻¹' {x : ℝ × ℝ | 0 < x.1 ∧ x.1 ≤ u ∧ 1 - x.1 < x.2 ∧ x.2 ≤ 1})
        = (Ioc (0:ℝ) u).indicator (fun t => ENNReal.ofReal t) a := by
    intro a
    by_cases ha : a ∈ Ioc (0:ℝ) u
    · have hpre : Prod.mk a ⁻¹' {x : ℝ × ℝ | 0 < x.1 ∧ x.1 ≤ u ∧ 1 - x.1 < x.2 ∧ x.2 ≤ 1}
          = Ioc (1 - a) 1 := by
        ext b
        simp only [mem_preimage, mem_setOf_eq, mem_Ioc]
        constructor
        · intro h
          exact ⟨h.2.2.1, h.2.2.2⟩
        · intro h
          exact ⟨ha.1, ha.2, h.1, h.2⟩
      rw [hpre, indicator_of_mem ha, Real.volume_Ioc]
      congr 1
      ring
    · have hpre : Prod.mk a ⁻¹' {x : ℝ × ℝ | 0 < x.1 ∧ x.1 ≤ u ∧ 1 - x.1 < x.2 ∧ x.2 ≤ 1}
          = ∅ := by
        refine eq_empty_of_forall_notMem fun b hb => ?_
        simp only [mem_preimage, mem_setOf_eq] at hb
        exact ha ⟨hb.1, hb.2.1⟩
      rw [hpre, measure_empty, indicator_of_notMem ha]
  have h2 : (fun a : ℝ =>
      volume (Prod.mk a ⁻¹' {x : ℝ × ℝ | 0 < x.1 ∧ x.1 ≤ u ∧ 1 - x.1 < x.2 ∧ x.2 ≤ 1}))
      = (Ioc (0:ℝ) u).indicator (fun t => ENNReal.ofReal t) := by
    ext a; exact hslice a
  rw [h2, lintegral_indicator measurableSet_Ioc]
  have hI : (∫ a in Ioc (0:ℝ) u, a) = u ^ 2 / 2 := integral_id_Ioc hu
  rw [← ofReal_integral_eq_lintegral_ofReal
    (f := fun a : ℝ => a) (μ := volume.restrict (Ioc (0:ℝ) u))]
  · rw [hI]
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hu).1
      (continuous_id.intervalIntegrable (0:ℝ) u)
  · exact (ae_restrict_iff' measurableSet_Ioc).2
      (ae_of_all _ fun a ha => ha.1.le)

/-- Open/closed boundary of the Farey triangle is a null line. -/
lemma volume_Farey_lt {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    volume {x : ℝ × ℝ | 0 < x.1 ∧ x.1 < u ∧ 1 - x.1 < x.2 ∧ x.2 ≤ 1}
      = ENNReal.ofReal (u ^ 2 / 2) := by
  have hdiff : {x : ℝ × ℝ | 0 < x.1 ∧ x.1 < u ∧ 1 - x.1 < x.2 ∧ x.2 ≤ 1}
      = {x : ℝ × ℝ | 0 < x.1 ∧ x.1 ≤ u ∧ 1 - x.1 < x.2 ∧ x.2 ≤ 1}
        \ {x : ℝ × ℝ | x.1 = u} := by
    ext x
    simp only [mem_setOf_eq, mem_diff]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, le_of_lt h2, h3, h4⟩, by
        rintro (rfl : x.1 = u)
        exact absurd h2 (lt_irrefl _)⟩
    · rintro ⟨⟨h1, h2, h3, h4⟩, hne⟩
      exact ⟨h1, lt_of_le_of_ne h2 fun he => hne he, h3, h4⟩
  have hnull : volume ({x : ℝ × ℝ | 0 < x.1 ∧ x.1 ≤ u ∧ 1 - x.1 < x.2 ∧ x.2 ≤ 1}
      ∩ {x : ℝ × ℝ | x.1 = u}) = 0 :=
    measure_mono_null inter_subset_right (volume_line_fst u)
  rw [hdiff, measure_diff_null' hnull, volume_Farey_le hu hu1]

/-! ## Area of `Ω` -/

lemma volume_Omega : volume Omega = (2 : ℝ≥0∞)⁻¹ := by
  have h : Omega = {x : ℝ × ℝ | 0 < x.1 ∧ x.1 ≤ (1:ℝ) ∧ 1 - x.1 < x.2 ∧ x.2 ≤ 1} := by
    ext x
    simp only [mem_setOf_eq]
    rw [mem_Omega_iff]
  rw [h, volume_Farey_le (by norm_num : (0:ℝ) ≤ 1) le_rfl]
  have : ((1:ℝ) ^ 2 / 2 : ℝ) = 1/2 := by ring
  rw [this, ofReal_one_half]

/-- Area of the Farey triangle under `volume` is `1/2`, so `m` is a probability. -/
theorem AreaOmegaStatement : volume Omega = (2 : ℝ≥0∞)⁻¹ :=
  volume_Omega

/-! ## Area of `Y_r` -/

lemma volume_Yr {r : ℝ} (hr : 0 < r) (hr' : r < 1) :
    volume (Yr r) = ENNReal.ofReal (r ^ 2 / 2) := by
  have h : Yr r = {x : ℝ × ℝ | 0 < x.1 ∧ x.1 ≤ r ∧ 1 - x.1 < x.2 ∧ x.2 ≤ 1} := by
    ext x
    simp only [Yr, mem_inter_iff, mem_setOf_eq]
    rw [mem_Omega_iff]
    constructor
    · rintro ⟨⟨ha0, _ha1, hb, hb1⟩, har⟩
      exact ⟨ha0, har, hb, hb1⟩
    · rintro ⟨ha0, har, hb, hb1⟩
      exact ⟨⟨ha0, har.trans hr'.le, hb, hb1⟩, har⟩
  rw [h, volume_Farey_le hr.le hr'.le]

lemma m_Yr {r : ℝ} (hr : 0 < r) (hr' : r < 1) : m (Yr r) = ENNReal.ofReal (r ^ 2) := by
  have hs : MeasurableSet (Yr r) := measurableSet_Yr r
  have hsub : Yr r ⊆ Omega := fun _x hx => hx.1
  have hΩ : Yr r ∩ Omega = Yr r := inter_eq_self_of_subset_left hsub
  rw [m, Measure.smul_apply, Measure.restrict_apply hs, hΩ, volume_Yr hr hr']
  rw [smul_eq_mul, two_mul_ofReal_half]

/-- Paper Ex9: `m(Y_r) = r²` for `0 < r < 1`. -/
theorem MeasureYrStatement : ∀ r : ℝ, 0 < r → r < 1 → m (Yr r) = ENNReal.ofReal (r ^ 2) :=
  fun _r hr hr' => m_Yr hr hr'

/-! ## Tail of `c = 1/a` -/

lemma tailC_eq {K : ℝ} (hK : 1 < K) :
    {x ∈ Omega | K < x.1⁻¹}
      = {x : ℝ × ℝ | 0 < x.1 ∧ x.1 < K⁻¹ ∧ 1 - x.1 < x.2 ∧ x.2 ≤ 1} := by
  have hK0 : 0 < K := zero_lt_one.trans hK
  have hK1 : K⁻¹ < 1 := (inv_lt_one₀ hK0).mpr hK
  ext x
  simp only [mem_setOf_eq]
  rw [mem_Omega_iff]
  constructor
  · rintro ⟨⟨ha0, _ha1, hb, hb1⟩, hKx⟩
    exact ⟨ha0, (lt_inv_comm₀ hK0 ha0).mp hKx, hb, hb1⟩
  · rintro ⟨ha0, hax, hb, hb1⟩
    refine ⟨⟨ha0, ?_, hb, hb1⟩, (lt_inv_comm₀ hK0 ha0).mpr hax⟩
    exact (hax.trans hK1).le

lemma volume_tailC {K : ℝ} (hK : 1 < K) :
    volume {x ∈ Omega | K < x.1⁻¹} = ENNReal.ofReal ((K⁻¹) ^ 2 / 2) := by
  have hK0 : 0 < K := zero_lt_one.trans hK
  have hK1 : K⁻¹ < 1 := (inv_lt_one₀ hK0).mpr hK
  have hK0' : 0 < K⁻¹ := inv_pos.mpr hK0
  rw [tailC_eq hK, volume_Farey_lt hK0'.le hK1.le]

lemma inv_sq_eq_rpow_neg_two {K : ℝ} (hK : 0 < K) : (K⁻¹) ^ 2 = K ^ (-2 : ℝ) := by
  have h1 : K ^ (-2 : ℝ) = (K ^ (2:ℝ))⁻¹ := by
    rw [show (-2:ℝ) = -(2:ℝ) by norm_num, Real.rpow_neg (le_of_lt hK)]
  have h2 : (K ^ (2:ℝ))⁻¹ = (K ^ 2)⁻¹ := by rw [Real.rpow_two]
  have h3 : (K ^ 2)⁻¹ = (K⁻¹) ^ 2 := by rw [← inv_pow]
  rw [← h3, ← h2, h1]

lemma m_tailC {K : ℝ} (hK : 1 < K) :
    m {x ∈ Omega | K < x.1⁻¹} = ENNReal.ofReal (K ^ (-2 : ℝ)) := by
  have hK0 : 0 < K := zero_lt_one.trans hK
  have hs : MeasurableSet {x ∈ Omega | K < x.1⁻¹} := by
    rw [tailC_eq hK]
    exact measurableSet_tailC
  have hsub : {x ∈ Omega | K < x.1⁻¹} ⊆ Omega := fun _x hx => hx.1
  have hΩ : {x ∈ Omega | K < x.1⁻¹} ∩ Omega = {x ∈ Omega | K < x.1⁻¹} :=
    inter_eq_self_of_subset_left hsub
  rw [m, Measure.smul_apply, Measure.restrict_apply hs, hΩ, volume_tailC hK]
  rw [smul_eq_mul, two_mul_ofReal_half, inv_sq_eq_rpow_neg_two hK0]

/-- Paper E13: tail of `c = a^{-1}` under `dm`: `m(c>K) = K^{-2}` for `K>1`. -/
theorem TailCStatement : ∀ K : ℝ, 1 < K →
    m {x ∈ Omega | K < x.1⁻¹} = ENNReal.ofReal (K ^ (-2 : ℝ)) :=
  fun _K hK => m_tailC hK

end Paper14

import Paper35.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Deterministic geometry used by the Gaussian maxout branch

These lemmas formalize the common positive rescaling and covariance-normalization
steps of Section 6. They do not assert the probabilistic Crofton identities.
-/

noncomputable section

namespace Paper35.Gaussian

open scoped RealInnerProductSpace
open Set

variable {E : Type*} {K : ℕ}

/-- Adding a common location and multiplying by a positive scale preserves ordering. -/
theorem affine_order_iff (a b c r : ℝ) (hr : 0 < r) :
    c + r * a ≤ c + r * b ↔ a ≤ b := by
  constructor <;> intro h <;> nlinarith

theorem affine_strict_order_iff (a b c r : ℝ) (hr : 0 < r) :
    c + r * a < c + r * b ↔ a < b := by
  constructor <;> intro h <;> nlinarith

theorem affine_eq_iff (a b c r : ℝ) (hr : 0 < r) :
    c + r * a = c + r * b ↔ a = b := by
  constructor <;> intro h <;> nlinarith

/-- Opposite signs depend only on signs in any neighborhood of the crossing. -/
theorem signChanges_iff_of_local_sign_iff (f g : ℝ → ℝ) (s ε : ℝ) (hε : 0 < ε)
    (h : ∀ t ∈ Ioo (s - ε) (s + ε),
      (f t < 0 ↔ g t < 0) ∧ (0 < f t ↔ 0 < g t)) :
    SignChanges f s ↔ SignChanges g s := by
  have forward (f g : ℝ → ℝ)
      (h : ∀ t ∈ Ioo (s - ε) (s + ε),
        (f t < 0 ↔ g t < 0) ∧ (0 < f t ↔ 0 < g t)) :
      SignChanges f s → SignChanges g s := by
    rintro ⟨δ, hδ, hs⟩
    refine ⟨min δ ε, lt_min hδ hε, ?_⟩
    have hl (t : ℝ) (ht : t ∈ Ioo (s - min δ ε) s) :
        t ∈ Ioo (s - δ) s ∧ t ∈ Ioo (s - ε) (s + ε) := by
      have hδ' := min_le_left δ ε
      have hε' := min_le_right δ ε
      constructor <;> constructor <;> linarith [ht.1, ht.2]
    have hr (t : ℝ) (ht : t ∈ Ioo s (s + min δ ε)) :
        t ∈ Ioo s (s + δ) ∧ t ∈ Ioo (s - ε) (s + ε) := by
      have hδ' := min_le_left δ ε
      have hε' := min_le_right δ ε
      constructor <;> constructor <;> linarith [ht.1, ht.2]
    rcases hs with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · exact Or.inl ⟨fun t ht => (h t (hl t ht).2).1.mp (hleft t (hl t ht).1),
        fun t ht => (h t (hr t ht).2).2.mp (hright t (hr t ht).1)⟩
    · exact Or.inr ⟨fun t ht => (h t (hl t ht).2).2.mp (hleft t (hl t ht).1),
        fun t ht => (h t (hr t ht).2).1.mp (hright t (hr t ht).1)⟩
  exact ⟨forward f g h, forward g f (fun t ht => ⟨(h t ht).1.symm, (h t ht).2.symm⟩)⟩

/-- Source-domain version: positivity is required only on the probe interval. -/
theorem signChanges_pos_mul_iff_on (h r : ℝ → ℝ) {L s : ℝ}
    (hs : s ∈ Ioo 0 L) (hr : ∀ t ∈ Ioo 0 L, 0 < r t) :
    SignChanges (fun t => r t * h t) s ↔ SignChanges h s := by
  have hε : 0 < min s (L - s) := lt_min hs.1 (sub_pos.mpr hs.2)
  apply signChanges_iff_of_local_sign_iff _ _ s (min s (L-s)) hε
  intro t ht
  have ht' : t ∈ Ioo 0 L := by
    have := min_le_left s (L-s)
    have := min_le_right s (L-s)
    constructor <;> linarith [ht.1, ht.2]
  constructor
  · constructor <;> intro hsign <;> nlinarith [hr t ht']
  · exact mul_pos_iff_of_pos_left (hr t ht')

theorem signChanges_pos_mul_iff (h r : ℝ → ℝ) (hr : ∀ t, 0 < r t) (s : ℝ) :
    SignChanges (fun t => r t * h t) s ↔ SignChanges h s := by
  have hneg (t : ℝ) : r t * h t < 0 ↔ h t < 0 := by
    constructor <;> intro hsign <;> nlinarith [hr t]
  have hpos (t : ℝ) : 0 < r t * h t ↔ 0 < h t := by
    exact mul_pos_iff_of_pos_left (hr t)
  simp only [SignChanges, hneg, hpos]

/-- Pathwise invariance needs no derivative assumptions on the positive scale. -/
theorem activeSwitch_affine_iff (f : Fin K → ℝ → ℝ) (c r : ℝ → ℝ)
    (hr : ∀ s, 0 < r s) (L s : ℝ) :
    ActiveSwitch (fun j t => c t + r t * f j t) L s ↔
      ActiveSwitch f L s := by
  have hdiff (i j : Fin K) :
      (fun t => (c t + r t * f i t) - (c t + r t * f j t)) =
        (fun t => r t * (f i t - f j t)) := by
    funext t
    ring
  simp only [ActiveSwitch, affine_eq_iff _ _ _ _ (hr s),
    affine_strict_order_iff _ _ _ _ (hr s), hdiff, signChanges_pos_mul_iff _ _ hr]

theorem switchSet_affine (f : Fin K → ℝ → ℝ) (c r : ℝ → ℝ)
    (hr : ∀ s, 0 < r s) (L : ℝ) :
    switchSet (fun j t => c t + r t * f j t) L = switchSet f L := by
  ext s
  exact activeSwitch_affine_iff f c r hr L s

theorem switchCount_affine (f : Fin K → ℝ → ℝ) (c r : ℝ → ℝ)
    (hr : ∀ s, 0 < r s) (L : ℝ) :
    switchCount (fun j t => c t + r t * f j t) L = switchCount f L := by
  unfold switchCount
  rw [switchSet_affine f c r hr]

/-- The deterministic reduction under exactly the source's interval positivity. -/
theorem activeSwitch_affine_iff_on (f : Fin K → ℝ → ℝ) (c r : ℝ → ℝ)
    {L s : ℝ} (hr : ∀ t ∈ Ioo 0 L, 0 < r t) :
    ActiveSwitch (fun j t => c t + r t * f j t) L s ↔
      ActiveSwitch f L s := by
  by_cases hs : s ∈ Ioo 0 L
  · have hdiff (i j : Fin K) :
        (fun t => (c t + r t * f i t) - (c t + r t * f j t)) =
          (fun t => r t * (f i t - f j t)) := by
      funext t
      ring
    simp only [ActiveSwitch, affine_eq_iff _ _ _ _ (hr s hs),
      affine_strict_order_iff _ _ _ _ (hr s hs), hdiff,
      signChanges_pos_mul_iff_on _ _ hs hr]
  · constructor <;> intro h <;> exact (hs (activeSwitch_interior h)).elim

theorem switchSet_affine_on (f : Fin K → ℝ → ℝ) (c r : ℝ → ℝ)
    (L : ℝ) (hr : ∀ t ∈ Ioo 0 L, 0 < r t) :
    switchSet (fun j t => c t + r t * f j t) L = switchSet f L := by
  ext s
  exact activeSwitch_affine_iff_on f c r hr

theorem switchCount_affine_on (f : Fin K → ℝ → ℝ) (c r : ℝ → ℝ)
    (L : ℝ) (hr : ∀ t ∈ Ioo 0 L, 0 < r t) :
    switchCount (fun j t => c t + r t * f j t) L = switchCount f L := by
  unfold switchCount
  rw [switchSet_affine_on f c r L hr]

/-- Common shifts and positive path-dependent scales preserve the actual
nonnegative extended expectation, without integrability assumptions. -/
theorem expectedSwitchCount_affine_on {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (f : Ω → Fin K → ℝ → ℝ)
    (c r : Ω → ℝ → ℝ) (L : ℝ)
    (hr : ∀ ω t, t ∈ Ioo 0 L → 0 < r ω t) :
    expectedSwitchCount μ (fun ω j t => c ω t + r ω t * f ω j t) L =
      expectedSwitchCount μ f L := by
  unfold expectedSwitchCount
  apply MeasureTheory.lintegral_congr
  intro ω
  exact switchCount_affine_on (f ω) (c ω) (r ω) L (hr ω)

section Normalization

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Normalized covariance lift, defined at zero as zero. -/
def normalize (y : E) : E := ‖y‖⁻¹ • y

@[simp] theorem normalize_norm (y : E) (hy : y ≠ 0) : ‖normalize y‖ = 1 := by
  exact norm_smul_inv_norm hy

/-- Normalization therefore takes a nonzero lift into the unit sphere. -/
theorem normalize_mem_sphere (y : E) (hy : y ≠ 0) :
    normalize y ∈ Metric.sphere (0 : E) 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using normalize_norm y hy

theorem norm_smul_normalize (y : E) (hy : y ≠ 0) : ‖y‖ • normalize y = y := by
  rw [normalize, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_smul]

/-- Centered Gaussian linear scores have a common strictly positive scale. -/
theorem inner_eq_norm_mul_inner_normalize (z y : E) (hy : y ≠ 0) :
    ⟪z, y⟫ = ‖y‖ * ⟪z, normalize y⟫ := by
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  rw [normalize, inner_smul_right]
  field_simp

/-- This is the deterministic reduction used in Theorem 2.8: the common mean
and the norm of the covariance lift do not affect active switches. -/
theorem covarianceLift_switchSet (Z : Fin K → E) (y : ℝ → E) (m : ℝ → ℝ)
    (hy : ∀ s, y s ≠ 0) (L : ℝ) :
    switchSet (fun j s => m s + ⟪Z j, y s⟫) L =
      switchSet (fun j s => ⟪Z j, normalize (y s)⟫) L := by
  have heq : (fun j s => m s + ⟪Z j, y s⟫) =
      (fun j s => m s + ‖y s‖ * ⟪Z j, normalize (y s)⟫) := by
    funext j s
    rw [← inner_eq_norm_mul_inner_normalize (Z j) (y s) (hy s)]
  rw [heq]
  exact switchSet_affine _ _ _ (fun s => norm_pos_iff.mpr (hy s)) L

/-- The source-domain form only assumes nonvanishing along the probe. -/
theorem covarianceLift_switchSet_on (Z : Fin K → E) (y : ℝ → E) (m : ℝ → ℝ)
    (L : ℝ) (hy : ∀ s ∈ Ioo 0 L, y s ≠ 0) :
    switchSet (fun j s => m s + ⟪Z j, y s⟫) L =
      switchSet (fun j s => ⟪Z j, normalize (y s)⟫) L := by
  have hfactor (z y : E) : ⟪z, y⟫ = ‖y‖ * ⟪z, normalize y⟫ := by
    by_cases hy' : y = 0
    · simp [hy', normalize]
    · exact inner_eq_norm_mul_inner_normalize z y hy'
  have heq : (fun j s => m s + ⟪Z j, y s⟫) =
      (fun j s => m s + ‖y s‖ * ⟪Z j, normalize (y s)⟫) := by
    funext j s
    rw [← hfactor (Z j) (y s)]
  rw [heq]
  exact switchSet_affine_on _ _ _ L (fun s hs => norm_pos_iff.mpr (hy s hs))

/-- The endpoint inner product of normalized lifts is the normalized covariance
kernel appearing inside arccos in (6.12). -/
theorem inner_normalize (a b : E) :
    ⟪normalize a, normalize b⟫ = ⟪a, b⟫ / (‖a‖ * ‖b‖) := by
  simp only [normalize, real_inner_smul_left, inner_smul_right]
  ring

/-- The expression in Corollary 6.3 is the principal angle of the lifted endpoints. -/
theorem angle_normalize (a b : E) (ha : a ≠ 0) (hb : b ≠ 0) :
    InnerProductGeometry.angle (normalize a) (normalize b) =
      Real.arccos (⟪a, b⟫ / (‖a‖ * ‖b‖)) := by
  rw [InnerProductGeometry.angle, normalize_norm a ha, normalize_norm b hb,
    one_mul, div_one, inner_normalize]

theorem arccos_normalized_kernel_mem_Icc (a b : E) :
    Real.arccos (⟪a, b⟫ / (‖a‖ * ‖b‖)) ∈ Icc 0 Real.pi := by
  exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

/-- A nonzero affine lifted segment has endpoint angle strictly below π,
as used for the minor arc in Corollary 6.3. -/
theorem angle_lt_pi_of_segment_nonzero (a b : E)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, (1 - t) • a + t • b ≠ 0) :
    InnerProductGeometry.angle a b < Real.pi := by
  have hne : InnerProductGeometry.angle a b ≠ Real.pi := by
    intro heq
    obtain ⟨_, r, hr, hb⟩ := InnerProductGeometry.angle_eq_pi_iff.mp heq
    have hd : 0 < 1 - r := by linarith
    have ht : 1 / (1 - r) ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact (div_pos zero_lt_one hd).le
      · apply (div_le_one hd).mpr
        linarith
    apply h (1 / (1-r)) ht
    rw [hb, smul_smul, ← add_smul]
    have hc : 1 - 1 / (1-r) + 1 / (1-r) * r = 0 := by
      field_simp
      ring
    rw [hc, zero_smul]
  exact lt_of_le_of_ne (InnerProductGeometry.angle_le_pi a b) hne

/-- Nonvanishing on the compact probe interval gives a uniform positive radius. -/
theorem exists_positive_radius {y : ℝ → E} {L : ℝ} (hL : 0 ≤ L)
    (hc : ContinuousOn y (Icc 0 L)) (hy : ∀ s ∈ Icc 0 L, y s ≠ 0) :
    ∃ c > 0, ∀ s ∈ Icc 0 L, c ≤ ‖y s‖ := by
  obtain ⟨s, hs, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) L).Nonempty from ⟨0, le_rfl, hL⟩) hc.norm
  exact ⟨‖y s‖, norm_pos_iff.mpr (hy s hs), hmin⟩

/-- Velocity of the normalized lift, valid away from the origin. -/
def normalizedVelocity (y v : E) : E :=
  ‖y‖⁻¹ • v - (⟪y, v⟫ / ‖y‖ ^ 3) • y

/-- Exact normalized-lift speed identity underlying equation (6.8). -/
theorem normalizedVelocity_norm_sq (y v : E) (hy : y ≠ 0) :
    ‖normalizedVelocity y v‖ ^ 2 =
      ‖v‖ ^ 2 / ‖y‖ ^ 2 - ⟪y, v⟫ ^ 2 / ‖y‖ ^ 4 := by
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  rw [normalizedVelocity, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, real_inner_smul_left, inner_smul_right,
    real_inner_comm v y, mul_pow, sq_abs]
  field_simp
  ring

/-- Normalizing a differentiable lifted curve gives its projected tangential velocity. -/
theorem hasDerivAt_normalize {f : ℝ → E} {v : E} {s : ℝ}
    (hf : HasDerivAt f v s) (h : f s ≠ 0) :
    HasDerivAt (fun t => normalize (f t)) (normalizedVelocity (f s) v) s := by
  have hn : ‖f s‖ ≠ 0 := norm_ne_zero_iff.mpr h
  have hnsq : ‖f s‖ ^ 2 ≠ 0 := pow_ne_zero _ hn
  have hd : HasDerivAt (fun t => ‖f t‖) (⟪f s, v⟫ / ‖f s‖) s := by
    convert hf.norm_sq.sqrt hnsq using 1 <;>
      simp only [Real.sqrt_sq (norm_nonneg _)]
    field_simp
  have hi := hd.inv hn
  convert hi.smul hf using 1
  have hcoef : -(⟪f s, v⟫ / ‖f s‖) / ‖f s‖ ^ 2 =
      -(⟪f s, v⟫ / ‖f s‖ ^ 3) := by
    field_simp
  dsimp only [normalizedVelocity, Pi.inv_apply]
  rw [hcoef]
  simp only [sub_eq_add_neg, neg_smul]

/-- Dropping the nonnegative radial correction bounds the normalized speed. -/
theorem normalizedVelocity_norm_le (y v : E) (hy : y ≠ 0) :
    ‖normalizedVelocity y v‖ ≤ ‖v‖ / ‖y‖ := by
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hsq := normalizedVelocity_norm_sq y v hy
  have hnon : 0 ≤ ⟪y, v⟫ ^ 2 / ‖y‖ ^ 4 := by positivity
  have hdiv : 0 ≤ ‖v‖ / ‖y‖ := div_nonneg (norm_nonneg _) hn.le
  have heq : (‖v‖ / ‖y‖) ^ 2 = ‖v‖ ^ 2 / ‖y‖ ^ 2 := div_pow _ _ _
  nlinarith [norm_nonneg (normalizedVelocity y v)]

end Normalization

end Paper35.Gaussian

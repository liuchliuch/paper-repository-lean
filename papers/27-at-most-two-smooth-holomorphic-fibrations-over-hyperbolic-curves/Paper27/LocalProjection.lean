import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Lean.Elab.Tactic.Omega

/-!
# Local differential calculation for the branched-cover projections

Source: P27, Remark 2.5 (`S2.Thmtheorem5`, local display `S2.Ex10`).

The local branched-cover map is `(t,w) ↦ (t,w^m + φ(t))`.  This file proves the
complex Fréchet derivative statements for its two coordinate projections.  The
analytic input is the genuine hypothesis `HasDerivAt φ φ' t`.  These results do
not assert the existence or any global property of the branched covers discussed
later in the remark.
-/

namespace Paper27

/-- The displayed local branched-cover model in Remark 2.5. -/
def localBranchMap (m : ℕ) (φ : ℂ → ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (p.1, p.2 ^ m + φ p.1)

/-- The second projection of the local branched-cover model. -/
def localSecondProjection (m : ℕ) (φ : ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  p.2 ^ m + φ p.1

/-- The differential `m w^(m-1) dw + φ' dt`, as a continuous complex-linear map. -/
noncomputable def localSecondDifferential (m : ℕ) (w φ' : ℂ) : (ℂ × ℂ) →L[ℂ] ℂ :=
  ((m : ℂ) * w ^ (m - 1)) • ContinuousLinearMap.snd ℂ ℂ ℂ +
    φ' • ContinuousLinearMap.fst ℂ ℂ ℂ

@[simp] theorem localSecondDifferential_apply (m : ℕ) (w φ' : ℂ) (v : ℂ × ℂ) :
    localSecondDifferential m w φ' v =
      (m : ℂ) * w ^ (m - 1) * v.2 + φ' * v.1 := by
  simp [localSecondDifferential, smul_eq_mul]

/-- The actual complex Fréchet derivative of the second local projection. -/
theorem hasFDerivAt_localSecondProjection (m : ℕ) {φ : ℂ → ℂ} {t w φ' : ℂ}
    (hφ : HasDerivAt φ φ' t) :
    HasFDerivAt (localSecondProjection m φ) (localSecondDifferential m w φ') (t, w) := by
  have hp := (hasDerivAt_pow m w).comp_hasFDerivAt (t, w)
    (hasFDerivAt_snd (𝕜 := ℂ) (p := (t, w)))
  have hq := hφ.comp_hasFDerivAt (t, w)
    (hasFDerivAt_fst (𝕜 := ℂ) (p := (t, w)))
  simpa [localSecondProjection, localSecondDifferential, Function.comp_def] using hp.add hq

/-- The first coordinate projection has its usual complex derivative. -/
theorem hasFDerivAt_first_localBranchMap (m : ℕ) (φ : ℂ → ℂ) (p : ℂ × ℂ) :
    HasFDerivAt (fun q => (localBranchMap m φ q).1)
      (ContinuousLinearMap.fst ℂ ℂ ℂ) p := by
  exact hasFDerivAt_fst

/-- The first coordinate projection is a submersion at every point of the local model. -/
theorem surjective_fderiv_first_localBranchMap (m : ℕ) (φ : ℂ → ℂ) (p : ℂ × ℂ) :
    Function.Surjective (fderiv ℂ (fun q => (localBranchMap m φ q).1) p) := by
  rw [(hasFDerivAt_first_localBranchMap m φ p).fderiv]
  exact fun y => ⟨(y, 0), rfl⟩

/-- For `m ≥ 2`, the displayed second differential vanishes at `w = φ' = 0`. -/
theorem localSecondDifferential_zero (m : ℕ) (hm : 2 ≤ m) :
    localSecondDifferential m 0 0 = 0 := by
  have hpow : m - 1 ≠ 0 := by omega
  apply ContinuousLinearMap.ext
  intro v
  simp [localSecondDifferential_apply, zero_pow hpow]

/-- At such a ramification point, this is the derivative of the actual second projection. -/
theorem hasFDerivAt_localSecondProjection_zero (m : ℕ) (hm : 2 ≤ m)
    {φ : ℂ → ℂ} {t : ℂ} (hφ : HasDerivAt φ 0 t) :
    HasFDerivAt (𝕜 := ℂ) (localSecondProjection m φ) 0 (t, 0) := by
  simpa only [localSecondDifferential_zero m hm] using
    hasFDerivAt_localSecondProjection m (w := 0) hφ

/-- A zero differential to `ℂ` is not surjective. -/
theorem not_surjective_fderiv_localSecondProjection_zero (m : ℕ) (hm : 2 ≤ m)
    {φ : ℂ → ℂ} {t : ℂ} (hφ : HasDerivAt φ 0 t) :
    ¬ Function.Surjective (fderiv ℂ (localSecondProjection m φ) (t, 0)) := by
  rw [(hasFDerivAt_localSecondProjection_zero m hm hφ).fderiv]
  intro h
  obtain ⟨v, hv⟩ := h 1
  exact (zero_ne_one : (0 : ℂ) ≠ 1) (by simpa using hv)

/-- Complete rank criterion for the second differential, for the range `m ≥ 2` in the paper. -/
theorem localSecondDifferential_surjective_iff (m : ℕ) (hm : 2 ≤ m) (w φ' : ℂ) :
    Function.Surjective (localSecondDifferential m w φ') ↔ w ≠ 0 ∨ φ' ≠ 0 := by
  constructor
  · intro hs
    by_cases hw : w = 0
    · right
      intro hφ
      subst w
      subst φ'
      rw [localSecondDifferential_zero m hm] at hs
      obtain ⟨v, hv⟩ := hs 1
      exact (zero_ne_one : (0 : ℂ) ≠ 1) (by simpa using hv)
    · exact Or.inl hw
  · rintro (hw | hφ)
    · have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have ha : (m : ℂ) * w ^ (m - 1) ≠ 0 := mul_ne_zero hm0 (pow_ne_zero _ hw)
      intro y
      refine ⟨(0, y / ((m : ℂ) * w ^ (m - 1))), ?_⟩
      simp [localSecondDifferential_apply, mul_div_cancel₀, ha]
    · intro y
      refine ⟨(y / φ', 0), ?_⟩
      simp [localSecondDifferential_apply, mul_div_cancel₀, hφ]

/-- The rank criterion for the actual derivative, with the analytic hypothesis explicit. -/
theorem surjective_fderiv_localSecondProjection_iff (m : ℕ) (hm : 2 ≤ m)
    {φ : ℂ → ℂ} {t w φ' : ℂ} (hφ : HasDerivAt φ φ' t) :
    Function.Surjective (fderiv ℂ (localSecondProjection m φ) (t, w)) ↔
      w ≠ 0 ∨ φ' ≠ 0 := by
  rw [(hasFDerivAt_localSecondProjection m hφ).fderiv]
  exact localSecondDifferential_surjective_iff m hm w φ'

end Paper27

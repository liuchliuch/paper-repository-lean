import Paper28.RelativeProjectionCalculus
import Paper28.Normalization

/-! The actual normalized finite projection and normalized straight homotopy
in Lemma 5.1. The denominator, relative fixing, carrier and sharp derivative
estimates are proved from the explicit formulas. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {J H : Type*} [Fintype J] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def normalizedProjection (φ : J → H → ℝ) (P : J → H →L[ℝ] H) (u : H) : H :=
  sphericalNormalize (weightedProjection φ P u)

def projectionHomotopyRaw (φ : J → H → ℝ) (P : J → H →L[ℝ] H) (t : ℝ) (u : H) : H :=
  (1-t) • u + t • weightedProjection φ P u

def projectionHomotopy (φ : J → H → ℝ) (P : J → H →L[ℝ] H) (t : ℝ) (u : H) : H :=
  sphericalNormalize (projectionHomotopyRaw φ P t u)

theorem projectionHomotopyRaw_error (φ : J → H → ℝ) (P : J → H →L[ℝ] H)
    (u : H) (t ε : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hε : 0 ≤ ε)
    (hError : ‖weightedProjection φ P u - u‖ ≤ ε) :
    ‖projectionHomotopyRaw φ P t u - u‖ ≤ ε := by
  have he : projectionHomotopyRaw φ P t u - u = t • (weightedProjection φ P u - u) := by
    unfold projectionHomotopyRaw
    module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  exact (mul_le_mul_of_nonneg_left hError ht0).trans (by nlinarith)

theorem projectionHomotopy_denominator (φ : J → H → ℝ) (P : J → H →L[ℝ] H)
    (u : H) (t ε : ℝ) (hu : ‖u‖ = 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hε : 0 ≤ ε)
    (hError : ‖weightedProjection φ P u - u‖ ≤ ε) :
    1-ε ≤ ‖projectionHomotopyRaw φ P t u‖ := by
  have he := projectionHomotopyRaw_error φ P u t ε ht0 ht1 hε hError
  have h := norm_sub_norm_le u (projectionHomotopyRaw φ P t u)
  rw [norm_sub_rev, hu] at h
  linarith

theorem projectionHomotopy_endpoints (φ : J → H → ℝ) (P : J → H →L[ℝ] H)
    (u : H) (hu : ‖u‖ = 1) :
    projectionHomotopy φ P 0 u = u ∧ projectionHomotopy φ P 1 u = normalizedProjection φ P u := by
  simp [projectionHomotopy, projectionHomotopyRaw, normalizedProjection, sphericalNormalize_fixed u hu]

theorem projectionHomotopy_fixed (φ : J → H → ℝ) (P : J → H →L[ℝ] H)
    (u : H) (hu : ‖u‖ = 1) (hSum : ∑ j, φ j u = 1)
    (hFix : ∀ j, φ j u ≠ 0 → P j u = u) (t : ℝ) : projectionHomotopy φ P t u = u := by
  have hR := weightedProjection_fixed φ P u hSum hFix
  have he : projectionHomotopyRaw φ P t u = u := by
    rw [projectionHomotopyRaw, hR]
    module
  rw [projectionHomotopy, he, sphericalNormalize_fixed u hu]

/-- The normalized image lies in the same actual finite-coordinate
subspace as its finitely many active projected vectors. -/
theorem normalizedProjection_mem (φ : J → H → ℝ) (P : J → H →L[ℝ] H)
    (u : H) (E : Submodule ℝ H) (hP : ∀ j, P j u ∈ E) : normalizedProjection φ P u ∈ E := by
  apply E.smul_mem
  exact Submodule.sum_mem E (fun j _ => E.smul_mem (φ j u) (hP j))

/-- The exact derivative constant after normalization, before choosing the
arbitrarily small coordinate error. -/
theorem normalizedProjectionDerivative_norm (φ : J → H → ℝ)
    (dφ : J → H → H →L[ℝ] ℝ) (P : J → H →L[ℝ] H)
    (u h : H) (ε C : ℝ) (hu : ‖u‖ = 1) (hSum : ∑ j, φ j u = 1)
    (hφ : ∀ j, 0 ≤ φ j u) (hP : ∀ j v, ‖P j v‖ ≤ ‖v‖)
    (hError : ∀ j, ‖P j u - u‖ ≤ ε) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hC : ∑ j, ‖dφ j u‖ ≤ C) :
    ‖normalizationDerivative (weightedProjection φ P u)
      (weightedProjectionDerivative φ dφ P u h)‖ ≤ ((1+C*ε)/(1-ε)) * ‖h‖ := by
  have hR := weightedProjection_norm_lower φ P u ε hu (weightedProjection_error φ P u ε hSum hφ hError)
  have hD := weightedProjectionDerivative_norm φ dφ P u h ε C hSum hφ hP hError hε hC
  have hC0 : 0 ≤ C := le_trans (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hC
  have hN : 0 ≤ (1+C*ε)*‖h‖ := mul_nonneg (by positivity) (norm_nonneg h)
  calc
    _ ≤ ‖weightedProjectionDerivative φ dφ P u h‖ / ‖weightedProjection φ P u‖ :=
      normalizationDerivative_norm_le _ _
    _ ≤ ((1+C*ε)*‖h‖) / ‖weightedProjection φ P u‖ :=
      div_le_div_of_nonneg_right hD (norm_nonneg _)
    _ ≤ ((1+C*ε)*‖h‖) / (1-ε) :=
      div_le_div_of_nonneg_left hN (by linarith) hR
    _ = _ := by ring

end Paper28

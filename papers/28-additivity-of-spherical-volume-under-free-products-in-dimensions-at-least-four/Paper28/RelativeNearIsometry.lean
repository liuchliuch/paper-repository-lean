import Paper28.RelativeNormalization

/-! Closing the quantitative local estimate in Lemma 5.1: arbitrarily small
coordinate errors give an actual normalized Frechet differential bounded by
1 + eta, using the constructed map and its derived derivative. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter
open scoped Topology
variable {J H : Type*} [Fintype J] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem exists_normalization_error (C η : ℝ) (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (1+C*ε)/(1-ε) ≤ 1+η := by
  let ε := η / (2*(C+η+1))
  have hd : 0 < 2*(C+η+1) := by positivity
  have he : 0 < ε := by dsimp [ε]; exact div_pos hη hd
  have he1 : ε < 1 := by
    dsimp [ε]
    rw [div_lt_one hd]
    linarith
  refine ⟨ε, he, he1, ?_⟩
  rw [div_le_iff₀ (sub_pos.mpr he1)]
  dsimp [ε]
  field_simp
  nlinarith

theorem hasFDerivAt_normalizedProjection (φ : J → H → ℝ)
    (dφ : J → H → H →L[ℝ] ℝ) (P : J → H →L[ℝ] H)
    (u : H) (hφ : ∀ j, HasFDerivAt (φ j) (dφ j u) u)
    (hSum : (fun x => ∑ j, φ j x) =ᶠ[𝓝 u] (fun _ => (1 : ℝ)))
    (hR : weightedProjection φ P u ≠ 0) :
    HasFDerivAt (normalizedProjection φ P)
      ((normalizationDerivative (weightedProjection φ P u)).comp
        (weightedProjectionDerivative φ dφ P u)) u :=
  (hasFDerivAt_sphericalNormalize (weightedProjection φ P u) hR).comp u
    (hasFDerivAt_weightedProjection φ dφ P u hφ hSum)

/-- The local sharp differential estimate with the exact requested error
eta. This is a consequence of the constructed operators, not an input. -/
theorem normalizedProjection_near_isometry (φ : J → H → ℝ)
    (dφ : J → H → H →L[ℝ] ℝ) (P : J → H →L[ℝ] H)
    (u : H) (ε C η : ℝ) (hu : ‖u‖ = 1) (hSum : ∑ j, φ j u = 1)
    (hφ : ∀ j, 0 ≤ φ j u) (hP : ∀ j v, ‖P j v‖ ≤ ‖v‖)
    (hError : ∀ j, ‖P j u - u‖ ≤ ε) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hC : ∑ j, ‖dφ j u‖ ≤ C) (hη : (1+C*ε)/(1-ε) ≤ 1+η) :
    ∀ h, ‖normalizationDerivative (weightedProjection φ P u)
      (weightedProjectionDerivative φ dφ P u h)‖ ≤ (1+η)*‖h‖ := by
  intro h
  exact (normalizedProjectionDerivative_norm φ dφ P u h ε C hu hSum hφ hP hError hε hε1 hC).trans
    (mul_le_mul_of_nonneg_right hη (norm_nonneg h))

end Paper28

import Paper28.RelativeNormalization

/-! The sharp projection bounds need coordinate errors only at active
weights. Zero weights have zero derivatives for the actual nonnegative
partition, so inactive projections can be replaced by the identity in the
pointwise algebra without changing the constructed map or derivative. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {J H : Type*} [Fintype J] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def activeProjection (φ : J → H → ℝ) (P : J → H →L[ℝ] H) (u : H) (j : J) : H →L[ℝ] H := by
  classical
  exact if φ j u = 0 then ContinuousLinearMap.id ℝ H else P j

theorem weightedProjection_active_eq (φ : J → H → ℝ) (P : J → H →L[ℝ] H) (u : H) :
    weightedProjection φ P u = weightedProjection φ (activeProjection φ P u) u := by
  classical
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : φ j u = 0 <;> simp [activeProjection,hj]

theorem weightedProjectionDerivative_active_eq (φ : J → H → ℝ)
    (dφ : J → H → H →L[ℝ] ℝ) (P : J → H →L[ℝ] H) (u : H)
    (hZero : ∀ j, φ j u = 0 → dφ j u = 0) :
    weightedProjectionDerivative φ dφ P u =
      weightedProjectionDerivative φ dφ (activeProjection φ P u) u := by
  classical
  have hFirst : (∑ j, φ j u • P j) = ∑ j, φ j u • activeProjection φ P u j := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : φ j u = 0 <;> simp [activeProjection,hj]
  have hSecond : (∑ j, (dφ j u).smulRight (P j u-u)) =
      ∑ j, (dφ j u).smulRight (activeProjection φ P u j u-u) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : φ j u = 0
    · rw [hZero j hj]
      ext v
      simp [ContinuousLinearMap.smulRight_apply]
    · simp [activeProjection,hj]
  unfold weightedProjectionDerivative
  rw [hFirst,hSecond]

theorem activeProjection_contraction (φ : J → H → ℝ) (P : J → H →L[ℝ] H) (u : H)
    (hP : ∀ j v, ‖P j v‖ ≤ ‖v‖) : ∀ j v, ‖activeProjection φ P u j v‖ ≤ ‖v‖ := by
  classical
  intro j v
  by_cases hj : φ j u = 0
  · simp [activeProjection,hj]
  · simpa only [activeProjection,if_neg hj] using hP j v

theorem activeProjection_error (φ : J → H → ℝ) (P : J → H →L[ℝ] H) (u : H) (ε : ℝ)
    (hε : 0 ≤ ε) (hError : ∀ j, φ j u ≠ 0 → ‖P j u-u‖ ≤ ε) :
    ∀ j, ‖activeProjection φ P u j u-u‖ ≤ ε := by
  classical
  intro j
  by_cases hj : φ j u = 0
  · simpa only [activeProjection,if_pos hj,ContinuousLinearMap.id_apply,sub_self,norm_zero] using hε
  · simpa only [activeProjection,if_neg hj] using hError j hj

theorem weightedProjection_error_active (φ : J → H → ℝ) (P : J → H →L[ℝ] H)
    (u : H) (ε : ℝ) (hSum : ∑ j, φ j u = 1) (hφ : ∀ j, 0 ≤ φ j u)
    (hε : 0 ≤ ε) (hError : ∀ j, φ j u ≠ 0 → ‖P j u-u‖ ≤ ε) :
    ‖weightedProjection φ P u-u‖ ≤ ε := by
  rw [weightedProjection_active_eq φ P u]
  exact weightedProjection_error φ (activeProjection φ P u) u ε hSum hφ
    (activeProjection_error φ P u ε hε hError)

theorem weightedProjectionDerivative_norm_active (φ : J → H → ℝ)
    (dφ : J → H → H →L[ℝ] ℝ) (P : J → H →L[ℝ] H) (u h : H) (ε C : ℝ)
    (hSum : ∑ j, φ j u = 1) (hφ : ∀ j, 0 ≤ φ j u)
    (hZero : ∀ j, φ j u = 0 → dφ j u = 0) (hP : ∀ j v, ‖P j v‖ ≤ ‖v‖)
    (hε : 0 ≤ ε) (hError : ∀ j, φ j u ≠ 0 → ‖P j u-u‖ ≤ ε)
    (hC : ∑ j, ‖dφ j u‖ ≤ C) :
    ‖weightedProjectionDerivative φ dφ P u h‖ ≤ (1+C*ε)*‖h‖ := by
  rw [weightedProjectionDerivative_active_eq φ dφ P u hZero]
  exact weightedProjectionDerivative_norm φ dφ (activeProjection φ P u) u h ε C hSum hφ
    (activeProjection_contraction φ P u hP) (activeProjection_error φ P u ε hε hError) hε hC

theorem normalizedProjectionDerivative_norm_active (φ : J → H → ℝ)
    (dφ : J → H → H →L[ℝ] ℝ) (P : J → H →L[ℝ] H) (u h : H) (ε C : ℝ)
    (hu : ‖u‖ = 1) (hSum : ∑ j, φ j u = 1) (hφ : ∀ j, 0 ≤ φ j u)
    (hZero : ∀ j, φ j u = 0 → dφ j u = 0) (hP : ∀ j v, ‖P j v‖ ≤ ‖v‖)
    (hε : 0 ≤ ε) (hε1 : ε < 1) (hError : ∀ j, φ j u ≠ 0 → ‖P j u-u‖ ≤ ε)
    (hC : ∑ j, ‖dφ j u‖ ≤ C) :
    ‖normalizationDerivative (weightedProjection φ P u) (weightedProjectionDerivative φ dφ P u h)‖ ≤
      ((1+C*ε)/(1-ε))*‖h‖ := by
  rw [weightedProjection_active_eq φ P u,weightedProjectionDerivative_active_eq φ dφ P u hZero]
  exact normalizedProjectionDerivative_norm φ dφ (activeProjection φ P u) u h ε C hu hSum hφ
    (activeProjection_contraction φ P u hP) (activeProjection_error φ P u ε hε hError) hε hε1 hC

end Paper28

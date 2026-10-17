import Paper28.NJacobian

/-! The full-dimensional Jacobian chain rule through the actual image of a
linear map. The deficient-rank case is proved by its nontrivial kernel. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped InnerProductSpace
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]

/-- A noninjective differential has zero full-dimensional Jacobian. -/
theorem linearJacobian_of_not_injective (D : E →ₗ[ℝ] F) (hD : ¬ Function.Injective D) :
    linearJacobian D = 0 := by
  have hk : (LinearMap.ker D) ≠ ⊥ := fun h => hD ((LinearMap.ker_eq_bot).mp h)
  have hle : (LinearMap.ker D) ≤ (LinearMap.ker (D.adjoint.comp D)) := by
    intro x hx
    change D.adjoint (D x) = 0
    rw [LinearMap.mem_ker.mp hx, map_zero]
  have hk' : (LinearMap.ker (D.adjoint.comp D)) ≠ ⊥ := fun h => hk (le_antisymm (h ▸ hle) bot_le)
  rw [linearJacobian_def, LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk', Real.sqrt_zero]

/-- Square-domain chain rule, proved by congruence of Gram matrices. -/
theorem linearJacobian_comp_of_finrank_eq (D : E →ₗ[ℝ] F) (A : F →ₗ[ℝ] G)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    linearJacobian (A.comp D) = linearJacobian A * linearJacobian D := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let c := (stdOrthonormalBasis ℝ F).reindex (finCongr hdim.symm)
  let C : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun i j => c.repr (D (b j)) i
  have hv (j) : D (b j) = ∑ i, C i j • c i := (c.toBasis.sum_repr _).symm
  have hc : Matrix.gram ℝ (fun i => c i) = 1 := by
    ext i j
    exact orthonormal_iff_ite.mp c.orthonormal i j
  have hD : Matrix.gram ℝ (fun j => D (b j)) = C.transpose * C := by
    conv_lhs => arg 2; ext j; rw [hv]
    rw [gram_linear_combinations, hc, Matrix.mul_one]
  have hA : Matrix.gram ℝ (fun j => A (D (b j))) =
      C.transpose * Matrix.gram ℝ (fun i => A (c i)) * C := by
    have hvec : (fun j => A (D (b j))) = fun j => ∑ i, C i j • A (c i) := by
      funext j
      rw [hv, map_sum]
      simp only [map_smul]
    rw [hvec, gram_linear_combinations]
  have hdet : (Matrix.gram ℝ (fun j => A (D (b j)))).det =
      (Matrix.gram ℝ (fun i => A (c i))).det * (Matrix.gram ℝ (fun j => D (b j))).det := by
    rw [hA, hD, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  rw [linearJacobian_eq_gram (A.comp D) b, linearJacobian_eq_gram A c,
    linearJacobian_eq_gram D b]
  change Real.sqrt (Matrix.gram ℝ (fun j => A (D (b j)))).det = _
  rw [hdet, Real.sqrt_mul ((Matrix.posSemidef_gram ℝ (fun i => A (c i))).det_nonneg)]

/-- Chain rule through the actual image plane, when no rank is lost. -/
theorem linearJacobian_comp_range (D : E →ₗ[ℝ] F) (A : F →ₗ[ℝ] G)
    (hD : Function.Injective D) :
    linearJacobian (A.comp D) =
      linearJacobian (A.comp (LinearMap.range D).subtype) * linearJacobian D := by
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (LinearMap.range D) :=
    (LinearMap.finrank_range_of_inj hD).symm
  have h := linearJacobian_comp_of_finrank_eq D.rangeRestrict (A.comp (LinearMap.range D).subtype) hdim
  have heq : (A.comp (LinearMap.range D).subtype).comp D.rangeRestrict = A.comp D := rfl
  rw [heq] at h
  change linearJacobian (A.comp D) = linearJacobian (A.comp (LinearMap.range D).subtype) * nJacobian D at h
  rw [nJacobian_eq_linearJacobian D] at h
  exact h

/-- Losing rank before composition forces every downstream term to zero. -/
theorem linearJacobian_comp_of_not_injective (D : E →ₗ[ℝ] F) (A : F →ₗ[ℝ] G)
    (hD : ¬ Function.Injective D) : linearJacobian (A.comp D) = 0 := by
  apply linearJacobian_of_not_injective
  intro hAD
  exact hD (fun x y h => hAD (congrArg A h))

end Paper28

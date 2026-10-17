import Paper38.EmpiricalCovariance
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Differential empirical moment closure for the actual finite particle cloud.
These statements apply at any physical time to particles satisfying the common affine velocity
`Xᵢ' = C Xᵢ - m`, and derive the moment ODE rather than postulating moment trajectories. -/

noncomputable section
open scoped BigOperators Matrix

namespace Paper38.Empirical

variable {N d : ℕ}

/-- Differentiation commutes with the finite arithmetic sample mean. -/
theorem mean_hasDerivAt (X : ℝ → Fin N → Fin d → ℝ)
    (v : Fin N → Fin d → ℝ) (t : ℝ)
    (hX : ∀ i, HasDerivAt (fun s => X s i) (v i) t) :
    HasDerivAt (fun s => mean (X s)) (mean v) t := by
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hX i)
  simpa only [mean] using hsum.const_smul (N : ℝ)⁻¹

/-- The centered velocity is obtained by subtracting the sample mean velocity. -/
theorem centered_hasDerivAt (X : ℝ → Fin N → Fin d → ℝ)
    (v : Fin N → Fin d → ℝ) (t : ℝ)
    (hX : ∀ i, HasDerivAt (fun s => X s i) (v i) t) (i : Fin N) :
    HasDerivAt (fun s => centered (X s) i) (centered v i) t := by
  exact (hX i).sub (mean_hasDerivAt X v t hX)

/-- Product-rule derivative of the empirical covariance, with no rank assumptions. -/
theorem covariance_hasDerivAt (X : ℝ → Fin N → Fin d → ℝ)
    (v : Fin N → Fin d → ℝ) (t : ℝ)
    (hX : ∀ i, HasDerivAt (fun s => X s i) (v i) t) :
    HasDerivAt (fun s => covariance (X s))
      ((N : ℝ)⁻¹ • (centeredMatrix v * (centeredMatrix (X t))ᵀ +
        centeredMatrix (X t) * (centeredMatrix v)ᵀ)) t := by
  apply hasDerivAt_pi.mpr
  intro j
  apply hasDerivAt_pi.mpr
  intro k
  have hi (i : Fin N) := centered_hasDerivAt X v t hX i
  have hp (i : Fin N) :=
    (hasDerivAt_pi.mp (hi i) j).mul (hasDerivAt_pi.mp (hi i) k)
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hp i)
  have hd := hs.const_mul (N : ℝ)⁻¹
  simpa only [covariance, centeredMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    Pi.smul_apply, smul_eq_mul, Pi.add_apply, Finset.sum_add_distrib] using hd

/-- Averaging the common affine particle equation yields its closed mean equation. -/
theorem mean_hasDerivAt_of_affine (hN : 0 < N)
    (X : ℝ → Fin N → Fin d → ℝ) (t : ℝ)
    (C : Matrix (Fin d) (Fin d) ℝ) (m : Fin d → ℝ)
    (hX : ∀ i, HasDerivAt (fun s => X s i) (C *ᵥ X t i - m) t) :
    HasDerivAt (fun s => mean (X s)) (C *ᵥ mean (X t) - m) t := by
  have hd := mean_hasDerivAt X (fun i => C *ᵥ X t i - m) t hX
  have heq : mean (fun i => C *ᵥ X t i - m) = C *ᵥ mean (X t) - m := by
    simpa only [sub_eq_add_neg, add_comm] using mean_affine hN (X t) (-m) C
  rw [heq] at hd
  exact hd

/-- Centering removes the common translation in the affine particle equation. -/
theorem centered_hasDerivAt_of_affine (hN : 0 < N)
    (X : ℝ → Fin N → Fin d → ℝ) (t : ℝ)
    (C : Matrix (Fin d) (Fin d) ℝ) (m : Fin d → ℝ)
    (hX : ∀ i, HasDerivAt (fun s => X s i) (C *ᵥ X t i - m) t) (i : Fin N) :
    HasDerivAt (fun s => centered (X s) i) (C *ᵥ centered (X t) i) t := by
  have hd := (hX i).sub (mean_hasDerivAt_of_affine hN X t C m hX)
  simpa only [centered, Matrix.mulVec_sub, sub_sub_sub_cancel_right] using hd

/-- The common affine particle equation yields the closed Lyapunov covariance equation. -/
theorem covariance_hasDerivAt_of_affine (hN : 0 < N)
    (X : ℝ → Fin N → Fin d → ℝ) (t : ℝ)
    (C : Matrix (Fin d) (Fin d) ℝ) (m : Fin d → ℝ)
    (hX : ∀ i, HasDerivAt (fun s => X s i) (C *ᵥ X t i - m) t) :
    HasDerivAt (fun s => covariance (X s))
      (C * covariance (X t) + covariance (X t) * Cᵀ) t := by
  have hd := covariance_hasDerivAt X (fun i => C *ᵥ X t i - m) t hX
  have hv : centeredMatrix (fun i => C *ᵥ X t i - m) = C * centeredMatrix (X t) := by
    have hfun : (fun i => C *ᵥ X t i - m) = (fun i => -m + C *ᵥ X t i) := by
      funext i
      exact sub_eq_neg_add _ _
    rw [hfun]
    ext j i
    exact congrFun (centered_affine hN (X t) (-m) C i) j
  rw [hv] at hd
  simpa only [covariance, Matrix.transpose_mul, smul_add,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc] using hd

/-- Eq. 6.1's moment closure derived from the finite particle derivatives. -/
theorem affine_particle_moment_closure (hN : 0 < N)
    (X : ℝ → Fin N → Fin d → ℝ) (t : ℝ)
    (C : Matrix (Fin d) (Fin d) ℝ) (m : Fin d → ℝ)
    (hX : ∀ i, HasDerivAt (fun s => X s i) (C *ᵥ X t i - m) t) :
    HasDerivAt (fun s => mean (X s)) (C *ᵥ mean (X t) - m) t ∧
    HasDerivAt (fun s => covariance (X s))
      (C * covariance (X t) + covariance (X t) * Cᵀ) t :=
  ⟨mean_hasDerivAt_of_affine hN X t C m hX,
    covariance_hasDerivAt_of_affine hN X t C m hX⟩

/-- One-sided/local-domain version of finite-mean differentiation. -/
theorem mean_hasDerivWithinAt (X : ℝ → Fin N → Fin d → ℝ)
    (v : Fin N → Fin d → ℝ) (t : ℝ) {s : Set ℝ}
    (hX : ∀ i, HasDerivWithinAt (fun u => X u i) (v i) s t) :
    HasDerivWithinAt (fun u => mean (X u)) (mean v) s t := by
  have hsum := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ => hX i)
  simpa only [mean] using hsum.const_smul (N : ℝ)⁻¹

/-- Centering differentiation on an arbitrary time domain. -/
theorem centered_hasDerivWithinAt (X : ℝ → Fin N → Fin d → ℝ)
    (v : Fin N → Fin d → ℝ) (t : ℝ) {s : Set ℝ}
    (hX : ∀ i, HasDerivWithinAt (fun u => X u i) (v i) s t) (i : Fin N) :
    HasDerivWithinAt (fun u => centered (X u) i) (centered v i) s t := by
  exact (hX i).sub (mean_hasDerivWithinAt X v t hX)

/-- Product-rule covariance differentiation on an arbitrary time domain. -/
theorem covariance_hasDerivWithinAt (X : ℝ → Fin N → Fin d → ℝ)
    (v : Fin N → Fin d → ℝ) (t : ℝ) {s : Set ℝ}
    (hX : ∀ i, HasDerivWithinAt (fun u => X u i) (v i) s t) :
    HasDerivWithinAt (fun u => covariance (X u))
      ((N : ℝ)⁻¹ • (centeredMatrix v * (centeredMatrix (X t))ᵀ +
        centeredMatrix (X t) * (centeredMatrix v)ᵀ)) s t := by
  apply hasDerivWithinAt_pi.mpr
  intro j
  apply hasDerivWithinAt_pi.mpr
  intro k
  have hi (i : Fin N) := centered_hasDerivWithinAt X v t hX i
  have hp (i : Fin N) :=
    (hasDerivWithinAt_pi.mp (hi i) j).mul (hasDerivWithinAt_pi.mp (hi i) k)
  have hs := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ => hp i)
  have hd := hs.const_mul (N : ℝ)⁻¹
  simpa only [covariance, centeredMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    Pi.smul_apply, smul_eq_mul, Pi.add_apply, Finset.sum_add_distrib] using hd

/-- Actual affine particle closure, valid also at the physical-time endpoint on `[0,∞)`. -/
theorem affine_particle_moment_closure_within (hN : 0 < N)
    (X : ℝ → Fin N → Fin d → ℝ) (t : ℝ) {s : Set ℝ}
    (C : Matrix (Fin d) (Fin d) ℝ) (m : Fin d → ℝ)
    (hX : ∀ i, HasDerivWithinAt (fun u => X u i) (C *ᵥ X t i - m) s t) :
    HasDerivWithinAt (fun u => mean (X u)) (C *ᵥ mean (X t) - m) s t ∧
    HasDerivWithinAt (fun u => covariance (X u))
      (C * covariance (X t) + covariance (X t) * Cᵀ) s t := by
  have hmean := mean_hasDerivWithinAt X (fun i => C *ᵥ X t i - m) t hX
  have heq : mean (fun i => C *ᵥ X t i - m) = C *ᵥ mean (X t) - m := by
    simpa only [sub_eq_add_neg, add_comm] using mean_affine hN (X t) (-m) C
  rw [heq] at hmean
  have hcov := covariance_hasDerivWithinAt X (fun i => C *ᵥ X t i - m) t hX
  have hv : centeredMatrix (fun i => C *ᵥ X t i - m) = C * centeredMatrix (X t) := by
    have hfun : (fun i => C *ᵥ X t i - m) = (fun i => -m + C *ᵥ X t i) := by
      funext i
      exact sub_eq_neg_add _ _
    rw [hfun]
    ext j i
    exact congrFun (centered_affine hN (X t) (-m) C i) j
  rw [hv] at hcov
  refine ⟨hmean, ?_⟩
  simpa only [covariance, Matrix.transpose_mul, smul_add,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc] using hcov

end Paper38.Empirical

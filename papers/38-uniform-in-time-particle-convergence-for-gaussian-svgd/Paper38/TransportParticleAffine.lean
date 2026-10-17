import Paper38.AffineLifting
import Paper38.ModelBridges
import Mathlib.Analysis.ODE.Gronwall

/-! Linear-ODE uniqueness derives the particle affine representation from an
actual fundamental matrix. Existence of that fundamental matrix and of the
nonlinear moment flow is deliberately not asserted by this component. -/

noncomputable section
namespace Paper38.TransportParticleAffine

open Paper38.Model MeasureTheory Set
open scoped Matrix NNReal

variable {d N : ℕ}

/-- Matrix evaluation at a fixed Euclidean vector is a genuine linear map. -/
def matrixAction (v : E d) : Mat d →ₗ[ℝ] E d :=
  ((LinearMap.applyₗ : E d →ₗ[ℝ] (E d →ₗ[ℝ] E d) →ₗ[ℝ] E d) v).comp
    Matrix.toEuclideanLin.toLinearMap

@[simp] lemma matrixAction_apply (v : E d) (A : Mat d) : matrixAction v A = matVec A v := rfl

def matrixCLM : Mat d →ₗ[ℝ] (E d →L[ℝ] E d) :=
  (LinearMap.toContinuousLinearMap : (E d →ₗ[ℝ] E d) ≃ₗ[ℝ] (E d →L[ℝ] E d)).toLinearMap.comp
    Matrix.toEuclideanLin.toLinearMap

@[simp] lemma matrixCLM_apply (A : Mat d) (v : E d) : matrixCLM A v = matVec A v := rfl

lemma fundamental_apply_deriv {L : ℝ → Mat d} {C : Mat d} {s : Set ℝ} {t : ℝ}
    (hL : HasDerivWithinAt L (C * L t) s t) (v : E d) :
    HasDerivWithinAt (fun r => matVec (L r) v) (matVec C (matVec (L t) v)) s t := by
  rw [← GaussianAffine.matVec_mul]
  apply ModelBridges.hasDerivWithinAt_of_coordinates
  change HasDerivWithinAt (fun r => L r *ᵥ WithLp.ofLp v)
    ((C * L t) *ᵥ WithLp.ofLp v) s t
  apply hasDerivWithinAt_pi.mpr
  intro j
  simpa only [Matrix.mulVec, dotProduct] using
    (HasDerivWithinAt.fun_sum (u := Finset.univ) (fun k _ =>
      ((hasDerivWithinAt_pi.mp (hasDerivWithinAt_pi.mp hL j) k).mul_const (v k))))

/-- Uniqueness of the continuous linear particle equation proves the affine
representation; it is not included as an input field. -/
theorem affine_representation_from_fundamental
    (C : ℝ → Mat d) (m μ : ℝ → E d) (L : ℝ → Mat d) (X : ℝ → Fin N → E d)
    (hC : ContinuousOn C (Ici 0)) (hL0 : L 0 = 1)
    (hX : ∀ t, 0 ≤ t → ∀ i,
      HasDerivWithinAt (fun r => X r i) (matVec (C t) (X t i) - m t) (Ici 0) t)
    (hμ : ∀ t, 0 ≤ t →
      HasDerivWithinAt μ (matVec (C t) (μ t) - m t) (Ici 0) t)
    (hL : ∀ t, 0 ≤ t → HasDerivWithinAt L (C t * L t) (Ici 0) t)
    (t : ℝ) (ht : 0 ≤ t) (i : Fin N) :
    X t i = μ t + matVec (L t) (X 0 i - μ 0) := by
  let v := X 0 i - μ 0
  let Y : ℝ → E d := fun r => μ r + matVec (L r) v
  have hY : ∀ r, 0 ≤ r →
      HasDerivWithinAt Y (matVec (C r) (Y r) - m r) (Ici 0) r := by
    intro r hr
    have h := (hμ r hr).add (fundamental_apply_deriv (hL r hr) v)
    convert h using 1
    change matVec (C r) (μ r + matVec (L r) v) - m r =
      (matVec (C r) (μ r) - m r) + matVec (C r) (matVec (L r) v)
    rw [show matVec (C r) (μ r + matVec (L r) v) =
      matVec (C r) (μ r) + matVec (C r) (matVec (L r) v) from
      (Matrix.toEuclideanLin (C r)).map_add _ _]
    abel
  have hcont : ContinuousOn (fun r => matrixCLM (C r)) (Icc 0 t) :=
    matrixCLM.continuous_of_finiteDimensional.comp_continuousOn
      (hC.mono (fun r hr => hr.1))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let K : ℝ≥0 := ⟨max 0 M, le_max_left _ _⟩
  have hK : ∀ r ∈ Ico 0 t, LipschitzOnWith K
      (fun y : E d => matVec (C r) y - m r) Set.univ := by
    intro r hr
    have hb : ‖matrixCLM (C r)‖₊ ≤ K := by
      exact_mod_cast (hM r ⟨hr.1, hr.2.le⟩).trans (le_max_right _ _)
    have hlip := (matrixCLM (C r)).lipschitz.weaken hb
    apply (lipschitzWith_iff_dist_le_mul.mpr (fun u w => ?_)).lipschitzOnWith
    have heq : (matVec (C r) u - m r) - (matVec (C r) w - m r) =
        matVec (C r) u - matVec (C r) w := by abel
    simpa only [matrixCLM_apply, dist_eq_norm, heq] using hlip.dist_le_mul u w
  have hinit : X 0 i = Y 0 := by
    simp only [Y, hL0, matVec, Matrix.one_mulVec, vec, WithLp.toLp_ofLp]
    dsimp [v]
    abel
  have heq := ODE_solution_unique_of_mem_Icc_right
    (v := fun r y => matVec (C r) y - m r) (s := fun _ => Set.univ) hK
    (fun r hr => ((hX r hr.1 i).continuousWithinAt).mono (fun s hs => hs.1))
    (fun r hr => (hX r hr.1 i).mono (fun s hs => hr.1.trans hs))
    (by intro r hr; trivial)
    (fun r hr => ((hY r hr.1).continuousWithinAt).mono (fun s hs => hs.1))
    (fun r hr => (hY r hr.1).mono (fun s hs => hr.1.trans hs))
    (by intro r hr; trivial) hinit
  exact heq ⟨ht, le_refl t⟩

/-- Equation (6.2) for an actual projected particle solution, obtained from
its actual empirical-mean derivative and linear-ODE uniqueness. -/
theorem particle_affine_representation (hN : 0 < N)
    (V : E d → ℝ) (X : ℝ → Fin N → E d) (hX : particleSolution V X)
    (hC : ContinuousOn (fun t => particleCoefficient V (X t)) (Ici 0))
    (L : ℝ → Mat d) (hL0 : L 0 = 1)
    (hL : ∀ t, 0 ≤ t → HasDerivWithinAt L
      (particleCoefficient V (X t) * L t) (Ici 0) t)
    (t : ℝ) (ht : 0 ≤ t) (i : Fin N) :
    X t i = empiricalMean (X t) + matVec (L t) (X 0 i - empiricalMean (X 0)) := by
  apply affine_representation_from_fundamental
    (fun t => particleCoefficient V (X t))
    (fun t => meanGradient V (empiricalMean (X t)) (empiricalCovariance (X t)))
    (fun t => empiricalMean (X t)) L X hC hL0
    (fun t ht i => hX.2 t ht i) ?_ hL t ht i
  intro s hs
  exact (ModelBridges.affine_particle_moment_closure_within hN X s
    (particleCoefficient V (X s))
    (meanGradient V (empiricalMean (X s)) (empiricalCovariance (X s)))
    (hX.2 s hs)).1

/-- Equation (6.3) follows by taking the actual empirical covariance of (6.2). -/
theorem particle_affine_covariance (hN : 0 < N)
    (V : E d → ℝ) (X : ℝ → Fin N → E d) (hX : particleSolution V X)
    (hC : ContinuousOn (fun t => particleCoefficient V (X t)) (Ici 0))
    (L : ℝ → Mat d) (hL0 : L 0 = 1)
    (hL : ∀ t, 0 ≤ t → HasDerivWithinAt L
      (particleCoefficient V (X t) * L t) (Ici 0) t)
    (t : ℝ) (ht : 0 ≤ t) :
    empiricalCovariance (X t) = L t * empiricalCovariance (X 0) * (L t).transpose := by
  have heq : X t = fun i => empiricalMean (X t) +
      matVec (L t) (X 0 i - empiricalMean (X 0)) := by
    funext i
    exact particle_affine_representation hN V X hX hC L hL0 hL t ht i
  calc
    empiricalCovariance (X t) = empiricalCovariance
      (fun i => empiricalMean (X t) + matVec (L t) (X 0 i - empiricalMean (X 0))) :=
      congrArg empiricalCovariance heq
    _ = _ := ModelBridges.empiricalCovariance_affine_lift hN (X 0) (empiricalMean (X t)) (L t)

lemma whitening_isUnit (x : Fin N → E d) (W : Mat d) (hW : IsWhitening x W) : IsUnit W := by
  apply (Matrix.isUnit_iff_isUnit_det W).mpr
  apply Matrix.isUnit_det_of_right_inverse (B := empiricalCovariance x * W.transpose)
  exact (Matrix.mul_assoc W (empiricalCovariance x) W.transpose).symm.trans hW

/-- Whitening gives the exact inverse factorization, without inverse covariance moments. -/
lemma whitening_inverse_covariance (x : Fin N → E d) (W : Mat d) (hW : IsWhitening x W) :
    W⁻¹ * (W⁻¹).transpose = empiricalCovariance x := by
  have hd := (Matrix.isUnit_iff_isUnit_det W).mp (whitening_isUnit x W hW)
  calc
    W⁻¹ * (W⁻¹).transpose =
        W⁻¹ * (W * empiricalCovariance x * W.transpose) * (W⁻¹).transpose := by
      rw [hW, Matrix.mul_one]
    _ = (W⁻¹ * W) * empiricalCovariance x * (W.transpose * (W⁻¹).transpose) := by
      noncomm_ring
    _ = empiricalCovariance x := by
      rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul W hd,
        Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

/-- The standardized affine factor B=LW⁻¹ reconstructs the actual particle cloud. -/
theorem standardized_affine_lift (x : Fin N → E d) (W L : Mat d)
    (hW : IsWhitening x W) (m : E d) :
    (∀ i, m + matVec L (x i - empiricalMean x) =
      m + matVec (L * W⁻¹) (standardizedCloud x W i)) ∧
    (L * W⁻¹) * (L * W⁻¹).transpose = L * empiricalCovariance x * L.transpose := by
  have hd := (Matrix.isUnit_iff_isUnit_det W).mp (whitening_isUnit x W hW)
  constructor
  · intro i
    unfold standardizedCloud
    rw [← GaussianAffine.matVec_mul,
      Matrix.nonsing_inv_mul_cancel_right W L hd]
  · calc
      (L * W⁻¹) * (L * W⁻¹).transpose =
          L * (W⁻¹ * (W⁻¹).transpose) * L.transpose := by
        rw [Matrix.transpose_mul]
        noncomm_ring
      _ = L * empiricalCovariance x * L.transpose := by
        rw [whitening_inverse_covariance x W hW]

end Paper38.TransportParticleAffine

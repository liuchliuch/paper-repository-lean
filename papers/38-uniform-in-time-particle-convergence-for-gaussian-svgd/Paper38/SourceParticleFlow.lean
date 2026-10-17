import Paper38.TransportParticleAffine
import Paper38.LinearMatrixODE
import Paper38.Specification
import Paper38.GaussianCoefficientModel
import Mathlib.Analysis.Matrix

/-! Actual projected-particle well-posedness derived from the actual moment
flow and the standard fundamental-matrix theorem. The covariance reconstruction
is proved by uniqueness of its linear Lyapunov ODE. -/

noncomputable section
namespace Paper38.SourceParticleFlow

open Paper38.Model Paper38.TransportParticleAffine Paper38.Specification Set
open scoped Matrix MatrixOrder NNReal Matrix.Norms.Frobenius

variable {d N : ℕ}

def momentCoefficient (V : E d → ℝ) (μ : E d) (S : Mat d) : Mat d :=
  1 - meanHessian V μ S * S - outer (meanGradient V μ S) μ

lemma momentCoefficient_eq_gaussianCoefficient (V : E d → ℝ) (μ : E d) (S : Mat d)
    (hS : S.PosDef) :
    momentCoefficient V μ S = ParticleLimit.gaussianCoefficient V (μ, covarianceRoot S) := by
  have hs : covarianceRoot S * covarianceRoot S = S :=
    CFC.sqrt_mul_sqrt_self _ hS.posSemidef.nonneg
  unfold ParticleLimit.gaussianCoefficient
  rw [hs]
  rfl

lemma mean_normalform (V : E d → ℝ) (μ : E d) (S : Mat d) :
    matVec (momentCoefficient V μ S) μ - meanGradient V μ S = (momentField V μ S).1 := by
  apply (EuclideanSpace.equiv (Fin d) ℝ).injective
  change momentCoefficient V μ S *ᵥ ModelBridges.coordinates μ -
    ModelBridges.coordinates (meanGradient V μ S) =
      ModelBridges.coordinates ((momentField V μ S).1)
  rw [ModelBridges.momentField_mean_coordinates]
  exact MomentClosure.affine_mean_eq_momentMean _ _ _ _

lemma covariance_normalform (V : E d → ℝ) (hV : ContDiff ℝ 2 V)
    (μ : E d) (S : Mat d) (hS : S.transpose = S) :
    momentCoefficient V μ S * S + S * (momentCoefficient V μ S).transpose =
      (momentField V μ S).2 := by
  rw [ModelBridges.momentField_covariance_coordinates]
  exact MomentClosure.affine_covariance_eq_momentCov _ _ _ _ hS
    (ModelBridges.meanHessian_transpose V hV μ S)

/-- The continuous linear operator in the covariance Lyapunov equation. -/
def lyapunovLinear (C : Mat d) : Mat d →ₗ[ℝ] Mat d where
  toFun S := C * S + S * C.transpose
  map_add' A B := by simp only [Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' a S := by simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add, RingHom.id_apply]

def lyapunovOperator : Mat d →ₗ[ℝ] (Mat d →L[ℝ] Mat d) where
  toFun C := (lyapunovLinear C).toContinuousLinearMap
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro S
    change (A + B) * S + S * (A + B).transpose =
      (A * S + S * A.transpose) + (B * S + S * B.transpose)
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.transpose_add]
    abel
  map_smul' a C := by
    apply ContinuousLinearMap.ext
    intro S
    change (a • C) * S + S * (a • C).transpose = a • (C * S + S * C.transpose)
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_smul, smul_add]

@[simp] lemma lyapunovOperator_apply (C S : Mat d) :
    lyapunovOperator C S = C * S + S * C.transpose := rfl

/-- Uniqueness is derived by the ordinary bounded-Lipschitz ODE theorem on
any compact physical-time interval, with no Gaussian conclusion as input. -/
theorem lyapunov_ode_unique (C S T : ℝ → Mat d)
    (hC : ContinuousOn C (Ici 0)) (h0 : S 0 = T 0)
    (hS : ∀ t, 0 ≤ t → HasDerivWithinAt S (C t * S t + S t * (C t).transpose) (Ici 0) t)
    (hT : ∀ t, 0 ≤ t → HasDerivWithinAt T (C t * T t + T t * (C t).transpose) (Ici 0) t)
    (t : ℝ) (ht : 0 ≤ t) : S t = T t := by
  have hcont : ContinuousOn (fun r => lyapunovOperator (C r)) (Icc 0 t) :=
    (lyapunovOperator (d := d)).continuous_of_finiteDimensional.comp_continuousOn
      (hC.mono (fun r hr => hr.1))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let K : ℝ≥0 := ⟨max 0 M, le_max_left _ _⟩
  have hK : ∀ r ∈ Ico 0 t, LipschitzOnWith K
      (fun A : Mat d => C r * A + A * (C r).transpose) Set.univ := by
    intro r hr
    have hb : ‖lyapunovOperator (C r)‖₊ ≤ K := by
      exact_mod_cast (hM r ⟨hr.1, hr.2.le⟩).trans (le_max_right _ _)
    exact ((lyapunovOperator (C r)).lipschitz.weaken hb).lipschitzOnWith
  have heq := ODE_solution_unique_of_mem_Icc_right
    (v := fun r A => C r * A + A * (C r).transpose) (s := fun _ => Set.univ) hK
    (fun r hr => ((hS r hr.1).continuousWithinAt).mono (fun s hs => hs.1))
    (fun r hr => (hS r hr.1).mono (fun s hs => hr.1.trans hs))
    (by intro r hr; trivial)
    (fun r hr => ((hT r hr.1).continuousWithinAt).mono (fun s hs => hs.1))
    (fun r hr => (hT r hr.1).mono (fun s hs => hr.1.trans hs))
    (by intro r hr; trivial) h0
  exact heq ⟨ht, le_refl t⟩

lemma transpose_deriv {L : ℝ → Mat d} {D : Mat d} {s : Set ℝ} {t : ℝ}
    (hL : HasDerivWithinAt L D s t) :
    HasDerivWithinAt (fun r => (L r).transpose) D.transpose s t := by
  apply hasDerivWithinAt_pi.mpr
  intro i
  apply hasDerivWithinAt_pi.mpr
  intro j
  exact hasDerivWithinAt_pi.mp (hasDerivWithinAt_pi.mp hL j) i

/-- The actual moment covariance is reconstructed from the principal fundamental
matrix by uniqueness of the linear covariance equation. -/
theorem covariance_from_fundamental (V : E d → ℝ) (hV : ContDiff ℝ 2 V)
    (p : MomentPath d) (hp : momentSolution V p.mean p.cov)
    (hC : ContinuousOn (fun t => momentCoefficient V (p.mean t) (p.cov t)) (Ici 0))
    (L : ℝ → Mat d) (hL0 : L 0 = 1)
    (hL : ∀ t, 0 ≤ t → HasDerivWithinAt L
      (momentCoefficient V (p.mean t) (p.cov t) * L t) (Ici 0) t)
    (t : ℝ) (ht : 0 ≤ t) : p.cov t = L t * p.cov 0 * (L t).transpose := by
  apply lyapunov_ode_unique (fun r => momentCoefficient V (p.mean r) (p.cov r))
    p.cov (fun r => L r * p.cov 0 * (L r).transpose) hC
    (by simp [hL0]) ?_ ?_ t ht
  · intro r hr
    rw [covariance_normalform V hV _ _ (by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (hp.1 r hr).isHermitian.eq)]
    exact (hp.2 r hr).2
  · intro r hr
    have hh := ((hL r hr).mul_const (p.cov 0)).mul (transpose_deriv (hL r hr))
    convert hh using 1
    simp only [Matrix.transpose_mul]
    noncomm_ring

/-- Reconstruct an actual particle solution from its actual moment flow. -/
theorem affine_particleSolution_from_moment (hN : 0 < N)
    (V : E d → ℝ) (hV : ContDiff ℝ 2 V) (x : Fin N → E d)
    (p : MomentPath d) (hp : IsMomentPathFrom V (empiricalMean x) (empiricalCovariance x) p)
    (hC : ContinuousOn (fun t => momentCoefficient V (p.mean t) (p.cov t)) (Ici 0))
    (L : ℝ → Mat d) (hL0 : L 0 = 1)
    (hL : ∀ t, 0 ≤ t → HasDerivWithinAt L
      (momentCoefficient V (p.mean t) (p.cov t) * L t) (Ici 0) t) :
    IsParticlePathFrom V x (fun t i => p.mean t + matVec (L t) (x i - empiricalMean x)) := by
  let Y : ℝ → Fin N → E d := fun t i => p.mean t + matVec (L t) (x i - empiricalMean x)
  have hm (t : ℝ) : empiricalMean (Y t) = p.mean t :=
    ModelBridges.empiricalMean_affine_lift hN x (p.mean t) (L t)
  have hcov (t : ℝ) (ht : 0 ≤ t) : empiricalCovariance (Y t) = p.cov t := by
    rw [ModelBridges.empiricalCovariance_affine_lift hN x (p.mean t) (L t)]
    rw [← hp.2.2]
    exact (covariance_from_fundamental V hV p hp.1 hC L hL0 hL t ht).symm
  have hc (t : ℝ) (ht : 0 ≤ t) :
      particleCoefficient V (Y t) = momentCoefficient V (p.mean t) (p.cov t) := by
    unfold particleCoefficient momentCoefficient
    rw [hm, hcov t ht]
  refine ⟨⟨fun t ht => (hcov t ht).symm ▸ hp.1.1 t ht, ?_⟩, ?_⟩
  · intro t ht i
    have hmean : HasDerivWithinAt p.mean
        (matVec (momentCoefficient V (p.mean t) (p.cov t)) (p.mean t) -
          meanGradient V (p.mean t) (p.cov t)) (Ici 0) t := by
      rw [mean_normalform]
      exact (hp.1.2 t ht).1
    have hh := hmean.add (fundamental_apply_deriv (hL t ht) (x i - empiricalMean x))
    convert hh using 1
    unfold particleField
    rw [hc t ht, hm, hcov t ht]
    change matVec _ (p.mean t + matVec _ _) - _ = _
    rw [show matVec (momentCoefficient V (p.mean t) (p.cov t))
        (p.mean t + matVec (L t) (x i - empiricalMean x)) =
        matVec (momentCoefficient V (p.mean t) (p.cov t)) (p.mean t) +
        matVec (momentCoefficient V (p.mean t) (p.cov t)) (matVec (L t) (x i - empiricalMean x)) from
      (Matrix.toEuclideanLin (momentCoefficient V (p.mean t) (p.cov t))).map_add _ _]
    abel
  · funext i
    simp only [hL0, hp.2.1, matVec, Matrix.one_mulVec, vec, WithLp.toLp_ofLp]
    abel

/-- Full actual particle well-posedness. The only linear existence input is the
standard theorem for arbitrary continuous matrix coefficients; uniqueness uses
moment uniqueness and ordinary linear-ODE uniqueness proved above. -/
theorem particle_wellPosed_of_moment (hN : 0 < N)
    (V : E d → ℝ) (hV : ContDiff ℝ 2 V) (x : Fin N → E d)
    (hmoment : MomentWellPosed V (empiricalMean x) (empiricalCovariance x))
    (hlinear : LinearMatrixODE.StandardFundamentalMatrixTheorem d)
    (hcontinuous : ∀ p : MomentPath d,
      IsMomentPathFrom V (empiricalMean x) (empiricalCovariance x) p →
      ContinuousOn (fun t => momentCoefficient V (p.mean t) (p.cov t)) (Ici 0)) :
    ParticleWellPosed V x := by
  rcases hmoment with ⟨p, hp, hunique⟩
  have hC := hcontinuous p hp
  rcases hlinear (fun t => momentCoefficient V (p.mean t) (p.cov t)) hC with
    ⟨L, hL0, hL, hunit⟩
  let Y : ℝ → Fin N → E d := fun t i => p.mean t + matVec (L t) (x i - empiricalMean x)
  refine ⟨Y, affine_particleSolution_from_moment hN V hV x p hp hC L hL0 hL, ?_⟩
  intro X hX t ht
  let pX : MomentPath d := ⟨fun s => empiricalMean (X s), fun s => empiricalCovariance (X s)⟩
  have hpX : IsMomentPathFrom V (empiricalMean x) (empiricalCovariance x) pX :=
    ⟨ModelBridges.particleSolution_momentSolution V hV hN X hX.1,
      by change empiricalMean (X 0) = _; rw [hX.2],
      by change empiricalCovariance (X 0) = _; rw [hX.2]⟩
  have hm (r : ℝ) (hr : 0 ≤ r) : empiricalMean (X r) = p.mean r := (hunique pX hpX r hr).1
  have hs (r : ℝ) (hr : 0 ≤ r) : empiricalCovariance (X r) = p.cov r := (hunique pX hpX r hr).2
  have hcoeff (r : ℝ) (hr : 0 ≤ r) : particleCoefficient V (X r) =
      momentCoefficient V (p.mean r) (p.cov r) := by
    unfold particleCoefficient momentCoefficient
    rw [hm r hr, hs r hr]
  funext i
  have hh := affine_representation_from_fundamental
    (fun r => momentCoefficient V (p.mean r) (p.cov r))
    (fun r => meanGradient V (p.mean r) (p.cov r)) p.mean L X hC hL0
    (fun r hr i => by
      have hd := hX.1.2 r hr i
      unfold particleField at hd
      rwa [hcoeff r hr, hm r hr, hs r hr] at hd)
    (fun r hr => by rw [mean_normalform]; exact (hp.1.2 r hr).1)
    hL t ht i
  simpa only [Y, hX.2, hp.2.1] using hh

end Paper38.SourceParticleFlow

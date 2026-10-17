import Paper38.Model

noncomputable section
namespace Paper38.ParticleLimit

open Paper38.Model

/-- The exact Gaussian moment coefficient C(q) in source (6.15)--(6.17). -/
def gaussianCoefficient (V : E d → ℝ) (q : Coordinates d) : Mat d :=
  1 - meanHessian V q.1 (q.2 * q.2) * (q.2 * q.2) -
    outer (meanGradient V q.1 (q.2 * q.2)) q.1

end Paper38.ParticleLimit

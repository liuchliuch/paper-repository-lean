import Paper38.ExternalGaussianAnalysis
import Paper38.ExternalMatrixAnalysis
import Paper38.ExternalODEAnalysis
import Paper38.LinearMatrixODE

/-! Named ordinary external baseline theorem arguments. No fields are source
mobility, stability, global Gaussian dynamics, or statistical conclusions. -/

namespace Paper38.ExternalAnalyticInputs

/-- Precisely identified standard external analysis inputs at source dimension d.
Every field is an ordinary proof argument; no new axiom is declared. -/
structure Baselines (d : ℕ) : Prop where
  standardMaximalODE : GlobalODE.StandardMaximalODETheorem (HilbertCoordinates.Tangent d)
  fundamental : LinearMatrixODE.StandardFundamentalMatrixTheorem d
  decayingFundamental : LinearMatrixODE.StandardDecayingFundamentalMatrixTheorem d
  stein : ExternalGaussianAnalysis.GaussianSteinTheorem d
  sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d
  continuousDependence : ∀ N : ℕ,
    ExternalODEAnalysis.GlobalFlowContinuousDependence (Fin N → Model.E d)

end Paper38.ExternalAnalyticInputs

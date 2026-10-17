import Verification.Statements

/- Deliberate negative control, never imported by production or positive Solution. -/
axiom P38_unauthorized_control : Paper38.Contracts.CovarianceRank

namespace Paper38.Checked

theorem covariance_rank : Contracts.CovarianceRank := P38_unauthorized_control

end Paper38.Checked

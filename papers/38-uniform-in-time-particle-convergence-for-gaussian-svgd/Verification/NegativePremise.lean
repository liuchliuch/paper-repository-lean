import Verification.Statements

/- Deliberate negative control: mathematically true but with an extra premise. -/
namespace Paper38.Checked

theorem covariance_rank : False → Contracts.CovarianceRank := fun h => False.elim h

end Paper38.Checked

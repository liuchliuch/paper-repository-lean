import Verification.Statements

/- Real negative control: one additional False premise changes the target type. -/
namespace Paper33.Checked

theorem s3_exact_failure : False → Contracts.s3_exact_failure := fun h => False.elim h

end Paper33.Checked

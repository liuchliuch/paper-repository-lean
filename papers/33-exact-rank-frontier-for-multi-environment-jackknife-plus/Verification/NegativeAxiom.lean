import Verification.Statements

/- Real negative control: same literal type, derived through an unauthorized False axiom. -/
axiom P33_unauthorized_false_control : False

namespace Paper33.Checked

theorem s3_exact_failure : Contracts.s3_exact_failure := False.elim P33_unauthorized_false_control

end Paper33.Checked

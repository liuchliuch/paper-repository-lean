import Paper20.Certs.CheckedRec.Base
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace Paper20.Cert.Checked43
open Paper20.CheckedRecurrence
theorem verified_16 : checkRows 903 f43List integers 512 32 = true := by decide
end Paper20.Cert.Checked43

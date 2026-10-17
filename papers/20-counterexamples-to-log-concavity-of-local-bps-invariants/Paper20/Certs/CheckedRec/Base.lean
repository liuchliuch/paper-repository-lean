import Paper20.CheckedRecurrence
import Paper20.Certs.N43
import Paper20.Certs.F43

set_option maxRecDepth 200000

namespace Paper20.Cert.Checked43
open Paper20.CheckedRecurrence

def integers : List ℤ := n43List.map Int.ofNat

theorem integers_length : integers.length = 904 := by decide

end Paper20.Cert.Checked43

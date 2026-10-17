import Paper20.Certs.HilbertParts.Branch01
import Paper20.Certs.HilbertParts.Branch02
import Paper20.Certs.HilbertParts.Branch03
import Paper20.Certs.HilbertParts.Branch04
import Paper20.Certs.HilbertParts.Branch05
import Paper20.Certs.HilbertParts.Branch06
import Paper20.Certs.HilbertParts.Branch07
import Paper20.Certs.HilbertParts.Branch08
import Paper20.Certs.HilbertParts.Branch09
import Paper20.Certs.HilbertParts.Branch10
import Paper20.Certs.HilbertParts.Branch11
import Paper20.Certs.HilbertParts.Branch12
import Paper20.Certs.HilbertParts.Branch13
import Paper20.Certs.HilbertParts.Branch14
import Paper20.Certs.HilbertParts.Branch15
import Paper20.Certs.HilbertParts.Branch16
import Paper20.Certs.HilbertParts.Branch17
import Paper20.Certs.HilbertParts.Branch18
import Paper20.Certs.HilbertParts.Branch19
import Paper20.Certs.HilbertParts.Branch20
import Paper20.Certs.HilbertParts.Branch21
import Paper20.Certs.HilbertParts.Branch22
import Paper20.Certs.HilbertParts.Branch23
import Paper20.Certs.HilbertParts.Branch24
import Paper20.Certs.HilbertParts.Branch25
import Paper20.Certs.HilbertParts.Branch26
import Paper20.Certs.HilbertParts.Branch27
import Paper20.Certs.HilbertParts.Branch28
import Paper20.Certs.HilbertParts.Branch29
import Paper20.Certs.HilbertParts.Branch30
import Paper20.Certs.HilbertParts.Branch31
import Paper20.Certs.HilbertParts.Branch32
import Paper20.Certs.HilbertParts.Branch33
import Paper20.Certs.HilbertParts.Branch34
import Paper20.Certs.HilbertParts.Branch35
import Paper20.Certs.HilbertParts.Branch36
import Paper20.Certs.HilbertParts.Branch37
import Paper20.Certs.HilbertParts.Branch38
import Paper20.Certs.HilbertParts.Branch39
import Paper20.Certs.HilbertParts.Branch40
import Paper20.Certs.HilbertParts.Branch41
import Paper20.Certs.HilbertParts.Branch42
import Paper20.Certs.HilbertParts.Branch43
import Paper20.Certs.H43
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace Paper20.Cert.HilbertParts.Tree
open Paper20.HilbertJobs

/-- The complete partition sum (13), through every required coefficient.
No Hilbert or BPS coefficient equality is an input. Every leaf and every
recursive partition branch is checked by the Lean kernel. -/
theorem h43_partition_sum : (Paper20.hilbertArray 43 1).toList = Paper20.Cert.h43List := by
  rw [root_value, value_children root (by decide) (by decide)]
  have hc : children root = [j_43, j_42, j_41, j_40, j_39, j_38, j_37, j_36, j_35, j_34, j_33, j_32, j_31, j_30, j_29, j_28, j_27, j_26, j_25, j_24, j_23, j_22, j_21, j_20, j_19, j_18, j_17, j_16, j_15, j_14, j_13, j_12, j_11, j_10, j_9, j_8, j_7, j_6, j_5, j_4, j_3, j_2, j_1] := by decide
  rw [hc]
  simp only [List.map_cons, List.map_nil, correct_43, correct_42, correct_41, correct_40, correct_39, correct_38, correct_37, correct_36, correct_35, correct_34, correct_33, correct_32, correct_31, correct_30, correct_29, correct_28, correct_27, correct_26, correct_25, correct_24, correct_23, correct_22, correct_21, correct_20, correct_19, correct_18, correct_17, correct_16, correct_15, correct_14, correct_13, correct_12, correct_11, correct_10, correct_9, correct_8, correct_7, correct_6, correct_5, correct_4, correct_3, correct_2, correct_1]
  all_goals decide

end Paper20.Cert.HilbertParts.Tree

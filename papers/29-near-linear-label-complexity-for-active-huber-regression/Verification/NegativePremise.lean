import Paper29.Geometry
import Paper29.Specification
namespace Paper29.Checked
 theorem lemma31 (extra : True) : Specification.Lemma31 := by
  refine ⟨huber_triangle, psi_sub_le, huber_increment, ?_⟩
  intro n w y z hw
  exact weightedHuber_triangle w y z hw
end Paper29.Checked

import Paper20.RelativeCounterexamples
import Paper20.SkeinParity

namespace Paper20.Relative
open Polynomial Paper20.ExternalInput Paper20.HilbertAtZero
noncomputable section

/-- The node's ORIGINAL geometric BPS polynomial is w+1. -/
theorem geometric_node_polynomial (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) : geometricBPSPolynomial data 2 1=1+X := by
  have hb := geometric_bounds data geo mathas 2 1 0 (by decide) (by decide) (by decide)
  have h0 := hb.2.2.1
  have h1 : geometricBPS data 2 1 1=1 := hb.2.2.2
  rw [geometricBPSPolynomial,HilbertAtZero.bpsPolynomial,show deg 2 1=1 by decide]
  simp [Finset.sum_range_succ,h0,h1]

/-- The Hopf-link lowest HOMFLY coefficient z+z^-1, with exactly the
stated sign convention, follows from the supplied original identities and
the proved node BPS expansion. This supplies Remark 2.1's explicit check. -/
theorem geometric_node_homfly (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) :
    data.lowestHOMFLY 2 1=(HilbertAtZero.v-HilbertAtZero.v⁻¹)+
      (HilbertAtZero.v-HilbertAtZero.v⁻¹)⁻¹ := by
  let z := HilbertAtZero.v-HilbertAtZero.v⁻¹
  have hz : z≠0 := origin_difference_ne_zero
  have he := geometric_normalized_ruling data geo mathas 2 1 (by decide) (by decide)
  rw [geometric_node_polynomial data geo mathas,eval₂_add,eval₂_one,eval₂_X] at he
  apply mul_left_cancel₀ hz
  calc
    z*data.lowestHOMFLY 2 1=z^2*data.ruling 2 1 := by
      rw [geo.rutherford 2 1 (by decide) (by decide)]
      dsimp only [z]
      ring
    _=1+z^2 := he.symm
    _=z*(z+z⁻¹) := by field_simp <;> ring

end
end Paper20.Relative

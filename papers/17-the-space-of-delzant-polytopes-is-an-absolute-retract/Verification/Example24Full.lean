import Verification.Example24Pentagon
import Verification.Example24PrismCounterexample

/-! All geometric clauses of the source Example 2.4. -/
noncomputable section
open scoped BigOperators
namespace Paper17.Example24

def raysSumZ : Fin 5 → Fin 2 → ℤ
  | 0 => ![1, 0]
  | 1 => ![1, 1]
  | 2 => ![-1, 1]
  | 3 => ![-1, 0]
  | 4 => ![0, -1]

/-- Every one of the five displayed outward directions is integral and
primitive, in the literal coprime-coordinate sense. -/
theorem raysSum_integral_primitive (i : Fin 5) :
    raysSum i = realRays (fun _ : Unit => raysSumZ i) () ∧
      Int.gcd (raysSumZ i 0) (raysSumZ i 1) = 1 := by
  constructor
  · ext j
    fin_cases i <;> fin_cases j <;> norm_num [raysSum, raysSumZ, realRays, vec2]
  · fin_cases i <;> norm_num [raysSumZ]

/-- The cyclic consecutive pairs have positive determinant, with exactly the
source upper pair having multiplicity two. -/
theorem pentagon_consecutive_determinants (i : Fin 5) :
    det2 (pentagonBasis i 0) (pentagonBasis i 1) = if i = 2 then 2 else 1 := by
  fin_cases i <;> norm_num [pentagonBasis, raysSum, det2, vec2] <;> decide

/-- The explicit source example, including actual product carriers, smooth
refinement, the genuine three-dimensional obstruction and exact 3t error. -/
theorem source_example_2_4 :
    IsDelzant (triangle 1) ∧ IsDelzant (triangle (-1)) ∧
      ¬ IsDelzant ((triangle 1).add (triangle (-1))) ∧
      Fan.Equivalent (NormalFan ((triangle 1).add (triangle (-1)))) (NormalFan pentagon) ∧
      (∀ i, Int.gcd (raysSumZ i 0) (raysSumZ i 1) = 1) ∧
      IsDelzant (prism (triangle 1) 1) ∧ IsDelzant (prism (triangle (-1)) 1) ∧
      ¬ IsDelzant ((prism (triangle 1) 1).add (prism (triangle (-1)) 1)) ∧
      IsDelzant hexagon ∧
      (∀ x : V 2, x ∈ hexagon.carrier ↔ -2 ≤ x 0 ∧ x 0 ≤ 2 ∧ -2 ≤ x 1 ∧
        x 1 ≤ 2 ∧ x 0 + x 1 ≤ 3 ∧ -x 0 + x 1 ≤ 3) ∧
      IsDelzant exampleS ∧
      (NormalFan exampleS).refines (NormalFan (prism (triangle 1) 1)) ∧
      (NormalFan exampleS).refines (NormalFan (prism (triangle (-1)) 1)) ∧
      (∀ x ∈ exampleS.carrier, ‖P17Contract.euclideanCoordinates 3 x‖ ≤ 3) ∧
      ‖P17Contract.euclideanCoordinates 3 (prismPoint (vec2 2 (-2)) 1)‖ = 3 ∧
      (∀ t : ℝ, 0 < t →
        IsDelzant ((prism (triangle 1) 1).add (exampleS.smul t)) ∧
        (NormalFan ((prism (triangle 1) 1).add (exampleS.smul t))).refines
          (NormalFan (prism (triangle 1) 1)) ∧
        (NormalFan ((prism (triangle 1) 1).add (exampleS.smul t))).refines
          (NormalFan (prism (triangle (-1)) 1)) ∧
        P17Contract.euclideanHausdorffDist ((prism (triangle 1) 1).add (exampleS.smul t)).carrier
          (prism (triangle 1) 1).carrier = 3 * t) := by
  obtain ⟨hP, hQ, hS, hSP, hSQ⟩ := source_prisms_delzant_refinement
  exact ⟨triangle_isDelzant 1 (Or.inl rfl), triangle_isDelzant (-1) (Or.inr rfl),
    triangle_sum_not_isDelzant, triangle_sum_five_ray_fan.1,
    fun i => (raysSum_integral_primitive i).2, hP, hQ, prism_triangle_sum_not_isDelzant,
    hexagon_isDelzant, mem_hexagon_iff, hS, hSP, hSQ, exampleS_norm_le_three,
    exampleS_radius_attained.2, fun _ ht => source_prism_perturbation ht⟩

end Paper17.Example24

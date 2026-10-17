import K44K35Free.FiberCounts
import K44K35Free.IdentityCounts
import K44K35Free.GeometrySections
import K44K35Free.GaussianPlanes

/-! Exact exceptional-plane counts and incidence sums for the actual quartic cap. -/
namespace K44K35Free.Geometry

noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F]

/-- Odd field order supplies precisely the characteristic restriction used by the norm count. -/
theorem char_ne_two_of_odd_card (hodd : Odd (Fintype.card F)) : ringChar F ≠ 2 := by
  intro h
  have heven := FiniteField.even_card_of_char_two h
  have hmod := Nat.odd_iff.mp hodd
  omega

/-- The exceptional family is the actual union specified in equation (5). -/
def exceptionalPlanes (α : F) (c : Quartic F) : Finset (Plane F) :=
  identityPlanes α c ∪ Fiber.fiberPlanes

@[simp] theorem mem_exceptionalPlanes (α : F) (c : Quartic F) (E : Plane F) :
    E ∈ exceptionalPlanes α c ↔ Exceptional α c E := by
  simp [exceptionalPlanes,Exceptional]

/-- The two geometric exceptional families have no plane in common. -/
theorem identityPlanes_disjoint_fiberPlanes (α : F) (c : Quartic F) :
    Disjoint (identityPlanes α c) (Fiber.fiberPlanes (F := F)) := by
  apply disjoint_left.mpr
  intro E hI hF
  exact Fiber.identity_fiber_disjoint α c E ((mem_identityPlanes α c E).mp hI)
    ((Fiber.mem_fiberPlanes E).mp hF)

/-- Cardinality of the exceptional union, without any duplicate infinity planes. -/
theorem exceptionalPlanes_card (α : F) (c : Quartic F)
    (hα : IsNonsquare α) (hodd : Odd (Fintype.card F)) :
    (exceptionalPlanes α c).card =
      2 * Fintype.card F ^ 4 + 2 * Fintype.card F ^ 3 + Fintype.card F ^ 2 + 1 := by
  rw [exceptionalPlanes,card_union_of_disjoint (identityPlanes_disjoint_fiberPlanes α c),
    identityPlanes_card α c hα (char_ne_two_of_odd_card hodd),Fiber.fiberPlanes_card]
  ring

/-- Proposition 4, equation (8): the exact total incidence count over all exceptional planes. -/
theorem exceptional_total_incidence (α : F) (c : Quartic F)
    (hα : IsNonsquare α) (hodd : Odd (Fintype.card F)) :
    ∑ E ∈ exceptionalPlanes α c, (planeSection α c E).card =
      2 * Fintype.card F ^ 5 + 2 * Fintype.card F ^ 4 + Fintype.card F ^ 3 := by
  rw [exceptionalPlanes,sum_union (identityPlanes_disjoint_fiberPlanes α c),
    sum_identityPlanes_section_card α c hα (char_ne_two_of_odd_card hodd),
    Fiber.fiber_total_incidence α c]
  ring

/-- Proposition 4, equation (9): every exceptional section has at most `2q` points. -/
theorem exceptional_section_bound (α : F) (c : Quartic F) (E : Plane F)
    (hE : Exceptional α c E) : (planeSection α c E).card ≤ 2 * Fintype.card F := by
  rcases hE with hI | hF
  · rw [identity_plane_section_card α c E hI]
    omega
  · exact Fiber.fiber_section_bound α c E hF

/-- All exact counting clauses of Proposition 4, over an arbitrary finite field of odd order. -/
theorem proposition_4_counts (α : F) (c : Quartic F)
    (hα : IsNonsquare α) (hodd : Odd (Fintype.card F)) :
    Disjoint (identityPlanes α c) (Fiber.fiberPlanes (F := F)) ∧
    (identityPlanes α c).card = Fintype.card F ^ 3 * (Fintype.card F + 1) ∧
    (Fiber.fiberPlanes (F := F)).card =
      Fintype.card F ^ 4 + Fintype.card F ^ 3 + Fintype.card F ^ 2 + 1 ∧
    (∑ E ∈ exceptionalPlanes α c, (planeSection α c E).card) =
      2 * Fintype.card F ^ 5 + 2 * Fintype.card F ^ 4 + Fintype.card F ^ 3 ∧
    (∀ E : Plane F, Exceptional α c E →
      (planeSection α c E).card ≤ 2 * Fintype.card F) ∧
    (∀ E : Plane F, IdentityExceptional α c E →
      (planeSection α c E).card = Fintype.card F) ∧
    (∀ p : Param F, ((identityPlanes α c).filter (fun E => point α c p ∈ E.val)).card =
      Fintype.card F * (Fintype.card F + 1)) := by
  exact ⟨identityPlanes_disjoint_fiberPlanes α c,
    identityPlanes_card α c hα (char_ne_two_of_odd_card hodd),Fiber.fiberPlanes_card,
    exceptional_total_incidence α c hα hodd,exceptional_section_bound α c,
    identity_plane_section_card α c,
    identityPlanes_through_point_card α c hα (char_ne_two_of_odd_card hodd)⟩

/-- Proposition 4 in full: classification outside the exceptional family and all exact count clauses. -/
theorem proposition_4 (α : F) (c : Quartic F)
    (hα : IsNonsquare α) (hodd : Odd (Fintype.card F)) :
    (∀ E : Plane F, ¬ Exceptional α c E → (planeSection α c E).card ≤ 4) ∧
    Disjoint (identityPlanes α c) (Fiber.fiberPlanes (F := F)) ∧
    (identityPlanes α c).card = Fintype.card F ^ 3 * (Fintype.card F + 1) ∧
    (Fiber.fiberPlanes (F := F)).card =
      Fintype.card F ^ 4 + Fintype.card F ^ 3 + Fintype.card F ^ 2 + 1 ∧
    (∑ E ∈ exceptionalPlanes α c, (planeSection α c E).card) =
      2 * Fintype.card F ^ 5 + 2 * Fintype.card F ^ 4 + Fintype.card F ^ 3 ∧
    (∀ E : Plane F, Exceptional α c E →
      (planeSection α c E).card ≤ 2 * Fintype.card F) ∧
    (∀ E : Plane F, IdentityExceptional α c E →
      (planeSection α c E).card = Fintype.card F) ∧
    (∀ p : Param F, ((identityPlanes α c).filter (fun E => point α c p ∈ E.val)).card =
      Fintype.card F * (Fintype.card F + 1)) := by
  exact ⟨nonexceptional_section_card_le_four α c hα, proposition_4_counts α c hα hodd⟩

/-- Remark 5 in the original odd finite-field setting, for subsets of the actual cap. -/
theorem remark_5_point_deletion (α : F) (c : Quartic F)
    (hα : IsNonsquare α) (hodd : Odd (Fintype.card F)) (X : Finset (Param F))
    (hX : ∀ E : Plane F, IdentityExceptional α c E →
      (X ∩ planeSection α c E).card ≤ 4) :
    X.card ≤ 4 * Fintype.card F ^ 2 :=
  point_deletion_obstruction α c hα (char_ne_two_of_odd_card hodd) X hX

/-- The Gaussian count `[5 choose 2]_q`, the number of projective planes through a point of PG(5,q). -/
def pointPlaneCount (q : ℕ) : ℕ :=
  q ^ 6 + q ^ 5 + 2 * q ^ 4 + 2 * q ^ 3 + 2 * q ^ 2 + q + 1

/-- Each actual projective point of the cap lies on this many planes of PG(5,q). -/
theorem planes_through_cap_point_card (α : F) (c : Quartic F) (p : Param F) :
    Nat.card {E : Plane F // point α c p ∈ E.val} = pointPlaneCount (Fintype.card F) := by
  let L : Grassmann F (V F) 1 :=
    ⟨F ∙ point α c p, finrank_span_singleton (point_ne_zero α c p)⟩
  have heq (E : Plane F) : point α c p ∈ E.val ↔ L.val ≤ E.val := by
    exact (Submodule.span_singleton_le_iff_mem _ _).symm
  rw [Nat.card_congr (Equiv.subtypeEquivRight heq),
    Nat.card_congr (grassmannContainingLineEquiv L 2)]
  have hdim : Module.finrank F ((V F) ⧸ L.val) = 5 := by
    have h := L.val.finrank_quotient_add_finrank
    rw [L.property] at h
    have hV : Module.finrank F (V F) = 6 := by simp [V]
    rw [hV] at h
    omega
  simpa [pointPlaneCount,Nat.card_eq_fintype_card] using card_grassmann_two_dim_five hdim

/-- Incidence count of all cap points with all projective planes, needed by the random pairing. -/
theorem all_planes_total_incidence (α : F) (c : Quartic F) :
    letI := Fintype.ofFinite (Plane F)
    ∑ E : Plane F, (planeSection α c E).card =
      Fintype.card F ^ 3 * pointPlaneCount (Fintype.card F) := by
  classical
  letI := Fintype.ofFinite (Plane F)
  change (∑ E : Plane F, (planeSection α c E).card) = _
  simp only [planeSection,card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  have hp (p : Param F) :
      ∑ E : Plane F, (if point α c p ∈ E.val then (1 : ℕ) else 0) =
        pointPlaneCount (Fintype.card F) := by
    rw [← card_filter,← Fintype.card_subtype,← Nat.card_eq_fintype_card]
    exact planes_through_cap_point_card α c p
  simp_rw [hp]
  simp [Param]

/-- The fraction of planes through any projective point is exactly `1/(q³+1)`. -/
theorem plane_card_eq_point_count_mul :
    Nat.card (Plane F) = (Fintype.card F ^ 3 + 1) * pointPlaneCount (Fintype.card F) := by
  have hdim : Module.finrank F (V F) = 6 := by simp [V]
  rw [card_grassmann_three_dim_six hdim]
  simp only [pointPlaneCount,Nat.card_eq_fintype_card]
  ring

/-- Fraction-free form of the uniform plane-section average in equation (21). -/
theorem all_planes_total_incidence_mul (α : F) (c : Quartic F) :
    letI := Fintype.ofFinite (Plane F)
    (∑ E : Plane F, (planeSection α c E).card) * (Fintype.card F ^ 3 + 1) =
      Nat.card (Plane F) * Fintype.card F ^ 3 := by
  rw [all_planes_total_incidence,plane_card_eq_point_count_mul]
  ring

/-- Equation (21): a uniformly chosen actual projective plane meets the cap in
`q³/(q³+1)` points on average. -/
theorem average_plane_section (α : F) (c : Quartic F) :
    letI := Fintype.ofFinite (Plane F)
    (∑ E : Plane F, ((planeSection α c E).card : ℝ)) / Fintype.card (Plane F) =
      (Fintype.card F : ℝ) ^ 3 / ((Fintype.card F : ℝ) ^ 3 + 1) := by
  letI := Fintype.ofFinite (Plane F)
  have hI : (∑ E : Plane F, ((planeSection α c E).card : ℝ)) =
      (Fintype.card F : ℝ) ^ 3 * pointPlaneCount (Fintype.card F) := by
    exact_mod_cast all_planes_total_incidence α c
  have hN : (Fintype.card (Plane F) : ℝ) =
      ((Fintype.card F : ℝ) ^ 3 + 1) * pointPlaneCount (Fintype.card F) := by
    have hh := plane_card_eq_point_count_mul (F := F)
    rw [Nat.card_eq_fintype_card] at hh
    exact_mod_cast hh
  have hp : (pointPlaneCount (Fintype.card F) : ℝ) ≠ 0 := by
    have hp' : 0 < pointPlaneCount (Fintype.card F) := by unfold pointPlaneCount; omega
    exact_mod_cast hp'.ne'
  rw [hI,hN]
  exact mul_div_mul_right _ _ hp

/-- The exact exceptional incidence formula gives the absolute `O(q⁵)` estimate. -/
theorem exceptional_total_incidence_le_nat (α : F) (c : Quartic F)
    (hα : IsNonsquare α) (hodd : Odd (Fintype.card F)) :
    (∑ E ∈ exceptionalPlanes α c, (planeSection α c E).card) ≤ 5 * Fintype.card F ^ 5 := by
  rw [exceptional_total_incidence α c hα hodd]
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  have h4 : Fintype.card F ^ 4 ≤ Fintype.card F ^ 5 := Nat.pow_le_pow_right hq (by omega)
  have h3 : Fintype.card F ^ 3 ≤ Fintype.card F ^ 5 := Nat.pow_le_pow_right hq (by omega)
  omega

/-- There are `O(q⁴)` exceptional planes, with an absolute coefficient. -/
theorem exceptionalPlanes_card_le (α : F) (c : Quartic F)
    (hα : IsNonsquare α) (hodd : Odd (Fintype.card F)) :
    (exceptionalPlanes α c).card ≤ 6 * Fintype.card F ^ 4 := by
  rw [exceptionalPlanes_card α c hα hodd]
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  have h3 : Fintype.card F ^ 3 ≤ Fintype.card F ^ 4 := Nat.pow_le_pow_right hq (by omega)
  have h2 : Fintype.card F ^ 2 ≤ Fintype.card F ^ 4 := Nat.pow_le_pow_right hq (by omega)
  have h0 : 1 ≤ Fintype.card F ^ 4 := one_le_pow₀ hq
  omega

/-- Real form of the exceptional incidence estimate, for the literal uniform averages. -/
theorem exceptional_total_incidence_le (α : F) (c : Quartic F)
    (hα : IsNonsquare α) (hodd : Odd (Fintype.card F)) :
    (∑ E ∈ exceptionalPlanes α c, ((planeSection α c E).card : ℝ)) ≤
      5 * (Fintype.card F : ℝ) ^ 5 := by
  exact_mod_cast exceptional_total_incidence_le_nat α c hα hodd

end
end K44K35Free.Geometry

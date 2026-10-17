import ELV.Basic
import ELV.CostIdentities
import ELV.Oracle
import ELV.Costs
import ELV.BesselLower
import ELV.AdmissibleOptimum
import ELV.UnrestrictedOptimum
import ELV.FourQueryPurifier

/-! The complete operational Theorem 1.1 and both separable attainments.
The numerical identities below are retained as separate arithmetic lemmas. -/

noncomputable section

namespace ELV

/-- Equation (1.2): the two printed forms of `C_adm` coincide. -/
theorem adm_forms (gap : Gap) : Cost.admValue gap = Cost.admValueAlt gap :=
  Cost.admValue_eq_alt gap

/-- Equation (1.1) numerical candidate. -/
theorem sg_form (gap : Gap) : Cost.sgValue gap = 1 / (2 * gap.δ) := rfl

/-- Boundary phase cost (3.10). -/
theorem sg_boundary (gap : Gap) (p : ℝ) (hp : |p - 1 / 2| = gap.δ) :
    1 / (2 * |p - 1 / 2|) = Cost.sgValue gap := by
  unfold Cost.sgValue
  rw [hp]

/-- Fock / rescaling target (4.8)–(4.11). -/
theorem adm_matches_target (gap : Gap) :
    Cost.admValue gap = 1 / (1 - gap.mu) :=
  Cost.admValue_eq gap

/-- Proposition 4.2 free-variable form. -/
theorem one_direction_unbounded (C : ℝ) (hC : 0 < C) :
    ∃ N : ℕ, Real.sqrt N / 2 > C :=
  Bessel.prop42_unbounded C hC

/-- Numerical summary of the printed costs of Theorem 1.1. -/
theorem theorem11_numeric (gap : Gap) :
    Cost.sgValue gap = 1 / (2 * gap.δ) ∧
    Cost.admValue gap = 1 / (1 - gap.mu) ∧
    Cost.admValue gap = (1 + gap.mu) / (4 * gap.δ ^ 2) ∧
    0 < Cost.sgValue gap ∧ 0 < Cost.admValue gap :=
  ⟨Cost.sgValue_eq gap, Cost.admValue_eq gap, Cost.admValue_eq_alt gap,
    Cost.sgValue_pos gap, Cost.admValue_pos gap⟩

/-- Theorem 1.1: both operational infima, both printed restricted forms,
and separable attainment in every nonzero finite workspace. -/
theorem theorem11_full (gap : Gap) (n : ℕ) [NeZero n] :
    Costs.C_sg gap n = ENNReal.ofReal (1/(2*gap.δ)) ∧
    Costs.C_adm gap n = ENNReal.ofReal (1/(1-Real.sqrt (1-4*gap.δ^2))) ∧
    Costs.C_adm gap n = ENNReal.ofReal ((1+gap.mu)/(4*gap.δ^2)) ∧
    (∃ T : Costs.Realization gap n, T.uniformCost=Costs.C_sg gap n ∧
      TopologicalSpace.SeparableSpace T.Private) ∧
    (∃ T : Costs.Realization gap n, T.Admissible ∧ T.uniformCost=Costs.C_adm gap n ∧
      TopologicalSpace.SeparableSpace T.Private) :=
  ⟨Costs.unrestricted_optimum gap,(Costs.admissible_optimum_forms gap).1,
    (Costs.admissible_optimum_forms gap).2,Costs.unrestricted_attained_separable gap,
    Costs.admissible_attained_separable gap⟩

/-- The explicit four-query implementation also attains the unrestricted
infimum and has separable private space. -/
theorem four_query_attained (gap : Gap) (n : ℕ) [NeZero n] :
    (FourQuery.realization gap n).uniformCost=Costs.C_sg gap n ∧
    TopologicalSpace.SeparableSpace (FourQuery.realization gap n).Private := by
  constructor
  · rw [Costs.unrestricted_optimum]
    exact le_antisymm (FourQuery.uniform_cost_le gap)
      (Costs.unrestricted_realization_lower gap _)
  · exact FourQuery.private_separable

end ELV

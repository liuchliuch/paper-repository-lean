import Paper22.Programs
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Compactness and attainment of the actual finite matrix coding programs -/

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace Paper22
variable {n d : ℕ}

local instance compactMatrixCStarAlgebra (k : ℕ) : CStarAlgebra (Matrix (Fin k) (Fin k) ℂ) where

/-- The compact interval of matrix effects, in the usual finite dimensional topology. -/
theorem isCompact_effects : IsCompact {T : Matrix (Fin d) (Fin d) ℂ | IsEffect T} := by
  have he : {T : Matrix (Fin d) (Fin d) ℂ | IsEffect T} =
      {T | 0 ≤ T} ∩ Metric.closedBall 0 1 := by
    ext T
    simp only [Set.mem_setOf_eq, IsEffect, Set.mem_inter_iff, Metric.mem_closedBall,
      dist_zero_right]
    exact and_congr_right fun hT => (CStarAlgebra.norm_le_one_iff_of_nonneg T hT).symm
  rw [he]
  exact (isCompact_closedBall (0 : Matrix (Fin d) (Fin d) ℂ) 1).inter_left
    (isClosed_le continuous_const continuous_id)

abbrev ProgramPair (n d : ℕ) :=
  (Fin n → ℝ) × (Fin n → Matrix (Fin d) (Fin d) ℂ)

/-- Continuity of the true matrix objective in both probability and decoder variables. -/
theorem continuous_programObjective (V : CQChannel n d) :
    Continuous (fun z : ProgramPair n d => programObjective V.states z.1 z.2) := by
  unfold programObjective
  fun_prop

/-- The MC constraints are closed, including their semidefinite inequality. -/
theorem isClosed_mc_feasible (L : ℝ) :
    IsClosed {z : ProgramPair n d | MCFEasable L z.1 z.2} := by
  unfold MCFEasable IsEffect
  simp only [Set.setOf_and, Set.setOf_forall]
  refine (isClosed_iInter fun x => isClosed_le continuous_const (by fun_prop)).inter ?_
  refine (isClosed_eq (by fun_prop) continuous_const).inter ?_
  refine (isClosed_iInter fun x =>
    (isClosed_le continuous_const (by fun_prop)).inter
      (isClosed_le (by fun_prop) continuous_const)).inter ?_
  exact isClosed_le (by fun_prop) continuous_const

/-- The NS constraints are closed, including their exact matrix normalization. -/
theorem isClosed_ns_feasible (M : ℕ) :
    IsClosed {z : ProgramPair n d | NSFeasible M z.1 z.2} := by
  unfold NSFeasible IsEffect
  simp only [Set.setOf_and, Set.setOf_forall]
  refine (isClosed_iInter fun x => isClosed_le continuous_const (by fun_prop)).inter ?_
  refine (isClosed_eq (by fun_prop) continuous_const).inter ?_
  refine (isClosed_iInter fun x =>
    (isClosed_le continuous_const (by fun_prop)).inter
      (isClosed_le (by fun_prop) continuous_const)).inter ?_
  exact isClosed_eq (by fun_prop) continuous_const

/-- All probability coordinates are at most one. -/
theorem probability_le_one {q : Fin n → ℝ} (hq0 : ∀ x, 0 ≤ q x)
    (hq1 : ∑ x, q x = 1) (x : Fin n) : q x ≤ 1 := by
  calc
    q x ≤ ∑ y, q y := Finset.single_le_sum (fun y _ => hq0 y) (Finset.mem_univ x)
    _ = 1 := hq1

/-- Compactness of the MC feasible pairs, without replacing their matrix variables. -/
theorem isCompact_mc_feasible (L : ℝ) :
    IsCompact {z : ProgramPair n d | MCFEasable L z.1 z.2} := by
  let Kq : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ => Set.Icc 0 1)
  let KT : Set (Fin n → Matrix (Fin d) (Fin d) ℂ) :=
    Set.pi Set.univ (fun _ => {T | IsEffect T})
  have hKq : IsCompact Kq := isCompact_univ_pi fun _ => isCompact_Icc
  have hKT : IsCompact KT := isCompact_univ_pi fun _ => isCompact_effects
  refine (hKq.prod hKT).of_isClosed_subset (isClosed_mc_feasible L) ?_
  rintro ⟨q, T⟩ h
  exact ⟨fun x _ => ⟨h.1 x, probability_le_one h.1 h.2.1 x⟩,
    fun x _ => h.2.2.1 x⟩

/-- Compactness of the NS feasible pairs with their equality constraint. -/
theorem isCompact_ns_feasible (M : ℕ) :
    IsCompact {z : ProgramPair n d | NSFeasible M z.1 z.2} := by
  let Kq : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ => Set.Icc 0 1)
  let KT : Set (Fin n → Matrix (Fin d) (Fin d) ℂ) :=
    Set.pi Set.univ (fun _ => {T | IsEffect T})
  have hKq : IsCompact Kq := isCompact_univ_pi fun _ => isCompact_Icc
  have hKT : IsCompact KT := isCompact_univ_pi fun _ => isCompact_effects
  refine (hKq.prod hKT).of_isClosed_subset (isClosed_ns_feasible M) ?_
  rintro ⟨q, T⟩ h
  exact ⟨fun x _ => ⟨h.1 x, probability_le_one h.1 h.2.1 x⟩,
    fun x _ => h.2.2.1 x⟩

/-- The MC infimum is attained whenever the input alphabet and feasible set are nonempty. -/
theorem epsMC_attained (V : CQChannel n d) (hn : 0 < n) {L : ℝ} (hL : 0 ≤ L) :
    ∃ q T, MCFEasable L q T ∧ epsMC V L = programObjective V.states q T := by
  obtain ⟨q₀, T₀, h₀⟩ := mc_feasible_nonempty (d := d) hn hL
  obtain ⟨⟨q, T⟩, h, hmin⟩ := (isCompact_mc_feasible (n := n) (d := d) L).exists_isMinOn
    ⟨(q₀, T₀), h₀⟩ (continuous_programObjective V).continuousOn
  refine ⟨q, T, h, le_antisymm (epsMC_le_objective V h) ?_⟩
  apply le_csInf (show ({e | ∃ q T, MCFEasable L q T ∧
      e = programObjective V.states q T} : Set ℝ).Nonempty from ⟨_, q, T, h, rfl⟩)
  rintro e ⟨q', T', h', rfl⟩
  exact hmin (show (q', T') ∈ {z : ProgramPair n d | MCFEasable L z.1 z.2} from h')

/-- The NS infimum is attained at every positive message count on a nonempty alphabet. -/
theorem epsNS_attained (V : CQChannel n d) (hn : 0 < n) {M : ℕ} (hM : 1 ≤ M) :
    ∃ q T, NSFeasible M q T ∧ epsNS V M = programObjective V.states q T := by
  obtain ⟨q₀, T₀, h₀⟩ := ns_feasible_nonempty (d := d) hn hM
  obtain ⟨⟨q, T⟩, h, hmin⟩ := (isCompact_ns_feasible (n := n) (d := d) M).exists_isMinOn
    ⟨(q₀, T₀), h₀⟩ (continuous_programObjective V).continuousOn
  refine ⟨q, T, h, le_antisymm (epsNS_le_objective V h) ?_⟩
  apply le_csInf (show ({e | ∃ q T, NSFeasible M q T ∧
      e = programObjective V.states q T} : Set ℝ).Nonempty from ⟨_, q, T, h, rfl⟩)
  rintro e ⟨q', T', h', rfl⟩
  exact hmin (show (q', T') ∈ {z : ProgramPair n d | NSFeasible M z.1 z.2} from h')

end Paper22
end

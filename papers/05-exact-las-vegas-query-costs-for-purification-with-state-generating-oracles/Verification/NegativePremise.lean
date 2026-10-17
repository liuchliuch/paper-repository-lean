import Verification.Statements
import ELV.Basic
import ELV.CostIdentities
import ELV.Oracle
import ELV.Costs
import ELV.GramRealization
import ELV.LinePurifier
import ELV.BesselLower
import ELV.SignedGram
import ELV.Stabilize
import ELV.ReciprocalRescale

open ELV

/-! Proofs of the independently stated Comparator obligations. -/
namespace Verification.Certificate

theorem thm11_numeric (gap : Gap) : Specification.Theorem11_Numeric gap := by
  refine ⟨Cost.sgValue_eq gap, Cost.admValue_eq gap, Cost.admValue_eq_alt gap⟩

theorem costs_bound (gap : Gap) (n : ℕ) [NeZero n] :
    Specification.Costs_AccessMonotone gap n := by
  exact Costs.access_monotone gap n

theorem lem21_partial : Specification.Lemma21_Partial := by
  intro V _ _ ι a b h α
  exact Gram.synth_norm_eq h α

theorem lem31_cost : Specification.Lemma31_Cost := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp0 hp1
    exact LinePurifier.cost_low p hp0 hp1
  · intro p hp1 hp2
    exact LinePurifier.cost_high p hp1 hp2
  · intro p
    exact Cost.abs_one_sub_two_p p

theorem prop41_algebra : Specification.Prop41_Algebra := by
  refine ⟨?_, ?_⟩
  · intro a b c d
    exact SignedGram.contrib_sum a b c d
  · intro K _ _ fm gm fp gp
    exact SignedGram.cs_lower fm gm fp gp

theorem rescale_bound : Specification.Rescale_Bound := by
  intro μ t hμ ht ht0
  exact Rescale.fock_bound μ t hμ ht ht0

theorem prop42_unbounded : Specification.Prop42_Unbounded := by
  intro C hC
  exact Bessel.prop42_unbounded C hC

theorem zero_infeasible : Specification.Zero_Infeasible := by
  intro z hz h
  simp at h

theorem lemma21_stabilized : Specification.Lemma21_Stabilized := by
  intro V _ _ _ X a b h
  exact Gram.stabilized_realization_full h

theorem adversary_converse : Specification.Adversary_Converse := by
  intro H Q _ _ _ _ _ _ X O ξ τ v h
  exact Query.operational_converse O ξ τ v h

theorem thm11_restricted (gap : Gap) (n : ℕ) [NeZero n] : Specification.Theorem11_Restricted gap n := by
  exact ⟨(Costs.admissible_optimum_forms gap).1,(Costs.admissible_optimum_forms gap).2,
    Costs.admissible_attained_separable gap⟩

theorem prop41_operational (gap : Gap) (n : ℕ) [NeZero n] : Specification.Prop41_Operational gap n :=
  Costs.admissible_adversary_twoSpaces gap n

theorem remark22 : Specification.Remark22 := Query.bilateralShift_no_transduction

theorem prop42_operational (gap : Gap) (n : ℕ) [NeZero n] : Specification.Prop42_Operational gap n := by
  exact ⟨fun T hT hdir => Costs.oneDirection_infinite T hT hdir,
    Costs.oneDirection_optimum_infinite gap n⟩

theorem lemma31_full : Specification.Lemma31_Full := by
  intro E _ _ _ s hs
  constructor
  · intro p hp0 hp1 hne t ht hst R hRs hRt
    exact Line.line_purifier_public s hs p hp0 hp1 hne t ht hst R hRs hRt
  · intro R ζ hζ hRs
    exact Line.line_purifier_public_endpoint s hs R ζ hζ hRs

theorem thm11_full (gap : Gap) (n : ℕ) [NeZero n] (_extra : False) :
    Specification.Theorem11_Full gap n := ELV.theorem11_full gap n

theorem four_query_full (n : ℕ) [NeZero n] : Specification.FourQuery_Full n := by
  refine ⟨FourQuery.query_count,?_,?_⟩
  · intro O
    exact ⟨FourQuery.exact_run O,FourQuery.pointwise_cost O,FourQuery.catalyst_norm O⟩
  · intro gap
    exact ⟨(ELV.four_query_attained gap n).1,(ELV.four_query_attained gap n).2,
      FourQuery.catalyst_bound gap⟩

theorem introduction_consequences : Specification.Introduction_Consequences := by
  refine ⟨Costs.costs_at_quarter,?_,Costs.costs_dimension_independent⟩
  intro gap n _
  exact ⟨Costs.admissible_remainder_identity gap n,Costs.admissible_asymptotic_remainder_bound gap n⟩

end Verification.Certificate

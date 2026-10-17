import Paper28.RegularChartCover
import Paper28.QuotientCutoffBounds

/-! Standard weights for an actual finite quotient chart cover. Their
positive normalization domain and the derivative-sum bound are constructed
from compactness, before any coordinate projection is chosen. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Metric
variable {G : Type*} [Group G] [DecidableEq G]

def standardChartCenters (C : Finset (RegularSphere G)) (j : C) : CoordinateHilbert G := j.val.val

def standardChartBumps (C : Finset (RegularSphere G)) (j : C) : ContDiffBump (standardChartCenters C j) :=
  regularStandardBump j.val

def standardChartStabilizers (C : Finset (RegularSphere G)) :
    ∀ j : C, Fintype (regularStabilizer (standardChartCenters C j)) :=
  fun j => regularStabilizerFintype j.val
attribute [local instance] standardChartStabilizers

def standardQuotientDenominator (C : Finset (RegularSphere G)) : RegularOrbitQuotient G → ℝ :=
  quotientCutoffDenominator (standardChartCenters C) (standardChartBumps C)

def standardQuotientGradient (C : Finset (RegularSphere G)) : RegularOrbitQuotient G → ℝ :=
  quotientCutoffGradient (standardChartCenters C) (standardChartBumps C)

theorem standardCutoff_one (C : Finset (RegularSphere G)) (j : C) (γ : G) (u : RegularSphere G)
    (hclose : dist u (γ • j.val) ≤ (1/16 : ℝ)) :
    translatedCutoff (standardChartCenters C) (standardChartBumps C) (j,γ) u.val = 1 := by
  apply averagedBump_one
  · intro h
    exact h.property
  · change dist (leftRegular γ⁻¹ u.val) j.val.val ≤ (1/16 : ℝ)
    rw [leftRegular_inv_dist]
    exact hclose

theorem standard_chart_denominator_pos (C : Finset (RegularSphere G))
    (K : Set (RegularOrbitQuotient G))
    (hCover : K ⊆ ⋃ c ∈ C, regularQuotientMap '' ball c (1/16 : ℝ)) :
    ∀ q ∈ K, 0 < standardQuotientDenominator C q := by
  intro q hq
  obtain ⟨u,rfl⟩ := Quotient.mk_surjective q
  obtain ⟨x,hx⟩ := Set.mem_iUnion.mp (hCover hq)
  obtain ⟨hxC,hqx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨v,hv,hvu⟩ := hqx
  have hrel : MulAction.orbitRel G (RegularSphere G) u v := Quotient.exact hvu.symm
  obtain ⟨γ,hγ⟩ := hrel
  let j : C := ⟨x,hxC⟩
  have hclose : dist u (γ • j.val) < (1/16 : ℝ) := by
    rw [← hγ]
    rw [(isometry_smul (RegularSphere G) γ).dist_eq]
    exact hv
  have hOne := standardCutoff_one C j γ u hclose.le
  exact cutoffDenominator_pos (standardChartCenters C) (standardChartBumps C)
    (by intro j; norm_num [standardChartBumps,regularStandardBump])
    (fun j => j.val.property) u.val u.property (j,γ) (by rw [hOne]; norm_num)

/-- The actual finite chart weights have the source's uniform derivative
bound on an open quotient neighborhood. This data precedes delta and every
finite-support projection choice. -/
theorem exists_standard_chart_weights (K : Set (RegularOrbitQuotient G)) (hK : IsCompact K) :
    ∃ C : Finset (RegularSphere G),
      (K ⊆ ⋃ c ∈ C, regularQuotientMap '' ball c (1/16 : ℝ)) ∧
      ∃ C0 : ℝ, 0 < C0 ∧ ∃ U : Set (RegularOrbitQuotient G), IsOpen U ∧ K ⊆ U ∧
        ∀ q ∈ U, 0 < standardQuotientDenominator C q ∧ standardQuotientGradient C q ≤ C0 := by
  obtain ⟨C,hC⟩ := exists_finite_regular_chart_cover K hK
  refine ⟨C,hC,?_⟩
  exact exists_quotient_cutoff_bound (standardChartCenters C) (standardChartBumps C)
    (by intro j; norm_num [standardChartBumps,regularStandardBump]) (fun j => j.val.property)
    K hK (standard_chart_denominator_pos C K hC)

end Paper28

import Paper28.CompactCurrentSupportInput
import Paper28.LiftableSphericalSimplex
import Mathlib.Algebra.Group.Subgroup.Lattice

/-! Finite integer sums of the source projected spherical simplex currents.
Only their standard AK integration objects and support locality are an
external input. The finite-support cover under addition and cancellation is
derived here. No deformation or approximation is an input. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
universe u v
variable {G : Type u} [Group G] [DecidableEq G] [Countable G]

structure SphericalSimplexIntegrationInput (M : SphericalQuotientMetricInput G)
    (I : CompactIntegralCurrentSupportInput.{u,v} (RegularOrbitQuotient G) M.metric) where
  integration : ∀ k, LiftableSphericalSimplex M k → I.Current k
  support_subset : ∀ k (σ : LiftableSphericalSimplex M k),
    I.support (integration k σ) ⊆ σ.projectedPatch

def sphericalPolyhedralCurrents {M : SphericalQuotientMetricInput G}
    {I : CompactIntegralCurrentSupportInput.{u,v} (RegularOrbitQuotient G) M.metric}
    (S : SphericalSimplexIntegrationInput M I) (k : ℕ) : AddSubgroup (I.Current k) :=
  AddSubgroup.closure (Set.range (S.integration k))

theorem sphericalPolyhedral_support_cover {M : SphericalQuotientMetricInput G}
    {I : CompactIntegralCurrentSupportInput.{u,v} (RegularOrbitQuotient G) M.metric}
    (S : SphericalSimplexIntegrationInput M I) (k : ℕ) (C : I.Current k)
    (hC : C ∈ sphericalPolyhedralCurrents S k) :
    ∃ F : Finset (LiftableSphericalSimplex M k), I.support C ⊆ ⋃ σ ∈ F, σ.projectedPatch := by
  classical
  change C ∈ AddSubgroup.closure (Set.range (S.integration k)) at hC
  induction hC using AddSubgroup.closure_induction with
  | mem C hC =>
      obtain ⟨σ,rfl⟩ := hC
      refine ⟨{σ},?_⟩
      simpa only [Finset.mem_singleton, iUnion_iUnion_eq_left] using S.support_subset k σ
  | zero =>
      refine ⟨∅,?_⟩
      rw [I.support_zero]
      exact empty_subset _
  | add C D _ _ hC hD =>
      obtain ⟨F,hF⟩ := hC
      obtain ⟨E,hE⟩ := hD
      refine ⟨F∪E,?_⟩
      intro x hx
      rcases I.support_add_subset C D hx with hx | hx
      · obtain ⟨σ,hσ⟩ := mem_iUnion.mp (hF hx)
        obtain ⟨hσF,hxσ⟩ := mem_iUnion.mp hσ
        exact mem_iUnion.mpr ⟨σ,mem_iUnion.mpr ⟨Finset.mem_union_left E hσF,hxσ⟩⟩
      · obtain ⟨σ,hσ⟩ := mem_iUnion.mp (hE hx)
        obtain ⟨hσE,hxσ⟩ := mem_iUnion.mp hσ
        exact mem_iUnion.mpr ⟨σ,mem_iUnion.mpr ⟨Finset.mem_union_right F hσE,hxσ⟩⟩
  | neg C _ hC =>
      obtain ⟨F,hF⟩ := hC
      exact ⟨F,(I.support_neg_subset C).trans hF⟩

end Paper28

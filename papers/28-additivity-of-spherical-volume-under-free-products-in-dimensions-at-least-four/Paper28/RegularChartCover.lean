import Paper28.RegularCompactChartLifts
import Paper28.NormalizedCutoffs

/-! A finite actual quotient chart cover for a compact subset of X_G.
The chart radii are fixed before choosing a projection error, so the later
partition-derivative constant is independent of that error. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Metric
variable {G : Type*} [Group G] [DecidableEq G]

def regularStandardBump (c : RegularSphere G) : ContDiffBump c.val :=
  ⟨1/16,1/8,by norm_num,by norm_num⟩

def regularStabilizerFintype (c : RegularSphere G) : Fintype (regularStabilizer c.val) :=
  (regularStabilizer_finite c.val c.property).fintype

theorem regularQuotientMap_isOpenMap :
    IsOpenMap (regularQuotientMap : RegularSphere G → RegularOrbitQuotient G) :=
  isOpenMap_quotient_mk'_mul

/-- Fixed inner chart balls cover every compact quotient set using finitely
many lifted centers, with no finite-carrier conclusion assumed. -/
theorem exists_finite_regular_chart_cover (K : Set (RegularOrbitQuotient G)) (hK : IsCompact K) :
    ∃ C : Finset (RegularSphere G),
      K ⊆ ⋃ c ∈ C, regularQuotientMap '' ball c (1/16 : ℝ) := by
  have hc : K ⊆ ⋃ c : RegularSphere G, regularQuotientMap '' ball c (1/16 : ℝ) := by
    intro q _
    obtain ⟨u,rfl⟩ := Quotient.mk_surjective q
    refine Set.mem_iUnion.mpr ⟨u,u,?_ ,rfl⟩
    simp
  exact hK.elim_finite_subcover (fun c => regularQuotientMap '' ball c (1/16 : ℝ))
    (fun c => regularQuotientMap_isOpenMap _ isOpen_ball) hc

end Paper28

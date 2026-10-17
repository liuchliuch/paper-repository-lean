import Paper28.EquivariantSphereDescent
import Paper28.RegularChartCover

/-! Compactness turns the actual finite coordinate support on each lifted
neighborhood into a finite carrier of the exact form (12). -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Metric
variable {G : Type*} [Group G] [DecidableEq G]

def quotientFiniteCarrier (families : Finset (Finset G)) : Set (RegularOrbitQuotient G) :=
  regularQuotientMap '' {u : RegularSphere G | u.val ∈ liftedFiniteCarrier families}

theorem coordinateSphere_mem_quotientFiniteCarrier (families : Finset (Finset G))
    (E : Finset G) (hE : E ∈ families) (u : RegularSphere G)
    (hu : u.val ∈ coordinateSupportSubspace E) :
    regularQuotientMap u ∈ quotientFiniteCarrier families := by
  refine ⟨u,?_,rfl⟩
  refine ⟨1,E,hE,?_⟩
  have he : E.image (fun g => (1 : G)*g) = E := by ext g; simp
  rw [he]
  exact ⟨u.property,hu⟩

theorem exists_finite_carrier_of_local_support
    (U : Set (RegularOrbitQuotient G)) (K : Set (RegularOrbitQuotient G))
    (hK : IsCompact K) (hKU : K ⊆ U)
    (f : CoordinateHilbert G → CoordinateHilbert G)
    (hEq : ∀ γ u, f (leftRegular γ u) = leftRegular γ (f u))
    (hNorm : ∀ u : RegularSphere G, regularQuotientMap u ∈ U → ‖f u.val‖ = 1)
    (hLocal : ∀ u : RegularSphere G, ∃ E : Finset G, ∀ v : RegularSphere G,
      dist v u < (1/2 : ℝ) → f v.val ∈ coordinateSupportSubspace E) :
    ∃ families : Finset (Finset G), (∀ E ∈ families, (1 : G) ∈ E) ∧
      (∀ q : U, q.val ∈ K → equivariantSphereDescent U f hNorm q ∈ quotientFiniteCarrier families) := by
  classical
  choose E hE using hLocal
  let E1 : RegularSphere G → Finset G := fun u => insert 1 (E u)
  have hc : K ⊆ ⋃ u : RegularSphere G, regularQuotientMap '' ball u (1/2 : ℝ) := by
    intro q _
    obtain ⟨u,rfl⟩ := Quotient.mk_surjective q
    exact Set.mem_iUnion.mpr ⟨u,u,by simp,rfl⟩
  obtain ⟨C,hC⟩ := hK.elim_finite_subcover
    (fun u : RegularSphere G => regularQuotientMap '' ball u (1/2 : ℝ))
    (fun _ => regularQuotientMap_isOpenMap _ isOpen_ball) hc
  refine ⟨C.image E1,?_,?_⟩
  · intro D hD
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hD
    exact Finset.mem_insert_self _ _
  · intro q hq
    obtain ⟨u,hu⟩ := Set.mem_iUnion.mp (hC hq)
    obtain ⟨huC,hqu⟩ := Set.mem_iUnion.mp hu
    obtain ⟨v,hv,hvq⟩ := hqu
    have hvU : regularQuotientMap v ∈ U := hvq.symm ▸ q.property
    have hqv : q = ⟨regularQuotientMap v,hvU⟩ := Subtype.ext hvq.symm
    rw [hqv,equivariantSphereDescent_eval U f hEq hNorm v hvU]
    apply coordinateSphere_mem_quotientFiniteCarrier _ (E1 u) (Finset.mem_image.mpr ⟨u,huC,rfl⟩)
    exact coordinateSupportSubspace_mono _ _ (Finset.subset_insert _ _) (hE u v hv)

end Paper28

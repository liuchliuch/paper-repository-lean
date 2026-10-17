import Paper28.ProjectionErrorNeighborhood

/-! Descent of actual equivariant unit-valued maps to the actual orbit
quotient, including the representative evaluation identity. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {G : Type*} [Group G] [DecidableEq G]

def equivariantSphereDescent (U : Set (RegularOrbitQuotient G))
    (f : CoordinateHilbert G → CoordinateHilbert G)
    (hNorm : ∀ u : RegularSphere G, regularQuotientMap u ∈ U → ‖f u.val‖ = 1) :
    U → RegularOrbitQuotient G := fun q =>
  regularQuotientMap ⟨f q.val.out.val,hNorm q.val.out (by
    have h : regularQuotientMap q.val.out = q.val := Quotient.out_eq q.val
    rw [h]
    exact q.property)⟩

theorem equivariantSphereDescent_eval (U : Set (RegularOrbitQuotient G))
    (f : CoordinateHilbert G → CoordinateHilbert G)
    (hEq : ∀ γ u, f (leftRegular γ u) = leftRegular γ (f u))
    (hNorm : ∀ u : RegularSphere G, regularQuotientMap u ∈ U → ‖f u.val‖ = 1)
    (u : RegularSphere G) (hu : regularQuotientMap u ∈ U) :
    equivariantSphereDescent U f hNorm ⟨regularQuotientMap u,hu⟩ =
      regularQuotientMap ⟨f u.val,hNorm u hu⟩ := by
  have h : regularQuotientMap (regularQuotientMap u).out = regularQuotientMap u :=
    Quotient.out_eq _
  obtain ⟨γ,hγ⟩ := (Quotient.exact h : MulAction.orbitRel G (RegularSphere G)
    (regularQuotientMap u).out u)
  unfold equivariantSphereDescent
  apply Quotient.sound
  refine ⟨γ,?_⟩
  apply Subtype.ext
  change leftRegular γ (f u.val) = f (regularQuotientMap u).out.val
  rw [← hEq,← congrArg Subtype.val hγ]
  rfl

theorem equivariantSphereDescent_fixed (U : Set (RegularOrbitQuotient G))
    (f : CoordinateHilbert G → CoordinateHilbert G)
    (hEq : ∀ γ u, f (leftRegular γ u) = leftRegular γ (f u))
    (hNorm : ∀ u : RegularSphere G, regularQuotientMap u ∈ U → ‖f u.val‖ = 1)
    (u : RegularSphere G) (hu : regularQuotientMap u ∈ U) (hFix : f u.val = u.val) :
    equivariantSphereDescent U f hNorm ⟨regularQuotientMap u,hu⟩ = regularQuotientMap u := by
  rw [equivariantSphereDescent_eval U f hEq hNorm u hu]
  congr 1
  exact Subtype.ext hFix

theorem equivariantSphereDescent_eval_of_eq (U : Set (RegularOrbitQuotient G))
    (f : CoordinateHilbert G → CoordinateHilbert G)
    (hEq : ∀ γ u, f (leftRegular γ u) = leftRegular γ (f u))
    (hNorm : ∀ u : RegularSphere G, regularQuotientMap u ∈ U → ‖f u.val‖ = 1)
    (q : U) (u : RegularSphere G) (hu : regularQuotientMap u = q.val) :
    equivariantSphereDescent U f hNorm q =
      regularQuotientMap ⟨f u.val,hNorm u (hu.symm ▸ q.property)⟩ := by
  have he : q = ⟨regularQuotientMap u,hu.symm ▸ q.property⟩ := Subtype.ext hu.symm
  exact (congrArg (equivariantSphereDescent U f hNorm) he).trans
    (equivariantSphereDescent_eval U f hEq hNorm u _)

end Paper28

import Paper28.SphericalLiftedCurrentPresentation

/-! Native integer assembly of the ordinary simplex Stokes/common-face
refinement law, and closure of the actual source polyhedral groups under
boundary. There is no filling or transfer assertion in the foundation. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {G : Type} [Group G] [DecidableEq G] [Countable G]
  {M : SphericalQuotientMetricInput G}
  {I : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) M.metric}
  {J : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere G) inferInstance}
  (S : SphericalSimplexIntegrationInput M I.toCompactIntegralCurrentSupportInput)
  (L : LiftedSphericalSimplexIntegrationInput (M := M) J) (F : CanonicalGlobalCurrentCalculusInput)
  (Gluing : SphericalCurrentGluingInput S L F)

include Gluing in
theorem sphericalChain_boundary_refinement (k : ℕ)
    (z : FreeAbelianGroup (LiftableSphericalSimplex M (k+1))) :
    ∃ w : FreeAbelianGroup (LiftableSphericalSimplex M k),
      liftedSphericalChain L k w = finiteCoordinateBoundary J k (liftedSphericalChain L (k+1) z) := by
  refine FreeAbelianGroup.induction_on z ?_ ?_ ?_ ?_
  · exact ⟨0,by rw [map_zero,map_zero,map_zero]⟩
  · intro σ
    simpa only [liftedSphericalChain,FreeAbelianGroup.lift_apply_of] using Gluing.simplex_stokes_refinement k σ
  · intro z hz
    obtain ⟨w,hw⟩ := hz
    exact ⟨-w,by simpa only [map_neg] using congrArg Neg.neg hw⟩
  · intro z z' hz hz'
    obtain ⟨w,hw⟩ := hz
    obtain ⟨w',hw'⟩ := hz'
    exact ⟨w+w',by simpa only [map_add] using congrArg₂ (fun a b => a+b) hw hw'⟩

include Gluing in
theorem projectedSphericalChain_boundary (k : ℕ)
    (z : FreeAbelianGroup (LiftableSphericalSimplex M (k+1)))
    (w : FreeAbelianGroup (LiftableSphericalSimplex M k))
    (hw : liftedSphericalChain L k w = finiteCoordinateBoundary J k (liftedSphericalChain L (k+1) z)) :
    (projectedSphericalChain S k w).val = I.boundary k (projectedSphericalChain S (k+1) z).val := by
  have he := congrArg (fun C : finiteCoordinateSupportedCurrents J k =>
    (sphericalQuotientCurrentPush (I := I) (J := J) F).push k C.val) hw
  change (sphericalQuotientCurrentPush F).push k (liftedSphericalChain L k w).val =
    (sphericalQuotientCurrentPush F).push k (J.boundary k (liftedSphericalChain L (k+1) z).val) at he
  rw [Gluing.projected_compatibility,← (sphericalQuotientCurrentPush F).boundary_comm,
    Gluing.projected_compatibility] at he
  exact he

include Gluing in
theorem sphericalPolyhedral_boundary_mem (k : ℕ) (C : sphericalPolyhedralCurrents S (k+1)) :
    I.boundary k C.val ∈ sphericalPolyhedralCurrents S k := by
  obtain ⟨z,hz⟩ := projectedSphericalChain_surjective S (k+1) C
  obtain ⟨w,hw⟩ := sphericalChain_boundary_refinement S L F Gluing k z
  have he := projectedSphericalChain_boundary S L F Gluing k z w hw
  rw [hz] at he
  exact he ▸ (projectedSphericalChain S k w).property

def sphericalPolyhedralBoundary (k : ℕ) :
    sphericalPolyhedralCurrents S (k+1) →+ sphericalPolyhedralCurrents S k where
  toFun C := ⟨I.boundary k C.val,sphericalPolyhedral_boundary_mem S L F Gluing k C⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' C D := Subtype.ext (map_add _ _ _)

end Paper28

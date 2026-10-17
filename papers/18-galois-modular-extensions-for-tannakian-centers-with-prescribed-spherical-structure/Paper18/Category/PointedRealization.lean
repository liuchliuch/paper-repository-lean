import Paper18.Category.PointedBoson
import Paper18.Category.PointedCenterPivotal

/-!
# The actual Appendix B obstruction

The objects below are finite-dimensional graded complex vector spaces, with
actual linear morphisms, convolution, coherent bicharacter braiding, explicit
rigid duals and coherent pivotal structures. The scalar computations in the
original Appendix B module enter only after categorical morphisms and traces
have been constructed and computed.
-/

noncomputable section

open Classical CategoryTheory CategoryTheory.MonoidalCategory

namespace Paper18.Category.AppendixBPointed

/-- The fixed modular ambient category is a minimal nondegenerate extension
of its actual centralizer, and admits the explicit pivotal extension of the
prescribed spherical structure, while every spherical pivotal extension
through the fixed inclusion is impossible. The prescribed structure agrees
with the canonical structure on the entire actual symmetric center. -/
theorem appendixB_actual_obstruction :
    IsModular canonicalPivotal ∧
    canonicalPivotal.twistNatIso = twist ∧
    prescribedPivotal.Spherical ∧
    centerPrescribedPivotal = centerCanonicalPivotal ∧
    PreservesPivotal BInclusion prescribedPivotal nonsphericalPivotalExtension ∧
    ¬ nonsphericalPivotalExtension.Spherical ∧
    (∀ J : PivotalStructure Vec, J.Spherical →
      ¬ PreservesPivotal BInclusion prescribedPivotal J) ∧
    (PointedVec.skeleton Paper18.PointedA).fusionBasis.totalFPdim =
      bSkeleton.fusionBasis.totalFPdim * bCenterSkeleton.fusionBasis.totalFPdim :=
  ⟨canonical_modular, canonical_twist, prescribedPivotal_spherical,
    centerPrescribedPivotal_eq_canonical, nonsphericalPivotalExtension_preserves,
    nonsphericalPivotalExtension_not_spherical, prescribedPivotal_no_spherical_extension,
    minimal_extension_dimension⟩

end Paper18.Category.AppendixBPointed

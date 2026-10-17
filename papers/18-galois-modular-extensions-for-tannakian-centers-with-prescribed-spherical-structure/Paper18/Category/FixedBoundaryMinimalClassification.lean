import Paper18.Category.FixedBoundaryTannakianClassification
import Paper18.Category.FixedBoundaryMinimalCentralizer

/-! # Every actual minimal extension has the specified-boundary rigidity

This is the full universal classification assertion of Lemma A.1. The
separate existence assertion is not included in this theorem.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category.FixedBoundary
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [HasKernels A] [HasFiniteBiproducts A]
  [∀ X Y : A, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalPreadditive A] [MonoidalLinear ℂ A]
  [RightRigidCategory A] [Simple (𝟙_ A)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton A ι)
  (TC : TannakianCenter A RepresentationZ2.H)

include TC in
/-- In every actual minimal nondegenerate braided extension of an actual
C₂ Tannakian center, every braided tensor autoequivalence with a specified
monoidal boundary identification has an actual monoidal trivialization
retaining every prescribed component of that identification. -/
theorem minimalBoundary_trivializable
    (E : MinimalBraidedExtension.{v,u,w,v',u',w'} S)
    (P : BoundaryAutoequivalence E.inclusion) : P.Trivializable := by
  letI := S.hasCoequalizers
  letI := E.skeleton.hasCoequalizers
  exact tannakianBoundary_trivializable_of_centralizer S TC E.skeleton E.inclusion P
    E.nondegenerate
    (centralizer_of_minimal_fpdim S TC E.skeleton E.inclusion E.nondegenerate E.minimal)

include TC in
/-- The original componentwise formulation: the actual monoidal natural
isomorphism has precisely the prescribed value on every boundary object. -/
theorem minimalBoundary_exists_monoidal_iso
    (E : MinimalBraidedExtension.{v,u,w,v',u',w'} S)
    (P : BoundaryAutoequivalence E.inclusion) :
    ∃ β : P.functor ≅ 𝟭 E.ambient, NatTrans.IsMonoidal β.hom ∧
      ∀ X : A, β.hom.app (E.inclusion.obj X) = P.boundary.hom.app X := by
  obtain ⟨b⟩ := minimalBoundary_trivializable S TC E P
  exact ⟨b.iso, inferInstance, fun X => BoundaryIso.to_identity_boundary E.inclusion b X⟩

include TC in
/-- The exact universal specified-boundary part of the original Lemma
A.1 statement, with no classification or comparison input premise. -/
theorem lemmaA1_boundary_rigidity :
    ∀ E : MinimalBraidedExtension.{v,u,w,v',u',w'} S,
      ∀ P : BoundaryAutoequivalence E.inclusion, P.Trivializable :=
  fun E P => minimalBoundary_trivializable S TC E P

end Paper18.Category.FixedBoundary

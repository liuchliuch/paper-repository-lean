import Paper18.Category.FixedBoundaryGlue
import Paper18.Category.FixedBoundaryHomogeneousBoundary

/-!
# Ordinary comparison extracted from an actual odd module comparison

The actual odd-component comparison, together with the specified neutral
comparison, constructs an ordinary natural isomorphism on the original
category. No scalar coordinates are supplied to this construction.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [HasKernels C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts C]
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]
  (hχ : ∀ X : C, χ.hom.app X ≫ χ.hom.app X = 𝟙 X)
  (F : C ⥤ C) [F.Monoidal] [F.IsEquivalence] [F.Additive] [F.Linear ℂ]
  (a : SignKernel.inclusion χ ⋙ F ≅ SignKernel.inclusion χ)
  [NatTrans.IsMonoidal a.hom]
  (hF : ∀ X : C, Homogeneous χ 1 X → Homogeneous χ 1 (F.obj X))

/-- Forget an actual odd-component natural isomorphism to the original
ambient category, retaining its actual components. -/
def oddComparisonUnderlying
    (b : homogeneousBoundaryFunctor χ F a 1 hF ≅ 𝟭 (HomogeneousCategory χ 1)) :
    ObjectProperty.ι (Homogeneous χ 1) ⋙ F ≅ ObjectProperty.ι (Homogeneous χ 1) :=
  NatIso.ofComponents
    (fun X => (ObjectProperty.ι (Homogeneous χ 1)).mapIso (b.app X))
    (fun f => b.hom.naturality f)

/-- The ordinary ambient isomorphism is constructed from the actual odd
comparison and the given monoidal neutral boundary. -/
def ordinaryComparisonFromOdd
    (b : homogeneousBoundaryFunctor χ F a 1 hF ≅ 𝟭 (HomogeneousCategory χ 1)) : F ≅ 𝟭 C :=
  glueNatIso χ hχ F a (oddComparisonUnderlying χ F a hF b)

/-- The original specified neutral comparison is preserved pointwise. -/
theorem ordinaryComparisonFromOdd_boundary
    (b : homogeneousBoundaryFunctor χ F a 1 hF ≅ 𝟭 (HomogeneousCategory χ 1))
    (X : SignKernel.Positive χ) :
    (ordinaryComparisonFromOdd χ hχ F a hF b).hom.app X.obj = a.hom.app X :=
  glueNatIso_positive χ hχ F a _ X

/-- The constructed ordinary isomorphism also has the original odd
component, as an equality of actual ambient morphisms. -/
theorem ordinaryComparisonFromOdd_odd
    (b : homogeneousBoundaryFunctor χ F a 1 hF ≅ 𝟭 (HomogeneousCategory χ 1))
    (X : HomogeneousCategory χ 1) :
    (ordinaryComparisonFromOdd χ hχ F a hF b).hom.app X.obj = b.hom.app X :=
  glueNatIso_negative χ hχ F a _ X

end Paper18.Category.FixedBoundary

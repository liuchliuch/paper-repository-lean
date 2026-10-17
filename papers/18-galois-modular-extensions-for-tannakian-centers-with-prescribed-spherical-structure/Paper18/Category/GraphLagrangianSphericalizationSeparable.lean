import Paper18.Category.GraphLagrangianCanonicalSeparableTransport
import Paper18.Category.DiagonalAlgebraEtale
import Paper18.Category.SphericalizationFusion

/-! # Descending canonical separability from actual sphericalization

The constructed spherical structure on sphericalization provides the source
separability section. The actual forgetful functor is retract dominant, so
its actual diagonal comparison descends that section to the original category.
-/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.GraphLagrangian
attribute [local instance 2000] RightRigidCategory.rightDual
open DiagonalAlgebra
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (e : DeligneProduct.map (Sphericalized.forget (C := D)) Sphericalized.forget ⋙
      tensorProductFunctor (C := D) ≅
    tensorProductFunctor (C := Sphericalized D) ⋙ Sphericalized.forget)
  [NatTrans.IsMonoidal e.hom]

/-- The actual sphericalization sphere descends actual diagonal separability
through its actual monoidal tensor-product square. -/
def canonicalSeparableViaSphericalization
    (hpair : ∀ X Y : Sphericalized D,
      e.hom.app (DeligneProduct.externalObject X Y) ≫
        Sphericalized.forget.map (capPairIso X Y).hom =
      (tensorProductFunctor (C := D)).map
        (DeligneProduct.mapPairIso Sphericalized.forget Sphericalized.forget X Y).hom ≫
        (capPairIso (Sphericalized.forget.obj X) (Sphericalized.forget.obj Y)).hom ≫
          Functor.LaxMonoidal.μ Sphericalized.forget X Y) :
    SeparableAlgebra (canonicalAlgebra S) :=
  canonicalSeparableOfTensorSquare (Sphericalized.skeleton S) S Sphericalized.forget e
    hpair Sphericalized.forget_retract_dominant
    (canonicalSeparable (Sphericalized.skeleton S) Sphericalized.pivotalStructure
      Sphericalized.pivotalStructure_spherical)

end Paper18.Category.GraphLagrangian

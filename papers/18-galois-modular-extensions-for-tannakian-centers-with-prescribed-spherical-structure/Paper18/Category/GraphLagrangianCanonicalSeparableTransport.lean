import Paper18.Category.GraphLagrangianCanonicalMapEpi
import Paper18.Category.SeparableAlgebraQuotient
import Paper18.Category.TannakianDeequivariantization

/-! # Actual separability descends along a dominant tensor-product square

The actual canonical algebra comparison is an algebra epimorphism, proved
from rigid cap generators. Pushing the source separability section and
then descending its actual separability element supplies the target section.
-/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category.GraphLagrangian
attribute [local instance 2000] RightRigidCategory.rightDual
open DiagonalAlgebra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (F : C ⥤ D) [F.Braided] [F.Additive] [F.Linear ℂ]
  (e : DeligneProduct.map F F ⋙ tensorProductFunctor (C := D) ≅
    tensorProductFunctor (C := C) ⋙ F)
  [NatTrans.IsMonoidal e.hom]

/-- A dominant actual tensor-product square descends an actual source
separability section to the canonical target algebra. -/
def canonicalSeparableOfTensorSquare
    (hpair : ∀ X Y : C,
      e.hom.app (DeligneProduct.externalObject X Y) ≫ F.map (capPairIso X Y).hom =
        (tensorProductFunctor (C := D)).map (DeligneProduct.mapPairIso F F X Y).hom ≫
          (capPairIso (F.obj X) (F.obj Y)).hom ≫ Functor.LaxMonoidal.μ F X Y)
    (hdom : ∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X)))
    (SA : SeparableAlgebra (canonicalAlgebra S)) :
    SeparableAlgebra (canonicalAlgebra T) := by
  letI := canonicalMap_epi S T F e hpair hdom
  exact (SA.map (DeligneProduct.map F F)).quotient (canonicalMap S T F e)

end Paper18.Category.GraphLagrangian

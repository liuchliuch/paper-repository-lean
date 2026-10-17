import Paper18.Category.GraphLagrangianAdjointMap
import Paper18.Category.DiagonalAlgebraGeneral
import Paper18.Category.DeligneProductMap

/-! # The actual canonical diagonal algebra comparison from a tensor square

The monoidal tensor-product square induces a genuine monoid morphism from
the transported source diagonal algebra to the target diagonal algebra.
The counit and generator formulas are proved by the actual adjunction.
-/
noncomputable section
set_option maxHeartbeats 1000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w v' u' w'
namespace Paper18.Category.GraphLagrangian
attribute [local instance 2000] RightRigidCategory.rightDual
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
  (e : DeligneProduct.map F F ⋙ DiagonalAlgebra.tensorProductFunctor (C := D) ≅
    DiagonalAlgebra.tensorProductFunctor (C := C) ⋙ F)
  [NatTrans.IsMonoidal e.hom]

/-- The actual adjunction transpose is an actual algebra morphism from the
transported source canonical diagonal to the target canonical diagonal. -/
def canonicalMap : (DeligneProduct.map F F).obj (DiagonalAlgebra.canonicalAlgebra S) ⟶
    DiagonalAlgebra.canonicalAlgebra T :=
  AdjointMap.hom (DiagonalAlgebra.tensorProductFunctor (C := C))
    (DiagonalAlgebra.tensorProductRightAdjoint S) (DiagonalAlgebra.tensorProductRightAdjunction S)
    (DiagonalAlgebra.tensorProductFunctor (C := D))
    (DiagonalAlgebra.tensorProductRightAdjoint T) (DiagonalAlgebra.tensorProductRightAdjunction T)
    (DeligneProduct.map F F) F e

/-- The source algebra carries the actual transported monoid structure. -/
instance canonicalMap_sourceMonObj :
    MonObj ((DeligneProduct.map F F).obj (DiagonalAlgebra.canonicalAlgebra S)) :=
  Functor.monObjObj (F := DeligneProduct.map F F) (DiagonalAlgebra.canonicalAlgebra S)

/-- The actual unit and multiplication compatibility follows from the
proved lifted adjunction on monoid objects. -/
instance canonicalMap_isMonHom : IsMonHom (canonicalMap S T F e) :=
  AdjointMap.hom_isMonHom (DiagonalAlgebra.tensorProductFunctor (C := C))
    (DiagonalAlgebra.tensorProductRightAdjoint S) (DiagonalAlgebra.tensorProductRightAdjunction S)
    (DiagonalAlgebra.tensorProductFunctor (C := D))
    (DiagonalAlgebra.tensorProductRightAdjoint T) (DiagonalAlgebra.tensorProductRightAdjunction T)
    (DeligneProduct.map F F) F e

/-- The actual target counit evaluates the actual algebra comparison by
the actual monoidal square and actual source counit. -/
lemma canonicalMap_counit :
    (DiagonalAlgebra.tensorProductFunctor (C := D)).map (canonicalMap S T F e) ≫
      DiagonalAlgebra.canonicalAlgebraCounit T =
    e.hom.app (DiagonalAlgebra.canonicalAlgebra S) ≫
      F.map (DiagonalAlgebra.canonicalAlgebraCounit S) ≫ Functor.OplaxMonoidal.η F :=
  AdjointMap.hom_counit (DiagonalAlgebra.tensorProductFunctor (C := C))
    (DiagonalAlgebra.tensorProductRightAdjoint S) (DiagonalAlgebra.tensorProductRightAdjunction S)
    (DiagonalAlgebra.tensorProductFunctor (C := D))
    (DiagonalAlgebra.tensorProductRightAdjoint T) (DiagonalAlgebra.tensorProductRightAdjunction T)
    (DeligneProduct.map F F) F e

/-- Evaluation on any actual source generator is obtained by applying the
actual underlying tensor functor to its actual source evaluation. -/
lemma canonicalMap_generator {X : DeligneProduct C C}
    (f : X ⟶ DiagonalAlgebra.canonicalAlgebra S) :
    (DiagonalAlgebra.tensorProductFunctor (C := D)).map
      ((DeligneProduct.map F F).map f ≫ canonicalMap S T F e) ≫
        DiagonalAlgebra.canonicalAlgebraCounit T =
      e.hom.app X ≫ F.map
        ((DiagonalAlgebra.tensorProductFunctor (C := C)).map f ≫
          DiagonalAlgebra.canonicalAlgebraCounit S) ≫ Functor.OplaxMonoidal.η F := by
  rw [Functor.map_comp, assoc, canonicalMap_counit]
  have hn := e.hom.naturality f
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  simp only [Functor.map_comp, assoc]

end Paper18.Category.GraphLagrangian

import Paper18.Category.DrinfeldSemisimpleCentrality
import Paper18.Category.DrinfeldSemisimpleGenerator

/-!
# Actual finite semisimplicity of the Drinfeld center

The actual normalized weighted section averages underlying splittings to
central splittings. Finite-dimensional Hom spaces then give actual finite
simple decompositions. The actual induction adjunction provides the finite
generating family, so the complete finite center skeleton is a conclusion.
-/
noncomputable section
universe v u w
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [LeftRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

/-- Every actual monomorphism in the center splits, by averaging its
actual underlying semisimple splitting. -/
def centerSplitMono {Z W : Center C} (f : Z ⟶ W) [Mono f] : SplitMono f := by
  letI : Mono f.f := inferInstanceAs (Mono ((Center.forget C).map f))
  let s := S.splitMono f.f
  refine ⟨centerAverage S J s.retraction, ?_⟩
  apply Center.ext
  change f.f ≫ (inductionNormalizedSection S J W ≫
    inductionUnderlyingMap S s.retraction ≫ (inductionCounit S J Z).f) = 𝟙 Z.1
  calc
    _ = inductionNormalizedSection S J Z ≫ inductionUnderlyingMap S (f.f ≫ s.retraction) ≫
        (inductionCounit S J Z).f := by
      rw [inductionNormalizedSection_naturality_assoc, inductionUnderlyingMap_comp, assoc]
    _ = _ := by
      rw [s.id, inductionUnderlyingMap_id, id_comp, inductionNormalizedSection_counit]

/-- Actual finite simple decompositions in the center, constructed by
endomorphism-dimension descent using the proved central splittings. -/
def centerSimpleDecompositions : SimpleDecompositions (Center C) :=
  SimpleDecompositions.ofSplitMonos (centerSplitMono S J)

/-- The actual finite family of induced underlying simples covers every
actual central simple by a categorical retract. -/
def centerFiniteSimpleGenerator : FiniteSimpleGenerator (Center C) ι :=
  centerGeneratorOfSimpleDecompositions S J (centerSimpleDecompositions S J)

/-- The finite index of actual central simples, formed by actual
isomorphism classes of simple summands of the induced generators. -/
def CenterSimpleIndex : Type w :=
  (centerSimpleDecompositions S J).SimpleIndex (centerFiniteSimpleGenerator S J)

instance centerSimpleIndex_fintype : Fintype (CenterSimpleIndex S J) := by
  dsimp only [CenterSimpleIndex]
  infer_instance

/-- The actual finite semisimple skeleton of the actual Drinfeld center.
No center skeleton, semisimplicity certificate, or factorization is an input. -/
def centerSkeleton : FiniteSemisimpleSkeleton (Center C) (CenterSimpleIndex S J) :=
  (centerSimpleDecompositions S J).skeleton (centerFiniteSimpleGenerator S J)

end Paper18.Category.Drinfeld

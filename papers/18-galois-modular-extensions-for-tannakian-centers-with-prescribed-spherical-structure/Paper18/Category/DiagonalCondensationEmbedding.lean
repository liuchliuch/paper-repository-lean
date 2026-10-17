import Paper18.Category.DiagonalCondensationEmbeddingHom
import Paper18.Category.DeligneProductEmbedding
import Paper18.Category.FactorizationFullyFaithfulCriterion
import Paper18.Category.SeparableModulesBiproducts

/-! # Genuine fully faithful free embeddings for a diagonal algebra

The actual diagonal Hom calculation proves simple Hom dimensions, from which
bijectivity of the actual functor map is derived. In particular neither
faithfulness nor fullness is supplied as an algebra hypothesis.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u v' u' vE uE w wC wD
namespace Paper18.Category.DiagonalCondensation
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  {A : DeligneProduct C D} [MonObj A]

/-- The actual free functor on the first Deligne factor. -/
def leftFreeFunctor : C ⥤ Mod_ (DeligneProduct C D) A :=
  DeligneProduct.left ⋙ InternalModule.freeFunctor

/-- The actual free functor on the second Deligne factor. -/
def rightFreeFunctor : D ⥤ Mod_ (DeligneProduct C D) A :=
  DeligneProduct.right ⋙ InternalModule.freeFunctor

instance leftFreeFunctor_additive : (leftFreeFunctor (A := A)).Additive := by
  dsimp [leftFreeFunctor]; infer_instance
instance leftFreeFunctor_linear : (leftFreeFunctor (A := A)).Linear ℂ := by
  dsimp [leftFreeFunctor]; infer_instance
instance rightFreeFunctor_additive : (rightFreeFunctor (A := A)).Additive := by
  dsimp [rightFreeFunctor]; infer_instance
instance rightFreeFunctor_linear : (rightFreeFunctor (A := A)).Linear ℂ := by
  dsimp [rightFreeFunctor]; infer_instance

section Diagonal
variable [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {E : Type uE} [Category.{vE} E] [Preadditive E] [Linear ℂ E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalLinear ℂ E]
  [RightRigidCategory E] [HasKernels E] [HasFiniteBiproducts E]
  [∀ X Y : E, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ E)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton E ι)
  (F : E ⥤ C) [F.Monoidal] [F.Full] [F.Faithful] [F.Additive] [F.Linear ℂ]
  (G : E ⥤ D) [G.Monoidal] [G.Full] [G.Faithful] [G.Additive] [G.Linear ℂ]
  (e : A ≅ ⨁ fun i => pair (F.obj (S.simpleObject i))
    (G.obj (dual E (S.simpleObject i))))

variable [HasKernels C] [HasFiniteBiproducts C]
  {κ : Type wC} [Fintype κ] (T : FiniteSemisimpleSkeleton C κ)

/-- The first-factor free functor is actually fully faithful. -/
def leftFreeFunctorFullyFaithful : (leftFreeFunctor (A := A)).FullyFaithful :=
  T.fullyFaithfulOfSimpleHomDimensions (leftFreeFunctor (A := A)) fun i j =>
    (finrank_freeLeftHom S F G e (T.simpleObject i) (T.simpleObject j)).trans
      (T.finrank_simple_hom_simple i j)

variable [HasKernels D] [HasFiniteBiproducts D]
  {ν : Type wD} [Fintype ν] (U : FiniteSemisimpleSkeleton D ν)

/-- The second-factor free functor is actually fully faithful. -/
def rightFreeFunctorFullyFaithful : (rightFreeFunctor (A := A)).FullyFaithful :=
  U.fullyFaithfulOfSimpleHomDimensions (rightFreeFunctor (A := A)) fun i j =>
    (finrank_freeRightHom S F G e (U.simpleObject i) (U.simpleObject j)).trans
      (U.finrank_simple_hom_simple i j)

end Diagonal
end Paper18.Category.DiagonalCondensation

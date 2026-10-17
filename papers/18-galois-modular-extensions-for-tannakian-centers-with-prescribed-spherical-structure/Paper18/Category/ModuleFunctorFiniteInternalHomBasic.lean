import Paper18.Category.ModuleFunctorFiniteRegular
import Paper18.Category.ModuleFunctorAdjoint

/-! # Actual internal Hom objects for finite semisimple module actions

The action-on-an-object functor is a genuine strong module functor.
Its right adjoint is constructed from actual finite Hom bases, and the
native strong module structure is derived from rigid mates. Thus internal
Hom objects and their actual evaluation/coevaluation are constructed,
without assuming the existence of representing objects.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u vM uM w
namespace Paper18.Category.ModuleInternalHom
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasFiniteBiproducts M] [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalLeftAction C M]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ]
  [∀ n : M, (MonoidalLeftAction.actionRight C n).Additive]
  [∀ n : M, (MonoidalLeftAction.actionRight C n).Linear ℂ]

/-- The actual internal-Hom right adjoint, with derived genuine strong
module, additive, and complex-linear structure. -/
def internalHomFunctor (n : M) : ModuleFunctor.Bundled C M C :=
  ModuleFunctor.semisimpleRightAdjoint S (ModuleFunctor.actionObject n)

/-- The actual representing internal-Hom object. -/
def homObject (n m : M) : C := (internalHomFunctor S n).toFunctor.obj m

/-- The actual action/internal-Hom adjunction. -/
def adjunction (n : M) : MonoidalLeftAction.actionRight C n ⊣
    (internalHomFunctor S n).toFunctor :=
  ModuleFunctor.semisimpleRightAdjunction S (ModuleFunctor.actionObject n)

/-- The actual linear universal property of internal Hom. -/
def homLinearEquiv (n m : M) (X : C) :
    (X ⊙ₗ n ⟶ m) ≃ₗ[ℂ] (X ⟶ homObject S n m) :=
  DiagonalAlgebra.semisimpleAdjointHomLinearEquiv S
    (MonoidalLeftAction.actionRight C n) X m

@[simp] lemma adjunction_homEquiv (n m : M) (X : C) :
    (adjunction S n).homEquiv X m = (homLinearEquiv S n m X).toEquiv :=
  DiagonalAlgebra.semisimpleRightAdjunction_homEquiv S
    (MonoidalLeftAction.actionRight C n) X m

/-- Genuine evaluation, the actual adjunction counit. -/
def evaluation (n m : M) : homObject S n m ⊙ₗ n ⟶ m := (adjunction S n).counit.app m

/-- Genuine coevaluation, the actual adjunction unit. -/
def coevaluation (n : M) (X : C) : X ⟶ homObject S n (X ⊙ₗ n) :=
  (adjunction S n).unit.app X

/-- Evaluation and coevaluation satisfy the actual first triangle. -/
lemma coevaluation_evaluation (n : M) (X : C) :
    (coevaluation S n X) ⊵ₗ n ≫ evaluation S n (X ⊙ₗ n) = 𝟙 _ :=
  (adjunction S n).left_triangle_components X

/-- Evaluation and coevaluation satisfy the actual second triangle. -/
lemma evaluation_coevaluation (n m : M) :
    coevaluation S n (homObject S n m) ≫
      (internalHomFunctor S n).toFunctor.map (evaluation S n m) = 𝟙 _ :=
  (adjunction S n).right_triangle_components m

/-- The actual internal endomorphism object. -/
def endObject (n : M) : C := homObject S n n

end Paper18.Category.ModuleInternalHom

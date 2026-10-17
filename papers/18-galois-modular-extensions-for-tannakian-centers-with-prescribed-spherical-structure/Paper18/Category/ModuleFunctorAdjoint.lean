import Paper18.Category.ModuleFunctorAdjointNaturality
import Paper18.Category.DiagonalAlgebraSemisimpleAdjoint
import Paper18.Category.ModuleFunctorFiniteBasic

/-! # Actual chosen right adjoints of finite semisimple module functors

The ordinary right adjoint is assembled from actual finite Hom bases.
Its native strong module structure and the module naturality of the
adjunction unit and counit are derived, with no module-adjoint existence
or semisimplicity of a module-functor category supplied as an assumption.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u v' u' v'' u'' w
namespace Paper18.Category.ModuleFunctor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {M : Type u'} [Category.{v'} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M] [MonoidalLeftAction C M]
  [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  {N : Type u''} [Category.{v''} N] [Preadditive N] [Linear ℂ N]
  [HasFiniteBiproducts N] [MonoidalLeftAction C N]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton M ι)

/-- The actual chosen right adjoint of an actual finite semisimple module
functor, carrying the derived native strong module structure. -/
def semisimpleRightAdjoint (F : Bundled C M N) : Bundled C N M where
  toFunctor := DiagonalAlgebra.semisimpleRightAdjoint S F.toFunctor
  leftLinear := rightAdjointLeftLinear (C := C) F.toFunctor
    (DiagonalAlgebra.semisimpleRightAdjunction S F.toFunctor)
  additive := inferInstance
  linear := inferInstance

/-- The actual ordinary adjunction underlying the chosen module adjoint. -/
def semisimpleRightAdjunction (F : Bundled C M N) :
    F.toFunctor ⊣ (semisimpleRightAdjoint S F).toFunctor :=
  DiagonalAlgebra.semisimpleRightAdjunction S F.toFunctor

@[simp]
lemma semisimpleRightAdjoint_toFunctor (F : Bundled C M N) :
    (semisimpleRightAdjoint S F).toFunctor =
      DiagonalAlgebra.semisimpleRightAdjoint S F.toFunctor := rfl

/-- The chosen adjunction unit is genuinely module natural. -/
instance semisimpleRightAdjunction_unit_moduleNatural (F : Bundled C M N) :
    IsModuleNatural C (semisimpleRightAdjunction S F).unit :=
  rightAdjointUnit_moduleNatural (C := C) F.toFunctor
    (DiagonalAlgebra.semisimpleRightAdjunction S F.toFunctor)

/-- The chosen adjunction counit is genuinely module natural. -/
instance semisimpleRightAdjunction_counit_moduleNatural (F : Bundled C M N) :
    IsModuleNatural C (semisimpleRightAdjunction S F).counit :=
  rightAdjointCounit_moduleNatural (C := C) F.toFunctor
    (DiagonalAlgebra.semisimpleRightAdjunction S F.toFunctor)

end Paper18.Category.ModuleFunctor

import Paper18.Category.ModuleFunctorFiniteInternalHomTensorMonad
import Paper18.Category.MonoidalOppositeFusion

/-! # The actual right algebra monad and its native algebra object

The algebra in the monoidal opposite has the original multiplication.
Its native left modules have actual right action maps in the original
category. No commutativity or braiding is used in this orientation change.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj
attribute [local instance] endofunctorMonoidalCategory
universe v u
namespace Paper18.Category.ModuleInternalHom
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The original algebra is an actual algebra in the monoidal opposite. -/
instance rightModuleAlgebra (A : C) [MonObj A] : MonObj (mop A) where
  one := η[A].mop
  mul := μ[A].mop
  one_mul := by
    apply Quiver.Hom.unmop_inj
    change (A ◁ η[A]) ≫ μ[A] = (ρ_ A).hom
    exact MonObj.mul_one A
  mul_one := by
    apply Quiver.Hom.unmop_inj
    change η[A] ▷ A ≫ μ[A] = (λ_ A).hom
    exact MonObj.one_mul A
  mul_assoc := by
    apply Quiver.Hom.unmop_inj
    change (A ◁ μ[A]) ≫ μ[A] = (α_ A A A).inv ≫ μ[A] ▷ A ≫ μ[A]
    apply (cancel_epi (α_ A A A).hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using (MonObj.mul_assoc A).symm

variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The actual monad obtained by right tensoring with an actual algebra. -/
def rightTensorMonad (A : C) [MonObj A] : Monad C :=
  Monad.ofMon ((ModuleFunctor.forget (C := C) (M := C) (N := C)).mapMon.obj
    ((ModuleFunctor.actionFunctor (C := C) (M := C)).mapMon.obj ⟨A⟩))

@[simp] theorem rightTensorMonad_obj (A : C) [MonObj A] (X : C) :
    (rightTensorMonad A).obj X = X ⊗ A := rfl

@[simp] theorem rightTensorMonad_map (A : C) [MonObj A] {X Y : C} (f : X ⟶ Y) :
    (rightTensorMonad A).map f = f ▷ A := rfl

/-- The actual monad unit inserts the actual algebra unit on the right. -/
@[simp] theorem rightTensorMonad_unit (A : C) [MonObj A] (X : C) :
    (rightTensorMonad A).η.app X = (ρ_ X).inv ≫ (X ◁ η[A]) := by
  change 𝟙 X ≫ ((ρ_ X).inv ≫ (X ◁ η[A])) = _
  simp

/-- The actual monad multiplication is the actual algebra multiplication
after the ambient associator. -/
@[simp] theorem rightTensorMonad_mul (A : C) [MonObj A] (X : C) :
    (rightTensorMonad A).μ.app X = (α_ X A A).hom ≫ (X ◁ μ[A]) := by
  change 𝟙 ((X ⊗ A) ⊗ A) ≫ ((α_ X A A).hom ≫ (X ◁ μ[A])) = _
  simp

end Paper18.Category.ModuleInternalHom

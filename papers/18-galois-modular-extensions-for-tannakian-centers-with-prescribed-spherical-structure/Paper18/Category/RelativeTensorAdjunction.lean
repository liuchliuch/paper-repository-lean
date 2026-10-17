import Paper18.Category.RelativeTensorFree

/-! # The actual free-forget adjunction for internal modules -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory
open scoped MonObj
universe v u
namespace Paper18.Category.RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {A : C} [MonObj A]

/-- The actual free-module universal property forms an adjunction, with
its naturality derived from the actual free lifts. -/
def freeForgetAdjunction : (InternalModule.freeFunctor (A := A)) ⊣ Mod_.forget (D := C) A :=
  Adjunction.mkOfHomEquiv
    { homEquiv X M := (freeHomLinearEquiv X M).toEquiv
      homEquiv_naturality_left_symm {X' X M} f g := by
        apply Mod_.Hom.ext
        change (A ◁ (f ≫ g)) ≫ γ[A,M.X] =
          (A ◁ f) ≫ (A ◁ g) ≫ γ[A,M.X]
        rw [whiskerLeft_comp, Category.assoc]
      homEquiv_naturality_right f g := by
        change freeUnit _ ≫ f.hom ≫ g.hom = (freeUnit _ ≫ f.hom) ≫ g.hom
        rw [Category.assoc] }

@[simp]
theorem freeForgetAdjunction_unit (X : C) :
    (freeForgetAdjunction (A := A)).unit.app X = freeUnit X := by
  change freeUnit X ≫ 𝟙 _ = freeUnit X
  rw [Category.comp_id]

@[simp]
theorem freeForgetAdjunction_counit (M : Mod_ C A) :
    (freeForgetAdjunction (A := A)).counit.app M = InternalModule.actionHom M := by
  apply Mod_.Hom.ext
  change (A ◁ 𝟙 M.X) ≫ γ[A,M.X] = γ[A,M.X]
  rw [MonoidalCategory.whiskerLeft_id, Category.id_comp]

end Paper18.Category.RelativeTensor

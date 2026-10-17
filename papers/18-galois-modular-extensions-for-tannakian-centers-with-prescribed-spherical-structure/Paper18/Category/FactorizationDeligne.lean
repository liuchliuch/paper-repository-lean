import Paper18.Category.FactorizationBasic
import Paper18.Category.DrinfeldBiproducts
import Paper18.Category.LinearTensorAdditive

/-! # The actual complex-linear Deligne factorization functor

The tensor-product Hom spaces and the additive envelope are essential here.
The ordinary product bifunctor alone does not have the correct Hom spaces.
-/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped TensorProduct
universe v u
namespace Paper18.Category.Drinfeld
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] [BraidedCategory C]

def factorizationCurried : C ⥤ C ⥤ Center C where
  obj X := negative C ⋙ tensorLeft ((positive C).obj X)
  map {X X'} f :=
    { app := fun Y => (positive C).map f ▷ (negative C).obj Y
      naturality := by
        intro Y Y' g
        dsimp
        rw [← MonoidalCategory.tensorHom_def, ← MonoidalCategory.tensorHom_def'] }
  map_id X := by ext; simp
  map_comp f g := by ext; simp

instance : (factorizationCurried C).Additive where
  map_add := by intros; ext; simp [factorizationCurried]

instance : (factorizationCurried C).Linear ℂ where
  map_smul := by intros; ext; simp [factorizationCurried]

instance (X : C) : ((factorizationCurried C).obj X).Additive := by
  change (negative C ⋙ tensorLeft ((positive C).obj X)).Additive
  infer_instance

instance (X : C) : ((factorizationCurried C).obj X).Linear ℂ := by
  change (negative C ⋙ tensorLeft ((positive C).obj X)).Linear ℂ
  infer_instance

def linearFactorization : LinearTensor C C ⥤ Center C :=
  LinearTensor.lift (factorizationCurried C)

instance : (linearFactorization C).Additive := inferInstanceAs
  ((LinearTensor.lift (factorizationCurried C)).Additive)
instance : (linearFactorization C).Linear ℂ := inferInstanceAs
  ((LinearTensor.lift (factorizationCurried C)).Linear ℂ)

@[simp] lemma linearFactorization_obj (X Y : C) :
    (linearFactorization C).obj ⟨X,Y⟩ = (positive C).obj X ⊗ (negative C).obj Y := rfl

@[simp] lemma linearFactorization_map_tmul {X X' Y Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (linearFactorization C).map
      (show (⟨X,Y⟩ : LinearTensor C C) ⟶ ⟨X',Y'⟩ from f ⊗ₜ[ℂ] g) =
      (positive C).map f ⊗ₘ (negative C).map g := by
  change (positive C).map f ▷ (negative C).obj Y ≫
    (positive C).obj X' ◁ (negative C).map g = _
  exact (MonoidalCategory.tensorHom_def _ _).symm

variable [HasFiniteBiproducts C]

def deligneFactorization : DeligneProduct C C ⥤ Center C :=
  DeligneProduct.lift (factorizationCurried C)

instance : (deligneFactorization C).Additive := inferInstanceAs
  ((DeligneProduct.lift (factorizationCurried C)).Additive)
instance : (deligneFactorization C).Linear ℂ := inferInstanceAs
  ((DeligneProduct.lift (factorizationCurried C)).Linear ℂ)

end Paper18.Category.Drinfeld

import Paper18.Category.LinearTensorLift
import Mathlib.CategoryTheory.Preadditive.Mat

/-! # The additive envelope for the linear tensor product -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe v u v' u' v'' u''
namespace Paper18.Category

section MatLinear
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]

instance linearMatHomModule (X Y : Mat_ C) : Module ℂ (X ⟶ Y) :=
  inferInstanceAs (Module ℂ (∀ i j, X.X i ⟶ Y.X j))

@[simp] lemma linearMat_smul_apply {X Y : Mat_ C} (r : ℂ) (f : X ⟶ Y)
    (i : X.ι) (j : Y.ι) : (r • f) i j = r • f i j := rfl

instance linearMatCategory : Linear ℂ (Mat_ C) where
  smul_comp X Y Z r f g := by
    ext i k
    change (∑ j, (r • f i j) ≫ g j k) = r • (∑ j, f i j ≫ g j k)
    simp [Finset.smul_sum]
  comp_smul X Y Z f r g := by
    ext i k
    change (∑ j, f i j ≫ (r • g j k)) = r • (∑ j, f i j ≫ g j k)
    simp [Finset.smul_sum]

instance [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] (X Y : Mat_ C) :
    FiniteDimensional ℂ (X ⟶ Y) :=
  inferInstanceAs (FiniteDimensional ℂ (∀ i j, X.X i ⟶ Y.X j))

instance : (Mat_.embedding C).Linear ℂ where
  map_smul _ _ := rfl

variable {E : Type u''} [Category.{v''} E] [Preadditive E] [Linear ℂ E]
  [HasFiniteBiproducts E] (F : C ⥤ E) [F.Additive] [F.Linear ℂ]

/-- An additive-envelope lift with independent source and target universes. -/
def linearMatLift : Mat_ C ⥤ E where
  obj X := ⨁ fun i => F.obj (X.X i)
  map f := biproduct.matrix fun i j => F.map (f i j)
  map_id X := by
    ext i j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  map_comp f g := by
    ext i j
    simp [Mat_.comp_apply, biproduct.lift_desc]

instance : (linearMatLift F).Additive where
  map_add := by
    intros
    dsimp [linearMatLift]
    ext i j
    simp

instance : (linearMatLift F).Linear ℂ where
  map_smul := by
    intros
    dsimp [linearMatLift]
    ext i j
    simp

end MatLinear

/-- The additive linear tensor product. For finite semisimple categories
its complete simple-pair presentation will identify it with their Deligne
product. -/
abbrev DeligneProduct (C : Type u) (D : Type u') [Category.{v} C] [Preadditive C]
    [Linear ℂ C] [Category.{v'} D] [Preadditive D] [Linear ℂ D] :=
  Mat_ (LinearTensor C D)

namespace DeligneProduct
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  {E : Type u''} [Category.{v''} E] [Preadditive E] [Linear ℂ E]
  [HasFiniteBiproducts E] (F : C ⥤ D ⥤ E) [F.Additive] [F.Linear ℂ]
  [∀ X : C, (F.obj X).Additive] [∀ X : C, (F.obj X).Linear ℂ]

/-- The actual additive linear lift of a separately linear bifunctor. -/
def lift : DeligneProduct C D ⥤ E := linearMatLift (LinearTensor.lift F)
instance : (lift F).Additive := inferInstanceAs ((linearMatLift (LinearTensor.lift F)).Additive)
instance : (lift F).Linear ℂ := inferInstanceAs ((linearMatLift (LinearTensor.lift F)).Linear ℂ)

end DeligneProduct
end Paper18.Category

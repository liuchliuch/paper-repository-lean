import Paper18.Category.SphericalizationKernelTensorHom
import Mathlib.CategoryTheory.Monoidal.Types.Coyoneda

/-! # Canonical tensor identities of actual unit points -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.Monoidal
universe v u v' u'
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

lemma unitPointTensor_map
    (F : C ⥤ D) [F.Monoidal] {X Y : C} (f : 𝟙_ C ⟶ X) (g : 𝟙_ C ⟶ Y) :
    unitPointTensor (ε F ≫ F.map f) (ε F ≫ F.map g) ≫ μ F X Y =
      ε F ≫ F.map (unitPointTensor f g) := by
  unfold unitPointTensor
  rw [← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [μ_natural, ε_tensorHom_comp_μ_assoc]
  rw [← leftUnitor_inv_naturality_assoc]
  simp only [Iso.inv_hom_id_assoc, ← CategoryTheory.Functor.map_comp]

lemma unitPointTensor_assoc {X Y Z : C}
    (f : 𝟙_ C ⟶ X) (g : 𝟙_ C ⟶ Y) (h : 𝟙_ C ⟶ Z) :
    unitPointTensor (unitPointTensor f g) h ≫ (α_ X Y Z).hom =
      unitPointTensor f (unitPointTensor g h) := by
  have hc := Functor.LaxMonoidal.associativity
    (CategoryTheory.coyoneda.obj (Opposite.op (𝟙_ C))) X Y Z
  exact congrFun hc ((f, g), h)

@[simp] lemma unitPointTensor_left {X : C} (f : 𝟙_ C ⟶ X) :
    unitPointTensor (𝟙 (𝟙_ C)) f ≫ (λ_ X).hom = f := by simp [unitPointTensor]

@[simp] lemma unitPointTensor_right {X : C} (f : 𝟙_ C ⟶ X) :
    unitPointTensor f (𝟙 (𝟙_ C)) ≫ (ρ_ X).hom = f := by
  simp [unitPointTensor, unitors_inv_equal]

lemma unitPointTensor_braiding [BraidedCategory C] {X Y : C}
    (f : 𝟙_ C ⟶ X) (g : 𝟙_ C ⟶ Y) :
    unitPointTensor f g ≫ (β_ X Y).hom = unitPointTensor g f := by
  rw [unitPointTensor, Category.assoc, BraidedCategory.braiding_naturality]
  simp only [braiding_tensorUnit_left, Category.assoc]
  rw [← unitors_inv_equal]
  simp [unitPointTensor]

end Paper18.Category

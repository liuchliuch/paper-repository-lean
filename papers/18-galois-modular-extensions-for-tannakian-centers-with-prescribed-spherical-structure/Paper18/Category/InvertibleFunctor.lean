import Paper18.Category.InvertibleObjects
import Mathlib.CategoryTheory.Monoidal.Functor

/-! # Actual tensor inverses under strong monoidal functors -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor.Monoidal
universe v u v' u'
namespace Paper18.Category.TensorInverse
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  {X : C} (A : TensorInverse X) (F : C ⥤ D) [F.Monoidal]

/-- The actual inverse and actual unit isomorphisms transported by the
strong monoidal structure. -/
def map : TensorInverse (F.obj X) where
  inverse := F.obj A.inverse
  left := μIso F A.inverse X ≪≫ F.mapIso A.left ≪≫ (εIso F).symm
  right := μIso F X A.inverse ≪≫ F.mapIso A.right ≪≫ (εIso F).symm

/-- An actual order-two isomorphism is preserved by strong monoidal
functors, with the actual tensor and unit comparisons displayed. -/
def mapSquare (he : X ⊗ X ≅ 𝟙_ C) : F.obj X ⊗ F.obj X ≅ 𝟙_ D :=
  μIso F X X ≪≫ F.mapIso he ≪≫ (εIso F).symm

end Paper18.Category.TensorInverse

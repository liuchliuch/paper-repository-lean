import Paper18.Category.ModuleFunctorSemisimpleBimodules

/-! # Reflecting an actual separability section from the monoidal opposite -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
universe v u
namespace Paper18.Category.CentralFunctorAdjointSeparable
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A : C} [MonObj A]

/-- Reversing tensor order interchanges the two genuine module-linearity
equations and leaves the actual splitting equation unchanged. -/
def separableOfMop (S : SeparableAlgebra (mop A)) : SeparableAlgebra A where
  section_ := S.section_.unmop
  section_mul := by
    exact congrArg Quiver.Hom.unmop S.section_mul
  left_linear := by
    exact congrArg Quiver.Hom.unmop S.right_linear
  right_linear := by
    exact congrArg Quiver.Hom.unmop S.left_linear

end Paper18.Category.CentralFunctorAdjointSeparable

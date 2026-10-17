import Mathlib.Data.Complex.Basic
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.Opposite

/-! # Complex linearity on the actual opposite category -/
noncomputable section
open CategoryTheory Opposite
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]

/-- Transport complex scalar multiplication through `unop` on actual Hom
spaces. Composition remains bilinear after reversing its order. -/
instance oppositeComplexLinear : Linear ℂ Cᵒᵖ where
  homModule _X _Y :=
    { smul := fun r f => (r • f.unop).op
      one_smul f := Quiver.Hom.unop_inj (one_smul ℂ f.unop)
      mul_smul r s f := Quiver.Hom.unop_inj (mul_smul r s f.unop)
      smul_add r f g := Quiver.Hom.unop_inj (smul_add r f.unop g.unop)
      smul_zero r := Quiver.Hom.unop_inj (smul_zero r)
      add_smul r s f := Quiver.Hom.unop_inj (add_smul r s f.unop)
      zero_smul f := Quiver.Hom.unop_inj (zero_smul ℂ f.unop) }
  smul_comp _ _ _ _ _ _ := Quiver.Hom.unop_inj (Linear.comp_smul _ _ _ _ _ _)
  comp_smul _ _ _ _ _ _ := Quiver.Hom.unop_inj (Linear.smul_comp _ _ _ _ _ _)

@[simp]
lemma complex_op_smul {X Y : C} (r : ℂ) (f : X ⟶ Y) : (r • f).op = r • f.op := rfl

@[simp]
lemma complex_unop_smul {X Y : Cᵒᵖ} (r : ℂ) (f : X ⟶ Y) : (r • f).unop = r • f.unop := rfl

end Paper18.Category

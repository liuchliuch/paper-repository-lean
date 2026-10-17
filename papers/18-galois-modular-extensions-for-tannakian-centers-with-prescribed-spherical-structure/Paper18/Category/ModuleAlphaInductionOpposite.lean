import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Data.Complex.Basic

/-! # The actual linear structures on the monoidal opposite

The monoidal opposite changes tensor order and retains genuine morphisms,
so the additive and scalar operations transport through actual unmopping.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
universe v u
namespace Paper18.Category.ModuleAlphaInduction
variable {D : Type u} [Category.{v} D]

def mopHomEquiv (X Y : Dᴹᵒᵖ) : (X ⟶ Y) ≃ (X.unmop ⟶ Y.unmop) where
  toFun := Quiver.Hom.unmop
  invFun := Quiver.Hom.mop
  left_inv _ := rfl
  right_inv _ := rfl

instance mopHomAddCommGroup [Preadditive D] (X Y : Dᴹᵒᵖ) : AddCommGroup (X ⟶ Y) :=
  (mopHomEquiv X Y).addCommGroup

instance mopPreadditive [Preadditive D] : Preadditive Dᴹᵒᵖ where
  homGroup X Y := inferInstance
  add_comp X Y Z f g h := by
    apply Quiver.Hom.unmop_inj
    change (f.unmop + g.unmop) ≫ h.unmop = f.unmop ≫ h.unmop + g.unmop ≫ h.unmop
    rw [Preadditive.add_comp]
  comp_add X Y Z f g h := by
    apply Quiver.Hom.unmop_inj
    change f.unmop ≫ (g.unmop + h.unmop) = f.unmop ≫ g.unmop + f.unmop ≫ h.unmop
    rw [Preadditive.comp_add]

instance mopHomModule [Preadditive D] [Linear ℂ D] (X Y : Dᴹᵒᵖ) : Module ℂ (X ⟶ Y) :=
  Equiv.module ℂ (mopHomEquiv X Y)

instance mopLinear [Preadditive D] [Linear ℂ D] : Linear ℂ Dᴹᵒᵖ where
  homModule X Y := inferInstance
  smul_comp X Y Z r f g := by
    apply Quiver.Hom.unmop_inj
    change (r • f.unmop) ≫ g.unmop = r • (f.unmop ≫ g.unmop)
    rw [Linear.smul_comp]
  comp_smul X Y Z f r g := by
    apply Quiver.Hom.unmop_inj
    change f.unmop ≫ (r • g.unmop) = r • (f.unmop ≫ g.unmop)
    rw [Linear.comp_smul]

instance mopFunctor_additive [Preadditive D] : (mopFunctor D).Additive where
  map_add := by intros; rfl
instance mopFunctor_linear [Preadditive D] [Linear ℂ D] : (mopFunctor D).Linear ℂ where
  map_smul _ _ := rfl

instance unmopFunctor_additive [Preadditive D] : (unmopFunctor D).Additive where
  map_add := by intros; rfl
instance unmopFunctor_linear [Preadditive D] [Linear ℂ D] : (unmopFunctor D).Linear ℂ where
  map_smul _ _ := rfl

variable [MonoidalCategory D] [Preadditive D] [MonoidalPreadditive D]
instance mopMonoidalPreadditive : MonoidalPreadditive Dᴹᵒᵖ where
  whiskerLeft_zero := by
    intros; apply Quiver.Hom.unmop_inj
    exact MonoidalPreadditive.zero_whiskerRight
  zero_whiskerRight := by
    intros; apply Quiver.Hom.unmop_inj
    exact MonoidalPreadditive.whiskerLeft_zero
  whiskerLeft_add := by
    intros; apply Quiver.Hom.unmop_inj
    exact MonoidalPreadditive.add_whiskerRight _ _
  add_whiskerRight := by
    intros; apply Quiver.Hom.unmop_inj
    exact MonoidalPreadditive.whiskerLeft_add _ _

instance mopMonoidalLinear [Linear ℂ D] [MonoidalLinear ℂ D] : MonoidalLinear ℂ Dᴹᵒᵖ where
  whiskerLeft_smul := by
    intros; apply Quiver.Hom.unmop_inj
    exact MonoidalLinear.smul_whiskerRight _ _ _
  smul_whiskerRight := by
    intros; apply Quiver.Hom.unmop_inj
    exact MonoidalLinear.whiskerLeft_smul _ _ _

end Paper18.Category.ModuleAlphaInduction

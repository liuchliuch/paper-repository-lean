import Paper18.Category.DrinfeldCoendModulesForward

/-! # The actual fully faithful center-to-coend-module functor -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- The actual center-to-module functor, with exactly the same underlying
objects and morphisms in the ambient category. -/
def toModules : Center D ⥤ Mod_ D (algebra S) where
  obj := toModulesObj S
  map f := Mod_.Hom.mk' f.f (action_naturality S f)
  map_id Z := by apply Mod_.hom_ext; rfl
  map_comp f g := by apply Mod_.hom_ext; rfl

@[simp] lemma toModules_obj_X (Z : Center D) : ((toModules S).obj Z).X = Z.1 := rfl
@[simp] lemma toModules_map_hom {Z W : Center D} (f : Z ⟶ W) :
    ((toModules S).map f).hom = f.f := rfl

instance toModules_faithful : (toModules S).Faithful where
  map_injective := by
    intro Z W f g h
    have he := congrArg Mod_.Hom.hom h
    exact Center.Hom.ext he

instance toModules_full : (toModules S).Full where
  map_surjective := by
    intro Z W f
    have hf : action S Z ≫ f.hom = algebra S ◁ f.hom ≫ action S W :=
      f.isMod_Hom.smul_hom
    let g : Z ⟶ W := ⟨f.hom, (action_comm_iff S f.hom).mp hf⟩
    exact ⟨g, by apply Mod_.hom_ext; rfl⟩

instance toModules_additive : (toModules S).Additive where
  map_add := by intros; apply Mod_.hom_ext; rfl

instance toModules_linear : (toModules S).Linear ℂ where
  map_smul := by intro Z W r f; apply Mod_.hom_ext; rfl

end Paper18.Category.DrinfeldCoendModules

import Paper18.Category.BalancedModuleCategoryExtension
import Paper18.Category.BimoduleRelativeTensorSplitBarBasic
import Paper18.Category.RelativeTensorAdjunction

/-! # Actual split presentations of the right input module -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u vE uE
namespace Paper18.Category.BalancedModuleCategory
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  {B : D} [MonObj B]

abbrev rightResolution (N : RightModules B) : RightModules B := InternalModule.free (mop B) N.X

def rightProjection (N : RightModules B) : rightResolution N ⟶ N := InternalModule.actionHom N

def rightTop (N : RightModules B) : rightResolution (rightResolution N) ⟶ rightResolution N :=
  rightProjection (rightResolution N)

def rightBottom (N : RightModules B) : rightResolution (rightResolution N) ⟶ rightResolution N :=
  InternalModule.freeMap (rightProjection N).hom

def rightSection (SB : SeparableAlgebra B) (N : RightModules B) : N ⟶ rightResolution N :=
  (leftFreeRetract (ModuleFunctor.separableMop SB) N).i

def rightSplitCoequalizer (SB : SeparableAlgebra B) (N : RightModules B) :
    IsSplitCoequalizer (rightTop N) (rightBottom N) (rightProjection N) := by
  have h := BimoduleRelativeTensor.SplitBar.ofCounitSection
    (RelativeTensor.freeForgetAdjunction (A := mop B)) N (rightSection SB N)
    (by simpa only [RelativeTensor.freeForgetAdjunction_counit] using
      (leftFreeRetract (ModuleFunctor.separableMop SB) N).retract)
  simpa only [RelativeTensor.freeForgetAdjunction_counit] using h

omit [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] in
lemma rightTop_formula (N : RightModules B) :
    rightTop N = (rightAmbientAssoc (Mod_.regular (mop B)) (rightUnderlying N) B).inv ≫
      ambientLeftFunctor.map (CategoryTheory.Prod.mkHom (𝟙 (rightUnderlying N))
        (rightRegularMultiply (B := B))) := by
  apply Mod_.Hom.ext
  apply Quiver.Hom.unmop_inj
  simp only [Mod_.comp_hom', unmop_comp, ambientLeftFunctor_map_hom]
  change (α_ (rightUnderlying N) B B).hom ≫ rightUnderlying N ◁ μ[B] =
    (α_ (rightUnderlying N) B B).hom ≫ (𝟙 (rightUnderlying N) ⊗ₘ μ[B])
  rw [id_tensorHom]

omit [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] in
lemma rightBottom_formula (N : RightModules B) :
    rightBottom N = ambientLeftFunctor.map (CategoryTheory.Prod.mkHom
      (rightAction N) (𝟙 (Mod_.regular (mop B)))) := by
  apply Mod_.Hom.ext
  apply Quiver.Hom.unmop_inj
  rw [ambientLeftFunctor_map_hom]
  change rightAction N ▷ B = rightAction N ⊗ₘ 𝟙 B
  rw [tensorHom_id]

end Paper18.Category.BalancedModuleCategory

import Paper18.Category.RelativeTensorMonoidal
import Paper18.Category.RelativeTensorBasic

/-! # Linearity of actual relative tensor products -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u
namespace Paper18.Category.RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C] {A : C} [MonObj A] [IsCommMonObj A]

/-- Left whiskering on the actual relative tensor is induced by ordinary
left whiskering before the balancing quotient. -/
@[reassoc (attr := simp)]
theorem π_whiskerLeft (M : Mod_ C A) {N P : Mod_ C A} (f : N ⟶ P) :
    π M N ≫ (M ◁ f).hom = (M.X ◁ f.hom) ≫ π M P := by
  change coequalizer.π _ _ ≫ (Bimod.whiskerLeft (toBimodObj M) (toBimod.map f)).hom = _
  dsimp only [Bimod.whiskerLeft_hom]
  erw [ι_colimMap, parallelPairHom_app_one]
  rfl

/-- Right whiskering is induced by the actual underlying right whiskering. -/
@[reassoc (attr := simp)]
theorem π_whiskerRight {M N : Mod_ C A} (f : M ⟶ N) (P : Mod_ C A) :
    π M P ≫ (f ▷ P).hom = (f.hom ▷ P.X) ≫ π N P := by
  change coequalizer.π _ _ ≫ (Bimod.whiskerRight (toBimod.map f) (toBimodObj P)).hom = _
  dsimp only [Bimod.whiskerRight_hom]
  erw [ι_colimMap, parallelPairHom_app_one]
  rfl

/-- Actual module maps out of the relative tensor are determined by their
underlying balanced composites. -/
theorem module_hom_ext {M N P : Mod_ C A} {f g : M ⊗ N ⟶ P}
    (h : π M N ≫ f.hom = π M N ≫ g.hom) : f = g := by
  apply Mod_.Hom.ext
  exact hom_ext M N h

section Linear
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

instance moduleMonoidalPreadditive : MonoidalPreadditive (Mod_ C A) where
  whiskerLeft_zero := by
    intro M N P
    apply module_hom_ext
    simp only [π_whiskerLeft, InternalModule.zero_hom,
      MonoidalPreadditive.whiskerLeft_zero, zero_comp, comp_zero]
  zero_whiskerRight := by
    intro M N P
    apply module_hom_ext
    simp only [π_whiskerRight, InternalModule.zero_hom,
      MonoidalPreadditive.zero_whiskerRight, zero_comp, comp_zero]
  whiskerLeft_add := by
    intro M N P f g
    apply module_hom_ext
    simp only [π_whiskerLeft, InternalModule.add_hom,
      MonoidalPreadditive.whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add]
  add_whiskerRight := by
    intro M N P f g
    apply module_hom_ext
    simp only [π_whiskerRight, InternalModule.add_hom,
      MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp, Preadditive.comp_add]

instance moduleMonoidalLinear : MonoidalLinear ℂ (Mod_ C A) where
  whiskerLeft_smul := by
    intro M N P c f
    apply module_hom_ext
    simp only [π_whiskerLeft, InternalModule.smul_hom,
      MonoidalLinear.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul]
  smul_whiskerRight := by
    intro c N P f M
    apply module_hom_ext
    simp only [π_whiskerRight, InternalModule.smul_hom,
      MonoidalLinear.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul]

end Linear
end Paper18.Category.RelativeTensor

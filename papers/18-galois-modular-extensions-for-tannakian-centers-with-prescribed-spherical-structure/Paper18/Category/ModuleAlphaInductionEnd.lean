import Paper18.Category.ModuleAlphaInductionComposition
import Paper18.Category.ModuleFunctorFiniteBasic
import Mathlib.CategoryTheory.Monoidal.Transport

/-! # The actual monoidal category of strong module endofunctors -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalLeftAction
universe v u vM uM
namespace Paper18.Category.ModuleAlphaInduction
variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  (M : Type uM) [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ]

/-- Actual additive complex-linear strong module endofunctors. -/
abbrev End := ModuleFunctor.Bundled C M M

/-- The actual tensor product is composition, in mathlib's endofunctor convention. -/
def endTensor (F G : End C M) : End C M where
  toFunctor := F.toFunctor ⋙ G.toFunctor
  leftLinear := inferInstance
  additive := inferInstance
  linear := inferInstance

/-- The actual identity strong module endofunctor. -/
def endUnit : End C M where
  toFunctor := 𝟭 M
  leftLinear := ModuleFunctor.identityActionLeftLinear C M
  additive := inferInstance
  linear := inferInstance

/-- The actual underlying module-functor associator. -/
instance endAssociator_moduleNatural (F G H : End C M) :
    ModuleFunctor.IsModuleNatural C
      (Functor.associator F.toFunctor G.toFunctor H.toFunctor).hom where
  lineator X m := by
    change Functor.LaxLeftLinear.μₗ ((F.toFunctor ⋙ G.toFunctor) ⋙ H.toFunctor) X m ≫ 𝟙 _ =
      X ⊴ₗ 𝟙 _ ≫ Functor.LaxLeftLinear.μₗ (F.toFunctor ⋙ (G.toFunctor ⋙ H.toFunctor)) X m
    simp only [comp_μ, Functor.comp_obj, Functor.comp_map, Functor.map_comp,
      actionHomRight_id, Category.id_comp, Category.comp_id, Category.assoc]

instance endLeftUnitor_moduleNatural (F : End C M) :
    ModuleFunctor.IsModuleNatural C (Functor.leftUnitor F.toFunctor).hom where
  lineator X m := by
    change Functor.LaxLeftLinear.μₗ ((endUnit C M).toFunctor ⋙ F.toFunctor) X m ≫ 𝟙 _ =
      X ⊴ₗ 𝟙 _ ≫ Functor.LaxLeftLinear.μₗ F.toFunctor X m
    simp only [comp_μ, endUnit, ModuleFunctor.identityActionLeftLinear,
      Functor.id_obj, actionHomRight_id, Category.comp_id, Category.id_comp]
    simp

instance endRightUnitor_moduleNatural (F : End C M) :
    ModuleFunctor.IsModuleNatural C (Functor.rightUnitor F.toFunctor).hom where
  lineator X m := by
    change Functor.LaxLeftLinear.μₗ (F.toFunctor ⋙ (endUnit C M).toFunctor) X m ≫ 𝟙 _ =
      X ⊴ₗ 𝟙 _ ≫ Functor.LaxLeftLinear.μₗ F.toFunctor X m
    simp only [comp_μ, endUnit, ModuleFunctor.identityActionLeftLinear,
      Functor.id_obj, Functor.id_map, actionHomRight_id, Category.comp_id, Category.id_comp]

/-- The actual composition tensor structure, with actual module-natural
unitors and associators. -/
instance endMonoidalStruct : MonoidalCategoryStruct (End C M) where
  tensorObj := endTensor C M
  tensorUnit := endUnit C M
  whiskerLeft F {_ _} τ :=
    ⟨Functor.whiskerLeft F.toFunctor τ.val,
      show ModuleFunctor.IsModuleNatural C (Functor.whiskerLeft F.toFunctor τ.val) from inferInstance⟩
  whiskerRight τ F :=
    ⟨Functor.whiskerRight τ.val F.toFunctor,
      show ModuleFunctor.IsModuleNatural C (Functor.whiskerRight τ.val F.toFunctor) from inferInstance⟩
  tensorHom {F G H K} τ σ :=
    ⟨τ.val ◫ σ.val, by
      change ModuleFunctor.IsModuleNatural C
        (Functor.whiskerLeft F.toFunctor σ.val ≫ Functor.whiskerRight τ.val K.toFunctor)
      infer_instance⟩
  associator F G H := ModuleFunctor.isoMk (Functor.associator F.toFunctor G.toFunctor H.toFunctor)
  leftUnitor F := ModuleFunctor.isoMk (Functor.leftUnitor F.toFunctor)
  rightUnitor F := ModuleFunctor.isoMk (Functor.rightUnitor F.toFunctor)

attribute [local instance] CategoryTheory.endofunctorMonoidalCategory

/-- Forgetting the genuine lineator strictly preserves the actual tensor data. -/
def endInducingData : Monoidal.InducingFunctorData
    (ModuleFunctor.forget (C := C) (M := M) (N := M)) where
  μIso _ _ := Iso.refl _
  εIso := Iso.refl _
  whiskerLeft_eq F {G H} τ := by
    change Functor.whiskerLeft F.toFunctor τ.val =
      𝟙 _ ≫ Functor.whiskerLeft F.toFunctor τ.val ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  whiskerRight_eq {F G} τ H := by
    change Functor.whiskerRight τ.val H.toFunctor =
      𝟙 _ ≫ Functor.whiskerRight τ.val H.toFunctor ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  tensorHom_eq {F G H K} τ σ := by
    change (τ.val ◫ σ.val) = 𝟙 _ ≫ (τ.val ◫ σ.val) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  associator_eq F G H := by
    ext m
    dsimp [ModuleFunctor.forget, endMonoidalStruct, ModuleFunctor.isoMk, endTensor, endUnit]
    simp only [Category.id_comp, Category.comp_id]
    rw [H.toFunctor.map_id (G.toFunctor.obj (F.toFunctor.obj m)),
      G.toFunctor.map_id (F.toFunctor.obj m), H.toFunctor.map_id]
    simp
  leftUnitor_eq F := by
    ext m
    dsimp [ModuleFunctor.forget, endMonoidalStruct, ModuleFunctor.isoMk, endTensor, endUnit]
    simp only [Category.id_comp, Category.comp_id]
    exact (F.toFunctor.map_id m).symm
  rightUnitor_eq F := by
    ext m
    dsimp [ModuleFunctor.forget, endMonoidalStruct, ModuleFunctor.isoMk, endTensor, endUnit]
    simp only [Functor.map_id, Category.id_comp, Category.comp_id]

/-- Actual associativity and unit coherence descend through faithful
forgetting to the genuine monoidal category of endofunctors. -/
instance endMonoidal : MonoidalCategory (End C M) :=
  Monoidal.induced (ModuleFunctor.forget (C := C) (M := M) (N := M)) (endInducingData C M)

/-- The actual forgetful functor is strong monoidal. -/
instance endForgetMonoidal :
    (ModuleFunctor.forget (C := C) (M := M) (N := M)).Monoidal :=
  Monoidal.fromInducedMonoidal (ModuleFunctor.forget (C := C) (M := M) (N := M)) (endInducingData C M)

instance endMonoidalPreadditive : MonoidalPreadditive (End C M) where
  whiskerLeft_zero := by intros; apply Subtype.ext; ext m; rfl
  zero_whiskerRight := by
    intro F G H; apply Subtype.ext; ext m
    exact F.toFunctor.map_zero _ _
  whiskerLeft_add := by intros; apply Subtype.ext; ext m; rfl
  add_whiskerRight := by
    intro F G H τ σ; apply Subtype.ext; ext m
    exact F.toFunctor.map_add

instance endMonoidalLinear : MonoidalLinear ℂ (End C M) where
  whiskerLeft_smul := by intros; apply Subtype.ext; ext m; rfl
  smul_whiskerRight := by
    intro r F G τ H; apply Subtype.ext; ext m
    exact H.toFunctor.map_smul _ _

end Paper18.Category.ModuleAlphaInduction

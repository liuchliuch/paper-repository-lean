import Paper18.Category.ModuleFunctorSemisimpleModuleMap
import Paper18.Category.ModuleAlphaInductionMonoidal
import Paper18.Category.ModuleFunctorSemisimpleSeparableLinear

/-! # Actual module endofunctors act on actual algebra modules

Transport of action modules is functorial in genuine strong module
functors. The identity and composition comparisons below have actual
identity underlying maps, and their module equations follow from the
actual composite lineator. Their coherence gives a strong monoidal
functor to the actual endofunctor category.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalLeftAction MonoidalOpposite
open scoped MonObj
universe v u vM uM
namespace Paper18.Category.GraphPicard.MoritaProduct
attribute [local instance] CategoryTheory.endofunctorMonoidalCategory
variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  (M : Type uM) [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ]
  (A : C) [MonObj A]

/-- Actual module transformations act on actual algebra-module objects. -/
def moduleLift : ModuleAlphaInduction.End C M ⥤ (Mod_ M A ⥤ Mod_ M A) where
  obj F := ModuleFunctor.mapActionModules F.toFunctor
  map f := by
    letI := f.property
    exact ModuleFunctor.mapActionModulesTransformation f.val
  map_id F := by
    apply NatTrans.ext
    funext X
    apply Mod_.Hom.ext
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext X
    apply Mod_.Hom.ext
    rfl

@[simp] theorem moduleLift_obj_X (F : ModuleAlphaInduction.End C M) (X : Mod_ M A) :
    (((moduleLift C M A).obj F).obj X).X = F.toFunctor.obj X.X := rfl

@[simp] theorem moduleLift_map_app_hom {F G : ModuleAlphaInduction.End C M}
    (f : F ⟶ G) (X : Mod_ M A) :
    (((moduleLift C M A).map f).app X).hom = f.val.app X.X := rfl

/-- The actual composition lineator gives an actual module isomorphism
on each algebra-module object. -/
def moduleLiftCompComponent (F G : ModuleAlphaInduction.End C M) (X : Mod_ M A) :
    ((moduleLift C M A).obj F ⋙ (moduleLift C M A).obj G).obj X ≅
      ((moduleLift C M A).obj (F ⊗ G)).obj X where
  hom := Mod_.Hom.mk' (𝟙 _) (by
    change (Functor.LaxLeftLinear.μₗ G.toFunctor A (F.toFunctor.obj X.X) ≫
      G.toFunctor.map (Functor.LaxLeftLinear.μₗ F.toFunctor A X.X ≫
        F.toFunctor.map γ[A,X.X])) ≫ 𝟙 _ =
      (A ⊴ₗ 𝟙 _) ≫
        ((Functor.LaxLeftLinear.μₗ G.toFunctor A (F.toFunctor.obj X.X) ≫
          G.toFunctor.map (Functor.LaxLeftLinear.μₗ F.toFunctor A X.X)) ≫
            G.toFunctor.map (F.toFunctor.map γ[A,X.X]))
    simp only [Category.comp_id, actionHomRight_id, Category.id_comp,
      G.toFunctor.map_comp, Category.assoc])
  inv := Mod_.Hom.mk' (𝟙 _) (by
    change ((Functor.LaxLeftLinear.μₗ G.toFunctor A (F.toFunctor.obj X.X) ≫
      G.toFunctor.map (Functor.LaxLeftLinear.μₗ F.toFunctor A X.X)) ≫
        G.toFunctor.map (F.toFunctor.map γ[A,X.X])) ≫ 𝟙 _ =
      (A ⊴ₗ 𝟙 _) ≫
        (Functor.LaxLeftLinear.μₗ G.toFunctor A (F.toFunctor.obj X.X) ≫
          G.toFunctor.map (Functor.LaxLeftLinear.μₗ F.toFunctor A X.X ≫
            F.toFunctor.map γ[A,X.X]))
    simp only [Category.comp_id, actionHomRight_id, Category.id_comp,
      G.toFunctor.map_comp, Category.assoc])
  hom_inv_id := by apply Mod_.Hom.ext; exact Category.id_comp _
  inv_hom_id := by apply Mod_.Hom.ext; exact Category.id_comp _

/-- The actual lift preserves composition through the actual component
isomorphisms, with no comparison-isomorphism premise. -/
def moduleLiftCompIso (F G : ModuleAlphaInduction.End C M) :
    (moduleLift C M A).obj F ⋙ (moduleLift C M A).obj G ≅
      (moduleLift C M A).obj (F ⊗ G) :=
  NatIso.ofComponents (moduleLiftCompComponent C M A F G) (by
    intro X Y f
    apply Mod_.Hom.ext
    change G.toFunctor.map (F.toFunctor.map f.hom) ≫ 𝟙 _ =
      𝟙 _ ≫ G.toFunctor.map (F.toFunctor.map f.hom)
    simp only [Category.comp_id, Category.id_comp])

/-- The identity strong module functor preserves the actual algebra
action through an actual identity-underlying isomorphism. -/
def moduleLiftUnitComponent (X : Mod_ M A) :
    X ≅ ((moduleLift C M A).obj (𝟙_ (ModuleAlphaInduction.End C M))).obj X where
  hom := Mod_.Hom.mk' (𝟙 _) (by
    change γ[A,X.X] ≫ 𝟙 _ = (A ⊴ₗ 𝟙 X.X) ≫ (𝟙 _ ≫ γ[A,X.X])
    simp only [Category.comp_id, actionHomRight_id, Category.id_comp])
  inv := Mod_.Hom.mk' (𝟙 _) (by
    change (𝟙 _ ≫ γ[A,X.X]) ≫ 𝟙 _ = (A ⊴ₗ 𝟙 X.X) ≫ γ[A,X.X]
    simp only [Category.comp_id, actionHomRight_id, Category.id_comp])
  hom_inv_id := by apply Mod_.Hom.ext; exact Category.id_comp _
  inv_hom_id := by apply Mod_.Hom.ext; exact Category.id_comp _

def moduleLiftUnitIso : 𝟭 (Mod_ M A) ≅
    (moduleLift C M A).obj (𝟙_ (ModuleAlphaInduction.End C M)) :=
  NatIso.ofComponents (moduleLiftUnitComponent C M A) (by
    intro X Y f
    apply Mod_.Hom.ext
    exact (Category.comp_id f.hom).trans (Category.id_comp f.hom).symm)

/-- Actual identity/composition comparisons satisfy all strong monoidal
coherence equations, checked on their actual underlying components. -/
def moduleLiftCoreMonoidal : (moduleLift C M A).CoreMonoidal where
  εIso := moduleLiftUnitIso C M A
  μIso := moduleLiftCompIso C M A
  μIso_hom_natural_left := by
    intro F G f H
    apply NatTrans.ext
    funext X
    apply Mod_.Hom.ext
    change H.toFunctor.map (f.val.app X.X) ≫ 𝟙 _ =
      𝟙 _ ≫ H.toFunctor.map (f.val.app X.X)
    simp only [Category.comp_id, Category.id_comp]
  μIso_hom_natural_right := by
    intro F G H f
    apply NatTrans.ext
    funext X
    apply Mod_.Hom.ext
    change f.val.app (H.toFunctor.obj X.X) ≫ 𝟙 _ =
      𝟙 _ ≫ f.val.app (H.toFunctor.obj X.X)
    simp only [Category.comp_id, Category.id_comp]
  associativity := by
    intro F G H
    apply NatTrans.ext
    funext X
    apply Mod_.Hom.ext
    dsimp [moduleLift, moduleLiftCompIso, moduleLiftCompComponent,
      ModuleFunctor.mapActionModulesTransformation, ModuleFunctor.mapActionModules,
      ModuleFunctor.mapActionModuleHom, ModuleAlphaInduction.endMonoidalStruct,
      ModuleFunctor.isoMk]
    simp only [Mod_.id_hom', Category.id_comp, Category.comp_id]
    rw [H.toFunctor.map_id, Category.id_comp]
    change (Functor.associator F.toFunctor G.toFunctor H.toFunctor).hom.app X.X = 𝟙 _
    rfl
  left_unitality := by
    intro F
    apply NatTrans.ext
    funext X
    apply Mod_.Hom.ext
    change 𝟙 _ = F.toFunctor.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _
    simp only [F.toFunctor.map_id, Category.id_comp]
  right_unitality := by
    intro F
    apply NatTrans.ext
    funext X
    apply Mod_.Hom.ext
    change 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.id_comp]

instance moduleLift_monoidal : (moduleLift C M A).Monoidal :=
  (moduleLiftCoreMonoidal C M A).toMonoidal

instance moduleLift_obj_additive (F : ModuleAlphaInduction.End C M) :
    ((moduleLift C M A).obj F).Additive where
  map_add {X Y} f g := by
    apply Mod_.Hom.ext
    exact F.toFunctor.map_add

instance moduleLift_obj_linear (F : ModuleAlphaInduction.End C M) :
    ((moduleLift C M A).obj F).Linear ℂ where
  map_smul f z := by
    apply Mod_.Hom.ext
    exact F.toFunctor.map_smul z f.hom

instance moduleLift_additive : (moduleLift C M A).Additive where
  map_add := by
    intro F G f g
    apply NatTrans.ext
    funext X
    apply Mod_.Hom.ext
    rfl

instance moduleLift_linear : (moduleLift C M A).Linear ℂ where
  map_smul f z := by
    apply NatTrans.ext
    funext X
    apply Mod_.Hom.ext
    rfl

end Paper18.Category.GraphPicard.MoritaProduct

import Paper18.Category.FixedBoundaryModuleWatts
import Mathlib.CategoryTheory.Linear.FunctorCategory

/-! # Actual complex-linear strong module functors and their morphisms

Objects carry mathlib's actual strong left lineator. Morphisms are actual
natural transformations satisfying the lineator equation. Their vector
space structure is inherited from the genuine natural-transformation space.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u v' u' v'' u''
namespace Paper18.Category.ModuleFunctor
variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  (M : Type u') [Category.{v'} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  (N : Type u'') [Category.{v''} N] [Preadditive N] [Linear ℂ N]
  [MonoidalLeftAction C N]

/-- An actual additive complex-linear strong module functor. -/
structure Bundled where
  toFunctor : M ⥤ N
  leftLinear : toFunctor.LeftLinear C
  additive : toFunctor.Additive
  linear : toFunctor.Linear ℂ

attribute [instance] Bundled.leftLinear Bundled.additive Bundled.linear

variable {C M N}
  [∀ X : C, (MonoidalLeftAction.actionLeft N X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft N X).Linear ℂ]

section ModuleNaturalLinear
variable
  {F G : M ⥤ N} [F.LeftLinear C] [G.LeftLinear C]

instance moduleNatural_zero : IsModuleNatural C (0 : F ⟶ G) where
  lineator X Y := by
    change Functor.LaxLeftLinear.μₗ F X Y ≫ 0 =
      (X ⊴ₗ (0 : F.obj Y ⟶ G.obj Y)) ≫ Functor.LaxLeftLinear.μₗ G X Y
    have hz : X ⊴ₗ (0 : F.obj Y ⟶ G.obj Y) = 0 :=
      (MonoidalLeftAction.actionLeft N X).map_zero (F.obj Y) (G.obj Y)
    rw [hz]
    simp

instance moduleNatural_add (τ σ : F ⟶ G)
    [IsModuleNatural C τ] [IsModuleNatural C σ] : IsModuleNatural C (τ + σ) where
  lineator X Y := by
    change Functor.LaxLeftLinear.μₗ F X Y ≫ (τ.app (X ⊙ₗ Y) + σ.app (X ⊙ₗ Y)) =
      (X ⊴ₗ (τ.app Y + σ.app Y)) ≫ Functor.LaxLeftLinear.μₗ G X Y
    have ha : X ⊴ₗ (τ.app Y + σ.app Y) = X ⊴ₗ τ.app Y + X ⊴ₗ σ.app Y :=
      (MonoidalLeftAction.actionLeft N X).map_add
    rw [ha, Preadditive.comp_add, Preadditive.add_comp,
      IsModuleNatural.lineator, IsModuleNatural.lineator]

instance moduleNatural_smul (r : ℂ) (τ : F ⟶ G)
    [IsModuleNatural C τ] : IsModuleNatural C (r • τ) where
  lineator X Y := by
    change Functor.LaxLeftLinear.μₗ F X Y ≫ (r • τ.app (X ⊙ₗ Y)) =
      (X ⊴ₗ (r • τ.app Y)) ≫ Functor.LaxLeftLinear.μₗ G X Y
    have hs : X ⊴ₗ (r • τ.app Y) = r • (X ⊴ₗ τ.app Y) :=
      (MonoidalLeftAction.actionLeft N X).map_smul r _
    rw [hs, Linear.comp_smul, Linear.smul_comp, IsModuleNatural.lineator]

end ModuleNaturalLinear

/-- The actual module natural transformations form a genuine submodule. -/
def homSubmodule (F G : Bundled C M N) : Submodule ℂ (F.toFunctor ⟶ G.toFunctor) where
  carrier := {τ | IsModuleNatural C τ}
  zero_mem' := show IsModuleNatural C (0 : F.toFunctor ⟶ G.toFunctor) from inferInstance
  add_mem' {τ σ} hτ hσ := by
    letI : IsModuleNatural C τ := hτ
    letI : IsModuleNatural C σ := hσ
    exact (inferInstance : IsModuleNatural C (τ + σ))
  smul_mem' r τ hτ := by
    letI : IsModuleNatural C τ := hτ
    exact (inferInstance : IsModuleNatural C (r • τ))

instance bundledCategory : Category (Bundled C M N) where
  Hom F G := homSubmodule F G
  id F := ⟨𝟙 F.toFunctor, show IsModuleNatural C (𝟙 F.toFunctor) from inferInstance⟩
  comp τ σ := ⟨τ.val ≫ σ.val, by
    letI : IsModuleNatural C τ.val := τ.property
    letI : IsModuleNatural C σ.val := σ.property
    exact (inferInstance : IsModuleNatural C (τ.val ≫ σ.val))⟩
  id_comp τ := Subtype.ext (Category.id_comp τ.val)
  comp_id τ := Subtype.ext (Category.comp_id τ.val)
  assoc τ σ υ := Subtype.ext (Category.assoc τ.val σ.val υ.val)

instance hom_moduleNatural {F G : Bundled C M N} (τ : F ⟶ G) :
    IsModuleNatural C τ.val := τ.property

@[ext] lemma bundled_hom_ext {F G : Bundled C M N} (τ σ : F ⟶ G)
    (h : τ.val = σ.val) : τ = σ := Subtype.ext h

instance bundledPreadditive : Preadditive (Bundled C M N) where
  homGroup F G := inferInstanceAs (AddCommGroup (homSubmodule F G))
  add_comp F G H τ σ υ := Subtype.ext (by
    change (τ.val + σ.val) ≫ υ.val = τ.val ≫ υ.val + σ.val ≫ υ.val
    simp)
  comp_add F G H τ σ υ := Subtype.ext (by
    change τ.val ≫ (σ.val + υ.val) = τ.val ≫ σ.val + τ.val ≫ υ.val
    simp)

instance bundledLinear : Linear ℂ (Bundled C M N) where
  homModule F G := inferInstanceAs (Module ℂ (homSubmodule F G))
  smul_comp F G H r τ σ := Subtype.ext (by
    change (r • τ.val) ≫ σ.val = r • (τ.val ≫ σ.val)
    simp)
  comp_smul F G H τ r σ := Subtype.ext (by
    change τ.val ≫ (r • σ.val) = r • (τ.val ≫ σ.val)
    simp)

/-- Forget the actual lineator and retain the genuine underlying functor. -/
def forget : Bundled C M N ⥤ (M ⥤ N) where
  obj F := F.toFunctor
  map τ := τ.val

instance forget_faithful : (forget (C := C) (M := M) (N := N)).Faithful where
  map_injective {_F _G} _τ _σ h := Subtype.ext h

instance forget_additive : (forget (C := C) (M := M) (N := N)).Additive where
  map_add := by intros; rfl

instance forget_linear : (forget (C := C) (M := M) (N := N)).Linear ℂ where
  map_smul _ _ := rfl

/-- An actual module natural isomorphism is an isomorphism in the actual
bundled module-functor category, including the proved inverse lineator law. -/
def isoMk {F G : Bundled C M N} (e : F.toFunctor ≅ G.toFunctor)
    [IsModuleNatural C e.hom] : F ≅ G where
  hom := ⟨e.hom, show IsModuleNatural C e.hom from inferInstance⟩
  inv := ⟨e.inv, show IsModuleNatural C e.inv from inferInstance⟩
  hom_inv_id := Subtype.ext e.hom_inv_id
  inv_hom_id := Subtype.ext e.inv_hom_id

end Paper18.Category.ModuleFunctor

import Mathlib.CategoryTheory.Monoidal.Action.LinearFunctor
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
import Paper18.Category.Multiplicity

/-!
# Actual regular-module functors are represented by their unit values

This uses mathlib's actual strong module-functor structure `LeftLinear`.
The natural identification with right tensoring is constructed from the
lineator and the right unitor. No Morita classification is assumed.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u v' u' v'' u''
namespace Paper18.Category.ModuleFunctor

section ModuleNatural
variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  {M : Type u'} [Category.{v'} M] [MonoidalLeftAction C M]
  {N : Type u''} [Category.{v''} N] [MonoidalLeftAction C N]
  {F H : M ⥤ N} [F.LeftLinear C] [H.LeftLinear C]

/-- Compatibility of an actual natural transformation with the actual
module lineators. -/
class IsModuleNatural (τ : F ⟶ H) : Prop where
  lineator : ∀ (X : C) (Y : M),
    Functor.LaxLeftLinear.μₗ F X Y ≫ τ.app (X ⊙ₗ Y) =
      X ⊴ₗ τ.app Y ≫ Functor.LaxLeftLinear.μₗ H X Y

attribute [reassoc] IsModuleNatural.lineator

instance moduleNatural_id : IsModuleNatural C (𝟙 F) where
  lineator X Y := by simp

instance moduleNatural_comp {K : M ⥤ N} [K.LeftLinear C]
    (τ : F ⟶ H) (σ : H ⟶ K) [IsModuleNatural C τ] [IsModuleNatural C σ] :
    IsModuleNatural C (τ ≫ σ) where
  lineator X Y := by
    simp only [NatTrans.comp_app, ← Category.assoc]
    rw [IsModuleNatural.lineator]
    simp only [Category.assoc]
    rw [IsModuleNatural.lineator]
    rw [← MonoidalLeftAction.actionHomRight_comp_assoc]

/-- A module natural transformation also commutes with the inverse
lineators of the actual strong module functors. -/
@[reassoc] theorem IsModuleNatural.inverse_lineator (τ : F ⟶ H)
    [IsModuleNatural C τ] (X : C) (Y : M) :
    τ.app (X ⊙ₗ Y) ≫ Functor.OplaxLeftLinear.δₗ H X Y =
      Functor.OplaxLeftLinear.δₗ F X Y ≫ X ⊴ₗ τ.app Y := by
  apply (cancel_epi (Functor.LaxLeftLinear.μₗ F X Y)).mp
  rw [← Category.assoc, IsModuleNatural.lineator]
  simp only [Category.assoc, Functor.LeftLinear.μₗ_comp_δₗ, Category.comp_id]
  simp only [← Category.assoc, Functor.LeftLinear.μₗ_comp_δₗ, Category.id_comp]

end ModuleNatural

section IdentityAction
variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  (M : Type u') [Category.{v'} M] [MonoidalLeftAction C M]

/-- The actual identity module functor on any native left module category. -/
instance identityActionLeftLinear : (𝟭 M).LeftLinear C where
  μₗ X Y := 𝟙 (X ⊙ₗ Y)
  μₗ_naturality_left := by intros; simp
  μₗ_naturality_right := by intros; simp
  μₗ_associativity := by intros; simp
  μₗ_unitality := by intros; simp
  δₗ X Y := 𝟙 (X ⊙ₗ Y)
  δₗ_naturality_left := by intros; simp
  δₗ_naturality_right := by intros; simp
  δₗ_associativity := by intros; simp
  δₗ_unitality_inv := by intros; simp
  μₗ_comp_δₗ := by intros; simp
  δₗ_comp_μₗ := by intros; simp

end IdentityAction

section Regular
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The identity has its actual identity module lineator. -/
instance regularIdentityLeftLinear : (𝟭 C).LeftLinear C where
  μₗ X Y := 𝟙 (X ⊗ Y)
  μₗ_naturality_left := by intros; simp
  μₗ_naturality_right := by intros; simp
  μₗ_associativity := by intros; simp
  μₗ_unitality := by intros; simp
  δₗ X Y := 𝟙 (X ⊗ Y)
  δₗ_naturality_left := by intros; simp
  δₗ_naturality_right := by intros; simp
  δₗ_associativity := by intros; simp
  δₗ_unitality_inv := by intros; simp
  μₗ_comp_δₗ := by intros; simp
  δₗ_comp_μₗ := by intros; simp

/-- Right tensoring is an actual strong functor for the regular left
module action. All lineator coherences are ambient associator coherences. -/
instance tensorRightLeftLinear (U : C) : (tensorRight U).LeftLinear C where
  μₗ X Y := (α_ X Y U).inv
  μₗ_naturality_left {X X'} f Y := by
    change (f ▷ (Y ⊗ U)) ≫ (α_ X' Y U).inv = (α_ X Y U).inv ≫ ((f ▷ Y) ▷ U)
    monoidal
  μₗ_naturality_right X {Y Y'} f := by
    change (X ◁ (f ▷ U)) ≫ (α_ X Y' U).inv = (α_ X Y U).inv ≫ ((X ◁ f) ▷ U)
    monoidal
  μₗ_associativity X Y Z := by
    change (α_ (X ⊗ Y) Z U).inv ≫ ((α_ X Y Z).hom ▷ U) =
      (α_ X Y (Z ⊗ U)).hom ≫ (X ◁ (α_ Y Z U).inv) ≫ (α_ X (Y ⊗ Z) U).inv
    monoidal
  μₗ_unitality Y := by
    change (λ_ (Y ⊗ U)).hom = (α_ (𝟙_ C) Y U).inv ≫ ((λ_ Y).hom ▷ U)
    monoidal
  δₗ X Y := (α_ X Y U).hom
  δₗ_naturality_left {X X'} f Y := by
    change ((f ▷ Y) ▷ U) ≫ (α_ X' Y U).hom = (α_ X Y U).hom ≫ (f ▷ (Y ⊗ U))
    monoidal
  δₗ_naturality_right X {Y Y'} f := by
    change ((X ◁ f) ▷ U) ≫ (α_ X Y' U).hom = (α_ X Y U).hom ≫ (X ◁ (f ▷ U))
    monoidal
  δₗ_associativity X Y Z := by
    change (α_ (X ⊗ Y) Z U).hom ≫ (α_ X Y (Z ⊗ U)).hom =
      ((α_ X Y Z).hom ▷ U) ≫ (α_ X (Y ⊗ Z) U).hom ≫ (X ◁ (α_ Y Z U).hom)
    monoidal
  δₗ_unitality_inv Y := by
    change (λ_ (Y ⊗ U)).inv = ((λ_ Y).inv ▷ U) ≫ (α_ (𝟙_ C) Y U).hom
    monoidal
  μₗ_comp_δₗ X Y := (α_ X Y U).inv_hom_id
  δₗ_comp_μₗ X Y := (α_ X Y U).hom_inv_id

variable (F : C ⥤ C) [F.LeftLinear C]

/-- The actual regular-module Eilenberg--Watts isomorphism. -/
def regularRepresentationIso : F ≅ tensorRight (F.obj (𝟙_ C)) :=
  NatIso.ofComponents (fun X =>
    (F.mapIso (ρ_ X)).symm ≪≫ (Functor.LeftLinear.μₗIso F X (𝟙_ C)).symm)
    (fun {X Y} f => by
      change F.map f ≫ (F.map (ρ_ Y).inv ≫ Functor.OplaxLeftLinear.δₗ F Y (𝟙_ C)) =
        (F.map (ρ_ X).inv ≫ Functor.OplaxLeftLinear.δₗ F X (𝟙_ C)) ≫
          (f ▷ F.obj (𝟙_ C))
      rw [← Category.assoc, ← F.map_comp, rightUnitor_inv_naturality, F.map_comp]
      simp only [Category.assoc]
      have hn := Functor.OplaxLeftLinear.δₗ_naturality_left F f (𝟙_ C)
      change F.map (f ▷ (𝟙_ C)) ≫ Functor.OplaxLeftLinear.δₗ F Y (𝟙_ C) =
        Functor.OplaxLeftLinear.δₗ F X (𝟙_ C) ≫ (f ▷ F.obj (𝟙_ C)) at hn
      rw [hn])

@[simp] theorem regularRepresentationIso_hom (X : C) :
    (regularRepresentationIso F).hom.app X =
      F.map (ρ_ X).inv ≫ Functor.OplaxLeftLinear.δₗ F X (𝟙_ C) := rfl

/-- The constructed identification respects the actual module structures,
so it is a module natural isomorphism, not just an ordinary identification. -/
instance regularRepresentationIso_moduleNatural :
    IsModuleNatural C (regularRepresentationIso F).hom where
  lineator X Y := by
    change Functor.LaxLeftLinear.μₗ F X Y ≫
        (F.map (ρ_ (X ⊗ Y)).inv ≫ Functor.OplaxLeftLinear.δₗ F (X ⊗ Y) (𝟙_ C)) =
      (X ◁ (F.map (ρ_ Y).inv ≫ Functor.OplaxLeftLinear.δₗ F Y (𝟙_ C))) ≫
        (α_ X Y (F.obj (𝟙_ C))).inv
    apply (cancel_mono (α_ X Y (F.obj (𝟙_ C))).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have ha := Functor.OplaxLeftLinear.δₗ_associativity F X Y (𝟙_ C)
    change Functor.OplaxLeftLinear.δₗ F (X ⊗ Y) (𝟙_ C) ≫
        (α_ X Y (F.obj (𝟙_ C))).hom = F.map (α_ X Y (𝟙_ C)).hom ≫
        Functor.OplaxLeftLinear.δₗ F X (Y ⊗ (𝟙_ C)) ≫
        (X ◁ Functor.OplaxLeftLinear.δₗ F Y (𝟙_ C)) at ha
    rw [ha]
    simp only [← F.map_comp_assoc]
    have hr : (ρ_ (X ⊗ Y)).inv ≫ (α_ X Y (𝟙_ C)).hom = X ◁ (ρ_ Y).inv := by monoidal
    rw [hr]
    have hn := Functor.LaxLeftLinear.μₗ_naturality_right F X (ρ_ Y).inv
    change (X ◁ F.map (ρ_ Y).inv) ≫ Functor.LaxLeftLinear.μₗ F X (Y ⊗ (𝟙_ C)) =
      Functor.LaxLeftLinear.μₗ F X Y ≫ F.map (X ◁ (ρ_ Y).inv) at hn
    slice_lhs 1 2 => rw [← hn]
    simp only [Category.assoc]
    erw [Functor.LeftLinear.μₗ_comp_δₗ_assoc]
    rw [whiskerLeft_comp]


variable {F} {H : C ⥤ C} [H.LeftLinear C]

/-- The actual representing isomorphism is natural in all module natural
transformations. Thus their action on every object is determined by the
component at the tensor unit. -/
theorem regularRepresentationIso_natural (τ : F ⟶ H) [IsModuleNatural C τ] (X : C) :
    τ.app X ≫ (regularRepresentationIso H).hom.app X =
      (regularRepresentationIso F).hom.app X ≫ (X ◁ τ.app (𝟙_ C)) := by
  rw [regularRepresentationIso_hom, regularRepresentationIso_hom]
  rw [← Category.assoc, ← τ.naturality, Category.assoc]
  have hd := IsModuleNatural.inverse_lineator C τ X (𝟙_ C)
  change τ.app (X ⊗ (𝟙_ C)) ≫ Functor.OplaxLeftLinear.δₗ H X (𝟙_ C) =
    Functor.OplaxLeftLinear.δₗ F X (𝟙_ C) ≫ (X ◁ τ.app (𝟙_ C)) at hd
  rw [hd, Category.assoc]

/-- Equality at the unit detects equality of actual module natural
transformations on the whole regular module category. -/
theorem moduleNatTrans_ext (τ σ : F ⟶ H) [IsModuleNatural C τ] [IsModuleNatural C σ]
    (h : τ.app (𝟙_ C) = σ.app (𝟙_ C)) : τ = σ := by
  ext X
  apply (cancel_mono ((regularRepresentationIso H).hom.app X)).mp
  rw [regularRepresentationIso_natural, regularRepresentationIso_natural, h]

end Regular
end Paper18.Category.ModuleFunctor

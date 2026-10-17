import Paper18.Category.SphericalizationFusion

/-! # The actual tensor comparison with the order-two equivariantization -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
universe v u
namespace Paper18.Category.Sphericalized
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [BraidedCategory C]

def toEquivariantUnitIso : 𝟙_ (sphericalizationAction C).Equivariant ≅
    toEquivariant.obj (𝟙_ (Sphericalized C)) :=
  WeakAction.Equivariant.mkIso (sphericalizationAction C) (Iso.refl _) (by
    intro g
    fin_cases g <;>
      simp [toEquivariant, toEquivariantObj, sphericalizationAction, sphericalizationRho,
        sphericalizationAction_rho_monoidal, sphericalizationRho_monoidal, SphericalizationGroup,
        WeakAction.Equivariant.tensorUnit, WeakAction.Equivariant.tensorObj]
    all_goals rfl)

def toEquivariantTensorIso (X Y : Sphericalized C) :
    toEquivariant.obj X ⊗ toEquivariant.obj Y ≅ toEquivariant.obj (X ⊗ Y) :=
  WeakAction.Equivariant.mkIso (sphericalizationAction C) (Iso.refl _) (by
    intro g
    change ((sphericalizationAction C).ρ g).map (𝟙 (X.obj.obj ⊗ Y.obj.obj)) ≫
      ((toEquivariantObj (X ⊗ Y)).structureIso g).hom =
        (δ ((sphericalizationAction C).ρ g) X.obj.obj Y.obj.obj ≫
          (((toEquivariantObj X).structureIso g).hom ⊗ₘ
            ((toEquivariantObj Y).structureIso g).hom)) ≫ 𝟙 _
    fin_cases g <;>
      simp [toEquivariantObj, sphericalizationAction, sphericalizationRho,
        sphericalizationAction_rho_monoidal, sphericalizationRho_monoidal, SphericalizationGroup]
    rfl)

instance toEquivariant_monoidal : (toEquivariant (C := C)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := toEquivariantUnitIso
    μIso := toEquivariantTensorIso
    μIso_hom_natural_left f Z := by
      apply WeakAction.Equivariant.Hom.ext
      change (f.hom ⊗ₘ 𝟙 Z.obj.obj) ≫ 𝟙 _ = 𝟙 _ ≫ (f.hom ⊗ₘ 𝟙 Z.obj.obj)
      simp
    μIso_hom_natural_right Z f := by
      apply WeakAction.Equivariant.Hom.ext
      change (𝟙 Z.obj.obj ⊗ₘ f.hom) ≫ 𝟙 _ = 𝟙 _ ≫ (𝟙 Z.obj.obj ⊗ₘ f.hom)
      simp
    associativity X Y Z := by
      apply WeakAction.Equivariant.Hom.ext
      change (𝟙 _ ⊗ₘ 𝟙 _) ≫ 𝟙 _ ≫ (α_ X.obj.obj Y.obj.obj Z.obj.obj).hom =
        (α_ X.obj.obj Y.obj.obj Z.obj.obj).hom ≫ (𝟙 _ ⊗ₘ 𝟙 _) ≫ 𝟙 _
      simp
    left_unitality X := by
      apply WeakAction.Equivariant.Hom.ext
      change (λ_ X.obj.obj).hom = (𝟙 _ ⊗ₘ 𝟙 _) ≫ 𝟙 _ ≫ (λ_ X.obj.obj).hom
      simp
    right_unitality X := by
      apply WeakAction.Equivariant.Hom.ext
      change (ρ_ X.obj.obj).hom = (𝟙 _ ⊗ₘ 𝟙 _) ≫ 𝟙 _ ≫ (ρ_ X.obj.obj).hom
      simp }

end Paper18.Category.Sphericalized

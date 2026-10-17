import Paper18.Category.ModuleAlphaInductionFunctor
import Paper18.Category.ModuleAlphaInductionTensorBasic
import Paper18.Category.ModuleAlphaInductionOpposite

/-! # Actual strong monoidal alpha induction

The tensorator is the actual inverse action associator and the unit map
is the actual inverse action unitor. Their module compatibility is proved
from the actual half-braiding tensor and unit identities.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalLeftAction MonoidalOpposite
universe v u vM uM
namespace Paper18.Category.ModuleAlphaInduction
variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  (M : Type uM) [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ]

/-- The actual inverse action associator as a natural isomorphism. -/
def centralTensorIso (Z W : Center C) :
    centralFunctor W ⋙ centralFunctor Z ≅ centralFunctor (M := M) (Z ⊗ W) :=
  NatIso.ofComponents (fun m => (αₗ Z.1 W.1 m).symm)
    (fun {m n} f => actionAssoc_inv_naturality_right Z.1 W.1 f)

instance centralTensorIso_moduleNatural (Z W : Center C) :
    ModuleFunctor.IsModuleNatural C (centralTensorIso C M Z W).hom := by
  apply moduleNatural_of_inverse_lineator
  intro X m
  simp only [centralTensorIso, NatIso.ofComponents_hom_app, comp_δ, central_δ]
  simpa only [Iso.symm_hom, Category.assoc] using centralLineator_tensor Z W X m

/-- The actual inverse action unitor as an isomorphism of the underlying functors. -/
def centralUnitIso : 𝟭 M ≅ centralFunctor (M := M) (𝟙_ (Center C)) :=
  (MonoidalLeftAction.actionUnitNatIso C M).symm

/-- The actual inverse action unitor respects the actual central module lineator. -/
instance centralUnitIso_moduleNatural :
    ModuleFunctor.IsModuleNatural C (centralUnitIso C M).hom := by
  apply moduleNatural_of_inverse_lineator
  intro X m
  change (λₗ (X ⊙ₗ m)).inv ≫ (centralLineator (𝟙_ (Center C)) X m).hom =
    (𝟙 (X ⊙ₗ m)) ≫ X ⊴ₗ (λₗ m).inv
  simpa only [Category.id_comp] using centralLineator_unit X m

/-- Genuine tensor comparison inside the actual module-endofunctor category. -/
def centralEndTensorIso (Z W : Center C) :
    centralEnd C M W ⊗ centralEnd C M Z ≅ centralEnd C M (Z ⊗ W) :=
  ModuleFunctor.isoMk (centralTensorIso C M Z W)

/-- Genuine unit comparison inside the actual module-endofunctor category. -/
def centralEndUnitIso : 𝟙_ (End C M) ≅ centralEnd C M (𝟙_ (Center C)) :=
  ModuleFunctor.isoMk (centralUnitIso C M)

/-- The actual strong monoidal central action, using the composition
convention intrinsic to mathlib's endofunctor tensor product. -/
instance centralActionMopMonoidal : (centralActionMop C M).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := (centralEndUnitIso C M).mop
      μIso Z W := (centralEndTensorIso C M Z W).mop
      μIso_hom_natural_left {Z Z'} f W := by
        apply Quiver.Hom.unmop_inj
        apply Subtype.ext
        ext m
        change f.f ⊵ₗ (W.1 ⊙ₗ m) ≫ (αₗ Z'.1 W.1 m).inv =
          (αₗ Z.1 W.1 m).inv ≫ (f.f ▷ W.1) ⊵ₗ m
        rw [actionHomLeft_action]
        simp
      μIso_hom_natural_right {W W'} Z f := by
        apply Quiver.Hom.unmop_inj
        apply Subtype.ext
        ext m
        change Z.1 ⊴ₗ f.f ⊵ₗ m ≫ (αₗ Z.1 W'.1 m).inv =
          (αₗ Z.1 W.1 m).inv ≫ (Z.1 ◁ f.f) ⊵ₗ m
        exact actionAssoc_inv_naturality_middle Z.1 f.f m
      associativity Z W V := by
        apply Quiver.Hom.unmop_inj
        apply Subtype.ext
        ext m
        change (αₗ Z.1 W.1 (V.1 ⊙ₗ m)).inv ≫
          (αₗ (Z.1 ⊗ W.1) V.1 m).inv ≫ (α_ Z.1 W.1 V.1).hom ⊵ₗ m =
            𝟙 _ ≫ Z.1 ⊴ₗ (αₗ W.1 V.1 m).inv ≫ (αₗ Z.1 (W.1 ⊗ V.1) m).inv
        rw [associator_action_hom]
        simp
      left_unitality Z := by
        apply Quiver.Hom.unmop_inj
        apply Subtype.ext
        ext m
        change 𝟙 _ = (λₗ (Z.1 ⊙ₗ m)).inv ≫ (αₗ (𝟙_ C) Z.1 m).inv ≫ (λ_ Z.1).hom ⊵ₗ m
        rw [leftUnitor_actionHom]
        simp
      right_unitality Z := by
        apply Quiver.Hom.unmop_inj
        apply Subtype.ext
        ext m
        change 𝟙 _ = Z.1 ⊴ₗ (λₗ m).inv ≫ (αₗ Z.1 (𝟙_ C) m).inv ≫ (ρ_ Z.1).hom ⊵ₗ m
        rw [rightUnitor_actionHom]
        simp }

@[simp] theorem centralActionMop_μ (Z W : Center C) (m : M) :
    ((Functor.LaxMonoidal.μ (centralActionMop C M) Z W).unmop).val.app m =
      (αₗ Z.1 W.1 m).inv := rfl
@[simp] theorem centralActionMop_δ (Z W : Center C) (m : M) :
    ((Functor.OplaxMonoidal.δ (centralActionMop C M) Z W).unmop).val.app m =
      (αₗ Z.1 W.1 m).hom := rfl
@[simp] theorem centralActionMop_ε (m : M) :
    ((Functor.LaxMonoidal.ε (centralActionMop C M)).unmop).val.app m =
      (λₗ m).inv := rfl

variable [BraidedCategory C]
instance positiveMopMonoidal : (positiveMop C M).Monoidal := by
  change (Drinfeld.positive C ⋙ centralActionMop C M).Monoidal
  infer_instance
instance negativeMopMonoidal : (negativeMop C M).Monoidal := by
  change (Drinfeld.negative C ⋙ centralActionMop C M).Monoidal
  infer_instance

@[simp] theorem positiveMop_μ (X Y : C) (m : M) :
    ((Functor.LaxMonoidal.μ (positiveMop C M) X Y).unmop).val.app m =
      (αₗ X Y m).inv := by
  change (αₗ X Y m).inv ≫ (𝟙 (X ⊗ Y)) ⊵ₗ m = _
  simp
@[simp] theorem negativeMop_μ (X Y : C) (m : M) :
    ((Functor.LaxMonoidal.μ (negativeMop C M) X Y).unmop).val.app m =
      (αₗ X Y m).inv := by
  change (αₗ X Y m).inv ≫ (𝟙 (X ⊗ Y)) ⊵ₗ m = _
  simp
@[simp] theorem positiveMop_δ (X Y : C) (m : M) :
    ((Functor.OplaxMonoidal.δ (positiveMop C M) X Y).unmop).val.app m =
      (αₗ X Y m).hom := by
  change (𝟙 (X ⊗ Y)) ⊵ₗ m ≫ (αₗ X Y m).hom = _
  simp
@[simp] theorem negativeMop_δ (X Y : C) (m : M) :
    ((Functor.OplaxMonoidal.δ (negativeMop C M) X Y).unmop).val.app m =
      (αₗ X Y m).hom := by
  change (𝟙 (X ⊗ Y)) ⊵ₗ m ≫ (αₗ X Y m).hom = _
  simp
@[simp] theorem positiveMop_ε (m : M) :
    ((Functor.LaxMonoidal.ε (positiveMop C M)).unmop).val.app m =
      (λₗ m).inv := by
  change (λₗ m).inv ≫ (𝟙 (𝟙_ C)) ⊵ₗ m = _
  simp
@[simp] theorem negativeMop_ε (m : M) :
    ((Functor.LaxMonoidal.ε (negativeMop C M)).unmop).val.app m =
      (λₗ m).inv := by
  change (λₗ m).inv ≫ (𝟙 (𝟙_ C)) ⊵ₗ m = _
  simp

section Linear
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [∀ m : M, (MonoidalLeftAction.actionRight C m).Additive]
  [∀ m : M, (MonoidalLeftAction.actionRight C m).Linear ℂ]
instance positiveMop_additive : (positiveMop C M).Additive := by unfold positiveMop; infer_instance
instance positiveMop_linear : (positiveMop C M).Linear ℂ := by unfold positiveMop; infer_instance
instance negativeMop_additive : (negativeMop C M).Additive := by unfold negativeMop; infer_instance
instance negativeMop_linear : (negativeMop C M).Linear ℂ := by unfold negativeMop; infer_instance
end Linear
end Paper18.Category.ModuleAlphaInduction

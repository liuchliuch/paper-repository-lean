import Paper18.Category.ModuleAlphaInductionCentral

/-! # The actual central crossing is a module-natural flip

Only the actual half-braiding of the central object is used.  The ambient
monoidal category need not be braided or pivotal.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.ModuleAlphaInduction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The half-braiding hexagon is precisely compatibility with the ordinary
right-tensor module lineator. -/
@[reassoc] theorem centralFlip_lineator (Z : Center C) (X m : C) :
    (α_ X Z.1 m).inv ≫ (Z.2.β X).inv ▷ m ≫ (α_ Z.1 X m).hom ≫
      (Z.2.β (X ⊗ m)).hom =
    X ◁ (Z.2.β m).hom ≫ (α_ X m Z.1).inv := by
  rw [Z.2.monoidal]
  simp only [Category.assoc, Iso.hom_inv_id_assoc,
    inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc]

/-- Actual crossing from the central left action to ordinary right tensoring. -/
def centralFlip (Z : Center C) : centralFunctor (M := C) Z ≅ tensorRight Z.1 :=
  NatIso.ofComponents (fun m => Z.2.β m) (fun f => Z.2.naturality f)

@[simp] theorem centralFlip_hom_app (Z : Center C) (m : C) :
    (centralFlip Z).hom.app m = (Z.2.β m).hom := rfl

instance centralFlip_moduleNatural (Z : Center C) :
    ModuleFunctor.IsModuleNatural C (centralFlip Z).hom where
  lineator X m := by
    rw [central_μ]
    dsimp only [centralLineator, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv]
    simp only [Category.assoc]
    change (α_ X Z.1 m).inv ≫ (Z.2.β X).inv ▷ m ≫
        (α_ Z.1 X m).hom ≫ (Z.2.β (X ⊗ m)).hom =
      X ◁ (Z.2.β m).hom ≫ (α_ X m Z.1).inv
    exact centralFlip_lineator Z X m

end Paper18.Category.ModuleAlphaInduction

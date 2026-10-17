import Paper18.Category.GraphPicardCentralFunctor

/-! # Native module lineators give the actual Morita central crossing

A central acting object crosses every actual strong module endofunctor.
The crossing is the actual inverse module lineator. Its compatibility as
a morphism of strong module functors follows from the genuine action
associativity and naturality laws, without a Morita-equivalence premise.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalLeftAction
universe v u vM uM
namespace Paper18.Category.GraphPicard.Morita
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ]
local notation "EndM" => ModuleAlphaInduction.End C M

/-- The actual native lineator, as an isomorphism between the two actual
composites with the given central action. -/
def nativeLineatorIso (Z : Center C) (F : EndM) :
    F.toFunctor ⋙ ModuleAlphaInduction.centralFunctor Z ≅
      ModuleAlphaInduction.centralFunctor Z ⋙ F.toFunctor :=
  NatIso.ofComponents (fun m => Functor.LeftLinear.μₗIso F.toFunctor Z.1 m)
    (fun f => Functor.LaxLeftLinear.μₗ_naturality_right F.toFunctor Z.1 f)

/-- The genuine inverse lineator is a genuine morphism of native strong
module functors; the central crossing enters through its actual action. -/
instance nativeLineatorIso_symm_moduleNatural (Z : Center C) (F : EndM) :
    ModuleFunctor.IsModuleNatural C (nativeLineatorIso Z F).symm.hom := by
  apply ModuleAlphaInduction.moduleNatural_of_inverse_lineator
  intro X m
  simp only [ModuleAlphaInduction.comp_δ, ModuleAlphaInduction.central_δ, Category.assoc]
  change Functor.OplaxLeftLinear.δₗ F.toFunctor Z.1 (X ⊙ₗ m) ≫
      Z.1 ⊴ₗ Functor.OplaxLeftLinear.δₗ F.toFunctor X m ≫
        (ModuleAlphaInduction.centralLineator Z X (F.toFunctor.obj m)).hom =
    F.toFunctor.map (ModuleAlphaInduction.centralLineator Z X m).hom ≫
      Functor.OplaxLeftLinear.δₗ F.toFunctor X (Z.1 ⊙ₗ m) ≫
        X ⊴ₗ Functor.OplaxLeftLinear.δₗ F.toFunctor Z.1 m
  dsimp only [ModuleAlphaInduction.centralLineator, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, actionRight_map]
  rw [Functor.OplaxLeftLinear.δₗ_associativity_inv_assoc,
    ← Functor.OplaxLeftLinear.δₗ_naturality_left_assoc,
    Functor.OplaxLeftLinear.δₗ_associativity]
  simp only [Functor.map_comp, Category.assoc]

/-- The actual crossing in the native module-endofunctor category. -/
def centralSwap (Z : Center C) (F : EndM) :
    ModuleAlphaInduction.centralEnd C M Z ⊗ F ≅
      F ⊗ ModuleAlphaInduction.centralEnd C M Z :=
  ModuleFunctor.isoMk (nativeLineatorIso Z F).symm

@[simp] theorem centralSwap_hom_app (Z : Center C) (F : EndM) (m : M) :
    (centralSwap Z F).hom.val.app m = Functor.OplaxLeftLinear.δₗ F.toFunctor Z.1 m := rfl

@[simp] theorem centralSwap_inv_app (Z : Center C) (F : EndM) (m : M) :
    (centralSwap Z F).inv.val.app m = Functor.LaxLeftLinear.μₗ F.toFunctor Z.1 m := rfl

end Paper18.Category.GraphPicard.Morita

import Paper18.Category.ModuleAlphaInductionBasic
import Paper18.Category.FixedBoundaryModuleStrong

/-! # Strongness and morphisms of the actual central module action -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalLeftAction
universe v u vM uM
namespace Paper18.Category.ModuleAlphaInduction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type uM} [Category.{vM} M] [MonoidalLeftAction C M]

/-- The actual isomorphic central lineators give a genuine native strong
module functor. This construction needs no chosen pivotal structure. -/
def centralLeftLinear (Z : Center C) :
    (MonoidalLeftAction.actionLeft M Z.1).LeftLinear C := by
  letI := centralOplaxLeftLinear (M := M) Z
  letI (X : C) (m : M) :
      IsIso (Functor.OplaxLeftLinear.δₗ (MonoidalLeftAction.actionLeft M Z.1) X m) :=
    (centralLineator Z X m).isIso_hom
  exact ModuleFunctor.leftLinearOfOplax (MonoidalLeftAction.actionLeft M Z.1)

/-- The actual underlying endofunctor, carrying the actual central strong lineator. -/
def centralFunctor (Z : Center C) : M ⥤ M := MonoidalLeftAction.actionLeft M Z.1

instance centralFunctorLeftLinear (Z : Center C) : (centralFunctor (M := M) Z).LeftLinear C :=
  centralLeftLinear Z

@[simp] theorem central_δ (Z : Center C) (X : C) (m : M) :
    Functor.OplaxLeftLinear.δₗ (centralFunctor (M := M) Z) X m =
      (centralLineator Z X m).hom := rfl

@[simp] theorem central_μ (Z : Center C) (X : C) (m : M) :
    Functor.LaxLeftLinear.μₗ (centralFunctor (M := M) Z) X m =
      (centralLineator Z X m).inv := by
  change inv (centralLineator Z X m).hom = (centralLineator Z X m).inv
  simp

/-- Actual natural transformations are the actual action of central morphisms. -/
def centralMap {Z W : Center C} (f : Z ⟶ W) :
    centralFunctor (M := M) Z ⟶ centralFunctor (M := M) W where
  app m := f.f ⊵ₗ m
  naturality m n g := action_exchange f.f g

/-- Centrality is exactly naturality of the inverse module lineators. -/
@[reassoc] theorem centralLineator_naturality_center {Z W : Center C}
    (f : Z ⟶ W) (X : C) (m : M) :
    f.f ⊵ₗ (X ⊙ₗ m) ≫ (centralLineator W X m).hom =
      (centralLineator Z X m).hom ≫ X ⊴ₗ f.f ⊵ₗ m := by
  dsimp only [centralLineator, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    actionRight_map]
  rw [actionHomLeft_action]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_actionHomLeft_assoc, f.comm, comp_actionHomLeft]
  rw [whiskerLeft_actionHomLeft]
  simp

/-- The actual transformations respect the genuine strong module structures. -/
instance centralMap_moduleNatural {Z W : Center C} (f : Z ⟶ W) :
    ModuleFunctor.IsModuleNatural C (centralMap (M := M) f) where
  lineator X m := by
    simp only [central_μ]
    change (centralLineator Z X m).inv ≫ f.f ⊵ₗ (X ⊙ₗ m) =
      X ⊴ₗ f.f ⊵ₗ m ≫ (centralLineator W X m).inv
    apply (cancel_mono (centralLineator W X m).hom).mp
    rw [Category.assoc, centralLineator_naturality_center]
    simp

end Paper18.Category.ModuleAlphaInduction

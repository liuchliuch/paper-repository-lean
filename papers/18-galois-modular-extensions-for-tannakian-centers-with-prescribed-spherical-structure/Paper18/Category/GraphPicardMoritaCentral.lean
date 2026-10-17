import Paper18.Category.GraphPicardMoritaCentralBasic

/-! # The actual Morita center functor

Central objects act with a genuine half-braiding against every actual
strong module endofunctor. The half-braiding tensor law is precisely the
composition law of native lineators, and its naturality is native module
naturality. No fullness, dominance or Morita-equivalence premise appears.
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

/-- The actual inverse native lineator is monoidal and natural in the
actual module endofunctor, hence is a genuine half-braiding. -/
def centralHalfBraiding (Z : Center C) :
    HalfBraiding (ModuleAlphaInduction.centralEnd C M Z) where
  β F := centralSwap Z F
  monoidal F G := by
    apply ModuleFunctor.bundled_hom_ext
    ext m
    change Functor.OplaxLeftLinear.δₗ (F.toFunctor ⋙ G.toFunctor) Z.1 m =
      𝟙 _ ≫ G.toFunctor.map (Functor.OplaxLeftLinear.δₗ F.toFunctor Z.1 m) ≫
        𝟙 _ ≫ Functor.OplaxLeftLinear.δₗ G.toFunctor Z.1 (F.toFunctor.obj m) ≫ 𝟙 _
    simpa only [Category.id_comp, Category.comp_id] using
      ModuleAlphaInduction.comp_δ F.toFunctor G.toFunctor Z.1 m
  naturality {F G} τ := by
    apply ModuleFunctor.bundled_hom_ext
    ext m
    change τ.val.app (Z.1 ⊙ₗ m) ≫ Functor.OplaxLeftLinear.δₗ G.toFunctor Z.1 m =
      Functor.OplaxLeftLinear.δₗ F.toFunctor Z.1 m ≫ Z.1 ⊴ₗ τ.val.app m
    exact ModuleFunctor.IsModuleNatural.inverse_lineator C τ.val Z.1 m

/-- A genuine central acting object gives a genuine object of the center
of the native module-endofunctor category. -/
def centralObject (Z : Center C) : Center EndM :=
  ⟨ModuleAlphaInduction.centralEnd C M Z, centralHalfBraiding Z⟩

/-- Actual central maps commute with every actual inverse module lineator. -/
def centralMap {Z W : Center C} (f : Z ⟶ W) : centralObject (M := M) Z ⟶ centralObject W where
  f := (ModuleAlphaInduction.centralAction C M).map f
  comm F := by
    apply ModuleFunctor.bundled_hom_ext
    ext m
    change F.toFunctor.map (f.f ⊵ₗ m) ≫ Functor.OplaxLeftLinear.δₗ F.toFunctor W.1 m =
      Functor.OplaxLeftLinear.δₗ F.toFunctor Z.1 m ≫ f.f ⊵ₗ F.toFunctor.obj m
    exact Functor.OplaxLeftLinear.δₗ_naturality_left F.toFunctor f.f m

/-- The actual central action lifts to the actual center of native module
endofunctors, without any alpha-induction equivalence assumption. -/
def centralLift : Center C ⥤ Center EndM where
  obj := centralObject
  map f := centralMap f
  map_id Z := by apply Center.ext; exact (ModuleAlphaInduction.centralAction C M).map_id Z
  map_comp f g := by apply Center.ext; exact (ModuleAlphaInduction.centralAction C M).map_comp f g

@[simp] theorem centralLift_comp_forget :
    centralLift (C := C) (M := M) ⋙ Center.forget EndM =
      ModuleAlphaInduction.centralAction C M := rfl

end Paper18.Category.GraphPicard.Morita

namespace Paper18.Category.GraphPicard
variable (D : Type u) [Category.{v} D] [MonoidalCategory D]
  (M : Type uM) [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction Dᴹᵒᵖ M]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Linear ℂ]

/-- The right central action has an actual central lift on every actual
right module category, including each actual graph-module component. -/
def rightCentralLift : Center D ⥤ Center (ModuleAlphaInduction.End Dᴹᵒᵖ M) :=
  centerOpposite ⋙ Morita.centralLift

@[simp] theorem rightCentralLift_comp_forget :
    rightCentralLift D M ⋙ Center.forget (ModuleAlphaInduction.End Dᴹᵒᵖ M) =
      rightCentralAction D M := rfl

end Paper18.Category.GraphPicard

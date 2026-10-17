import Paper18.Category.GraphPicardMoritaCentral

/-! # Actual tensor comparisons of the Morita central lift

Native lineator associativity and its unit law prove that the already
constructed strong central action tensorators are morphisms in the
actual center of module endofunctors.
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

/-- The genuine reversed central tensor comparison, with its central
morphism law derived from native lineator associativity. -/
def centralTensorLiftIso (Z W : Center C) :
    centralObject (M := M) W ⊗ centralObject Z ≅ centralObject (Z ⊗ W) := by
  refine Center.isoMk ⟨(ModuleAlphaInduction.centralEndTensorIso C M Z W).hom, ?_⟩
  intro F
  apply ModuleFunctor.bundled_hom_ext
  ext m
  change F.toFunctor.map (αₗ Z.1 W.1 m).inv ≫
      Functor.OplaxLeftLinear.δₗ F.toFunctor (Z.1 ⊗ W.1) m =
    (𝟙 _ ≫ Functor.OplaxLeftLinear.δₗ F.toFunctor Z.1 (W.1 ⊙ₗ m) ≫
      𝟙 _ ≫ Z.1 ⊴ₗ Functor.OplaxLeftLinear.δₗ F.toFunctor W.1 m ≫ 𝟙 _) ≫
        (αₗ Z.1 W.1 (F.toFunctor.obj m)).inv
  simpa only [Category.id_comp, Category.comp_id, Category.assoc] using
    (Functor.OplaxLeftLinear.δₗ_associativity_inv F.toFunctor Z.1 W.1 m).symm

/-- The actual central unit comparison is central by the actual native
module-functor unit equation. -/
def centralUnitLiftIso : 𝟙_ (Center EndM) ≅ centralObject (M := M) (𝟙_ (Center C)) := by
  refine Center.isoMk ⟨(ModuleAlphaInduction.centralEndUnitIso C M).hom, ?_⟩
  intro F
  apply ModuleFunctor.bundled_hom_ext
  ext m
  change F.toFunctor.map (λₗ[C] m).inv ≫
      Functor.OplaxLeftLinear.δₗ F.toFunctor (𝟙_ C) m =
    (𝟙 _ ≫ 𝟙 _) ≫ (λₗ[C] (F.toFunctor.obj m)).inv
  simpa only [Category.id_comp] using
    (Functor.OplaxLeftLinear.δₗ_unitality_inv F.toFunctor m).symm

end Paper18.Category.GraphPicard.Morita

namespace Paper18.Category.GraphPicard
variable (D : Type u) [Category.{v} D] [MonoidalCategory D]
  (M : Type uM) [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction Dᴹᵒᵖ M]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Linear ℂ]

/-- The actual right central action tensorator, lifted to genuine centers. -/
def rightCentralTensorLiftIso (Z W : Center D) :
    (rightCentralLift D M).obj Z ⊗ (rightCentralLift D M).obj W ≅
      (rightCentralLift D M).obj (Z ⊗ W) :=
  Morita.centralTensorLiftIso (centerOpposite.obj W) (centerOpposite.obj Z) ≪≫
    Morita.centralLift.mapIso (centerOppositeTensorIso Z W)

/-- The actual right central action unit comparison, lifted to genuine centers. -/
def rightCentralUnitLiftIso :
    𝟙_ (Center (ModuleAlphaInduction.End Dᴹᵒᵖ M)) ≅ (rightCentralLift D M).obj (𝟙_ (Center D)) :=
  Morita.centralUnitLiftIso ≪≫ Morita.centralLift.mapIso centerOppositeUnitIso

end Paper18.Category.GraphPicard

import Paper18.Category.GraphPicardMoritaProductActionCoherence
import Paper18.Category.GraphPicardMoritaProductFunctorComposition

/-! # Genuine module functors preserve the actual residual module action

The new lineator is the transported actual central-action comparison.
Its associativity and unit equations are the actual original lineator
equations, through the proved underlying coherence of the lifted action.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalLeftAction
open scoped MonObj
universe v u vM uM vN uN
namespace Paper18.Category.GraphPicard.MoritaProduct
variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ]
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [MonoidalLeftAction C N]
  [∀ X : C, (MonoidalLeftAction.actionLeft N X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft N X).Linear ℂ]
  (A : C) [MonObj A] (F : M ⥤ N) [F.LeftLinear C]

omit [BraidedCategory C] [Preadditive M] [Linear ℂ M] [Preadditive N] [Linear ℂ N]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ]
  [∀ X : C, (MonoidalLeftAction.actionLeft N X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft N X).Linear ℂ] in
@[simp] theorem transportMapHom {P Q : Mod_ M A} (f : P ⟶ Q) :
    ((ModuleFunctor.mapActionModules F).map f).hom = F.map f.hom := rfl

/-- An actual module functor transports the actual remaining action.
The lineator is a genuine isomorphism, constructed from central action. -/
def transportResidualLaxLeftLinear :
    letI := negativeLiftedAction C M A
    letI := negativeLiftedAction C N A
    (ModuleFunctor.mapActionModules (A := A) F).LaxLeftLinear C := by
  letI := negativeLiftedAction C M A
  letI := negativeLiftedAction C N A
  exact
    { μₗ X P := (transportedCentralActionIso F ((Drinfeld.negative C).obj X)).hom.app P
      μₗ_naturality_left := by
        intro X Y f P
        apply Mod_.Hom.ext
        simp only [Mod_.comp_hom', transportMapHom, transportedCentralActionIso_hom,
          negativeLiftedAction_map_left]
        exact Functor.LaxLeftLinear.μₗ_naturality_left F f P.X
      μₗ_naturality_right := by
        intro X P Q f
        apply Mod_.Hom.ext
        simp only [Mod_.comp_hom', transportMapHom, transportedCentralActionIso_hom,
          negativeLiftedAction_map_right]
        exact Functor.LaxLeftLinear.μₗ_naturality_right F X f.hom
      μₗ_associativity := by
        intro X Y P
        apply Mod_.Hom.ext
        simp only [Mod_.comp_hom', transportMapHom, transportedCentralActionIso_hom,
          negativeLiftedAction_associator_hom, negativeLiftedAction_map_right]
        exact Functor.LaxLeftLinear.μₗ_associativity F X Y P.X
      μₗ_unitality := by
        intro P
        apply Mod_.Hom.ext
        simp only [Mod_.comp_hom', transportMapHom, transportedCentralActionIso_hom,
          negativeLiftedAction_unit_hom]
        exact Functor.LaxLeftLinear.μₗ_unitality F P.X }

/-- The actual inverse central-action comparisons make the transported
module functor genuinely strong. -/
def transportResidualLeftLinear :
    letI := negativeLiftedAction C M A
    letI := negativeLiftedAction C N A
    (ModuleFunctor.mapActionModules (A := A) F).LeftLinear C := by
  letI := negativeLiftedAction C M A
  letI := negativeLiftedAction C N A
  letI := transportResidualLaxLeftLinear C A F
  letI (X : C) (P : Mod_ M A) :
      IsIso (Functor.LaxLeftLinear.μₗ (ModuleFunctor.mapActionModules F) X P) :=
    by
      change IsIso ((transportedCentralActionIso F ((Drinfeld.negative C).obj X)).hom.app P)
      infer_instance
  exact ModuleFunctor.leftLinearOfLax (C := C) (ModuleFunctor.mapActionModules F)

end Paper18.Category.GraphPicard.MoritaProduct

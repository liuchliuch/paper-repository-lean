import Paper18.Category.GraphPicardMoritaProductActionNaturality

/-! # Underlying coherence of the actual lifted module action -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalLeftAction MonoidalOpposite
open scoped MonObj
universe v u vM uM
namespace Paper18.Category.GraphPicard.MoritaProduct
attribute [local instance] CategoryTheory.endofunctorMonoidalCategory
variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (M : Type uM) [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ]
  (A : C) [MonObj A]

/-- The actual lifted action associator has the actual original action
associator as its underlying morphism. -/
theorem negativeLiftedAction_associator_hom (X Y : C) (P : Mod_ M A) :
    letI := negativeLiftedAction C M A
    ((αₗ X Y P).hom).hom = (αₗ X Y P.X).hom := by
  letI := negativeLiftedAction C M A
  change (((Functor.Monoidal.μIso (negativeLiftedActionFunctor C M A) X Y).inv).unmop.app P).hom = _
  rw [Functor.Monoidal.μIso_inv]
  change (((Functor.OplaxMonoidal.δ
    (ModuleAlphaInduction.negativeMop C M ⋙ simultaneousMop (moduleLift C M A))
      X Y).unmop).app P).hom = _
  rw [Functor.OplaxMonoidal.comp_δ]
  change ((ModuleFunctor.mapActionModulesTransformation
    ((Functor.OplaxMonoidal.δ (ModuleAlphaInduction.negativeMop C M) X Y).unmop).val).app P).hom ≫
      (moduleLiftCompComponent C M A
        ((ModuleAlphaInduction.negative C M).obj Y)
        ((ModuleAlphaInduction.negative C M).obj X) P).inv.hom = _
  simp only [moduleLiftCompComponent, Mod_.Hom.mk'_hom]
  change ((Functor.OplaxMonoidal.δ (ModuleAlphaInduction.negativeMop C M) X Y).unmop).val.app P.X ≫
    𝟙 (X ⊙ₗ (Y ⊙ₗ P.X)) = _
  exact (Category.comp_id _).trans
    (ModuleAlphaInduction.negativeMop_δ C M X Y P.X)

/-- The actual lifted action unit also retains the actual original
action unit on underlying morphisms. -/
theorem negativeLiftedAction_unit_hom (P : Mod_ M A) :
    letI := negativeLiftedAction C M A
    ((λₗ[C] P).hom).hom = (λₗ[C] P.X).hom := by
  letI := negativeLiftedAction C M A
  change (((Functor.Monoidal.εIso (negativeLiftedActionFunctor C M A)).inv).unmop.app P).hom = _
  rw [Functor.Monoidal.εIso_inv]
  change (((Functor.OplaxMonoidal.η
    (ModuleAlphaInduction.negativeMop C M ⋙ simultaneousMop (moduleLift C M A))).unmop).app P).hom = _
  rw [Functor.OplaxMonoidal.comp_η]
  change ((ModuleFunctor.mapActionModulesTransformation
    (Functor.OplaxMonoidal.η (ModuleAlphaInduction.negativeMop C M)).unmop.val).app P).hom ≫
      (moduleLiftUnitComponent C M A P).inv.hom = _
  simp only [moduleLiftUnitComponent, Mod_.Hom.mk'_hom]
  change (Functor.OplaxMonoidal.η (ModuleAlphaInduction.negativeMop C M)).unmop.val.app P.X ≫
    𝟙 P.X = _
  refine (Category.comp_id _).trans ?_
  change (𝟙 (𝟙_ C)) ⊵ₗ P.X ≫ (λₗ[C] P.X).hom = _
  rw [id_actionHomLeft, Category.id_comp]

end Paper18.Category.GraphPicard.MoritaProduct

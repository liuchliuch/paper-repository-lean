import Paper18.Category.ModuleComponentFunctorScalar

/-! # Unique complex-unit ratios of actual module-natural comparison maps -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u vM uM vN uN w
namespace Paper18.Category.PicardAssociatorObstruction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M]
  [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)] [MonoidalLeftAction C M]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton M ι) (i : ι)
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N] [MonoidalLeftAction C N]
  {F H : ModuleComponent.Component (C := C) S i ⥤ N}
  [F.Full] [F.Faithful] [F.Linear ℂ] [F.LeftLinear C] [H.LeftLinear C]
  (a b : F ≅ H) [ModuleFunctor.IsModuleNatural C a.hom]
  [ModuleFunctor.IsModuleNatural C b.hom]

/-- The ratio of two actual comparison isomorphisms is an actual module
functor automorphism. Component Schur theory derives its unique scalar unit. -/
theorem comparison_unique_scalar :
    ∃! z : ℂˣ, ∀ X, a.hom.app X = (z : ℂ) • b.hom.app X := by
  let τ := a ≪≫ b.symm
  haveI : ModuleFunctor.IsModuleNatural C τ.hom := by
    dsimp only [τ, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  obtain ⟨z, hz, hu⟩ := ModuleComponent.functorAut_unique_scalar S i F τ
  refine ⟨z, ?_, ?_⟩
  · intro X
    have hh := congrArg (fun f => f ≫ b.hom.app X) (hz X)
    simpa only [τ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, assoc,
      Iso.inv_hom_id_app, comp_id, Linear.smul_comp, id_comp] using hh
  · intro y hy
    apply hu y
    intro X
    change a.hom.app X ≫ b.inv.app X = _
    rw [hy X, Linear.smul_comp, Iso.hom_inv_id_app]

/-- The actual complex-unit coefficient is selected from the proved
unique comparison theorem, rather than included in comparison data. -/
def comparisonScalar : ℂˣ := (comparison_unique_scalar S i a b).exists.choose

lemma comparisonScalar_spec (X : ModuleComponent.Component (C := C) S i) :
    a.hom.app X = (comparisonScalar S i a b : ℂ) • b.hom.app X :=
  (comparison_unique_scalar S i a b).exists.choose_spec X

lemma comparisonScalar_eq (z : ℂˣ)
    (h : ∀ X, a.hom.app X = (z : ℂ) • b.hom.app X) :
    comparisonScalar S i a b = z :=
  (comparison_unique_scalar S i a b).unique (comparisonScalar_spec S i a b) h

end Paper18.Category.PicardAssociatorObstruction

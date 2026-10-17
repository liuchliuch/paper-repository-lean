import Paper18.Category.ModuleFunctorSemisimpleCorner
import Paper18.Category.ModuleFunctorFiniteActionIso
import Paper18.Category.ModuleAlphaInductionEnd

/-! # Actual equivalence of module-endofunctor categories by conjugation -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u vM uM vN uN
namespace Paper18.Category.ModuleFunctor
open MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M] [MonoidalLeftAction C M]
  [∀ c : C, (actionLeft M c).Additive] [∀ c : C, (actionLeft M c).Linear ℂ]
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N] [MonoidalLeftAction C N]
  [∀ c : C, (actionLeft N c).Additive] [∀ c : C, (actionLeft N c).Linear ℂ]

instance transportRightUnitor_moduleNatural (H : M ⥤ N) [H.LeftLinear C] :
    IsModuleNatural C (Functor.rightUnitor H).hom where
  lineator X m := by
    change (𝟙 _ ≫ Functor.LaxLeftLinear.μₗ H X m) ≫ 𝟙 _ =
      (X ⊴ₗ 𝟙 _) ≫ Functor.LaxLeftLinear.μₗ H X m
    simp only [id_comp, comp_id, actionHomRight_id]

variable (I : Bundled C M N) [I.toFunctor.Full] [I.toFunctor.Faithful]
  (P : Bundled C N M) (adj : I.toFunctor ⊣ P.toFunctor)
  [IsModuleNatural C adj.unit] [IsModuleNatural C adj.counit] [IsIso adj.counit]

/-- Restrict a genuine endofunctor through the actual equivalence. -/
def cornerRestriction (H : ModuleAlphaInduction.End C N) : ModuleAlphaInduction.End C M where
  toFunctor := (I.toFunctor ⋙ H.toFunctor) ⋙ P.toFunctor
  leftLinear := inferInstance
  additive := inferInstance
  linear := inferInstance

include adj in
/-- Conjugating that genuine restriction returns the genuine endofunctor.
All comparison morphisms are actual module-natural counits and coherence maps. -/
def cornerExtensionRestrictionIso (H : ModuleAlphaInduction.End C N) :
    (cornerExtension I P).obj (cornerRestriction I P H) ≅ H := by
  letI : IsModuleNatural C (asIso adj.counit).hom :=
    inferInstanceAs (IsModuleNatural C adj.counit)
  let e :=
    (Functor.isoWhiskerRight (Functor.associator P.toFunctor
      (I.toFunctor ⋙ H.toFunctor) P.toFunctor).symm I.toFunctor) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight
      (Functor.associator P.toFunctor I.toFunctor H.toFunctor).symm P.toFunctor) I.toFunctor ≪≫
    Functor.associator ((P.toFunctor ⋙ I.toFunctor) ⋙ H.toFunctor) P.toFunctor I.toFunctor ≪≫
    Functor.isoWhiskerLeft ((P.toFunctor ⋙ I.toFunctor) ⋙ H.toFunctor) (asIso adj.counit) ≪≫
    Functor.rightUnitor ((P.toFunctor ⋙ I.toFunctor) ⋙ H.toFunctor) ≪≫
    Functor.isoWhiskerRight (asIso adj.counit) H.toFunctor ≪≫ Functor.leftUnitor H.toFunctor
  letI : IsModuleNatural C e.hom := by
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom]
    infer_instance
  exact isoMk e

include adj in
/-- Actual equivalences of native module categories induce actual
essentially surjective conjugation on genuine module endofunctors. -/
def cornerExtensionEssSurj : (cornerExtension I P).EssSurj where
  mem_essImage H := ⟨cornerRestriction I P H, ⟨cornerExtensionRestrictionIso I P adj H⟩⟩

include adj in
/-- The actual End equivalence uses the already-proved full faithfulness
and the actual constructed inverse images. -/
def cornerEndEquivalence : ModuleAlphaInduction.End C M ≌ ModuleAlphaInduction.End C N := by
  letI := cornerExtension_faithful I P adj
  letI := cornerExtension_full I P adj
  letI := cornerExtensionEssSurj I P adj
  letI : (cornerExtension I P).IsEquivalence := {}
  exact (cornerExtension I P).asEquivalence

end Paper18.Category.ModuleFunctor

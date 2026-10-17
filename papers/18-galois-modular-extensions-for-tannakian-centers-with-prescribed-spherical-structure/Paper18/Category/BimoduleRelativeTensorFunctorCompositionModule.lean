import Paper18.Category.BimoduleRelativeTensorFunctorCompositionBasic

/-! # Actual module naturality of relative tensor composition -/
noncomputable section
set_option maxHeartbeats 1000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {R S T : D} [MonObj R] [MonObj S] [MonObj T]

instance π_double_right_epi (P : Native R S) (Q : Native S T) (N X : D) :
    Epi ((π P Q ▷ N) ▷ X) := by
  exact inferInstanceAs (Epi ((tensorRight N ⋙ tensorRight X).map
    (coequalizer.π (γ[mop S,P.X].hom ▷ Q.X.X)
      ((α_ P.X.X S Q.X.X).hom ≫ P.X.X ◁ γ[S,Q.X.X]))))

/-- The actual quotient associator commutes with the actual ambient
lineators, by applying their exact quotient formulas. -/
lemma composition_lineator (P : Native R S) (Q : Native S T) (N : Mod_ D T) (X : D) :
    lineatorRaw (tensor P Q) N X ≫
        ((tensorCompositionIso P Q).hom.app (RelativeTensor.ambientTensor N X)).hom =
      ((tensorCompositionIso P Q).hom.app N).hom ▷ X ≫
        lineatorRaw P ((tensorFunctor Q).obj N) X ≫
          ((tensorFunctor P).map (lineatorHom Q N X)).hom := by
  apply (cancel_epi (moduleπ (tensor P Q) N ▷ X)).mp
  apply (cancel_epi ((π P Q ▷ N.X) ▷ X)).mp
  have hNX : π P Q ▷ (N.X ⊗ X) ≫
      moduleπ (tensor P Q) (RelativeTensor.ambientTensor N X) ≫
        ((tensorCompositionIso P Q).hom.app (RelativeTensor.ambientTensor N X)).hom =
      (α_ P.X.X Q.X.X (N.X ⊗ X)).hom ≫
        P.X.X ◁ moduleπ Q (RelativeTensor.ambientTensor N X) ≫
          moduleπ P ((tensorFunctor Q).obj (RelativeTensor.ambientTensor N X)) :=
    moduleπ_composition P Q (RelativeTensor.ambientTensor N X)
  rw [moduleπ_lineatorRaw_assoc, associator_naturality_left_assoc, hNX]
  rw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, assoc, moduleπ_composition]
  simp only [comp_whiskerRight, assoc]
  rw [moduleπ_lineatorRaw_assoc, associator_naturality_middle_assoc, moduleπ_map]
  change _ = (α_ P.X.X Q.X.X N.X).hom ▷ X ≫
    (α_ P.X.X (Q.X.X ⊗ N.X) X).hom ≫
      P.X.X ◁ (moduleπ Q N ▷ X) ≫ P.X.X ◁ lineatorRaw Q N X ≫
        moduleπ P ((tensorFunctor Q).obj (RelativeTensor.ambientTensor N X))
  rw [← whiskerLeft_comp_assoc, moduleπ_lineatorRaw]
  monoidal

instance tensorComposition_moduleNatural (P : Native R S) (Q : Native S T) :
    ModuleFunctor.IsModuleNatural Dᴹᵒᵖ (tensorCompositionIso P Q).hom where
  lineator X N := by
    apply Mod_.Hom.ext
    exact composition_lineator P Q N X.unmop

lemma unit_lineator (R : D) [MonObj R] (N : Mod_ D R) (X : D) :
    lineatorRaw (regular R) N X ≫
        ((tensorUnitIso R).hom.app (RelativeTensor.ambientTensor N X)).hom =
      ((tensorUnitIso R).hom.app N).hom ▷ X := by
  apply (cancel_epi (moduleπ (regular R) N ▷ X)).mp
  rw [moduleπ_lineatorRaw_assoc, moduleπ_unit, ← comp_whiskerRight, moduleπ_unit]
  change (α_ R N.X X).hom ≫ ((α_ R N.X X).inv ≫ γ[R,N.X] ▷ X) = γ[R,N.X] ▷ X
  rw [Iso.hom_inv_id_assoc]

instance tensorUnit_moduleNatural (R : D) [MonObj R] :
    ModuleFunctor.IsModuleNatural Dᴹᵒᵖ (tensorUnitIso R).hom where
  lineator X N := by
    apply Mod_.Hom.ext
    change lineatorRaw (regular R) N X.unmop ≫
        ((tensorUnitIso R).hom.app (RelativeTensor.ambientTensor N X.unmop)).hom =
      ((tensorUnitIso R).hom.app N).hom ▷ X.unmop ≫ 𝟙 _
    rw [comp_id]
    exact unit_lineator R N X.unmop

end Paper18.Category.BimoduleRelativeTensor

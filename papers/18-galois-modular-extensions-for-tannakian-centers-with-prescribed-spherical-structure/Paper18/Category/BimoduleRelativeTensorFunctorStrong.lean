import Paper18.Category.BimoduleRelativeTensorFunctorModule

/-! # Actual strong ambient-module structure of relative tensor functors -/
noncomputable section
set_option maxHeartbeats 1000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {R S : D} [MonObj R] [MonObj S] (P : Native R S)

def tensorFunctorLaxLeftLinear : (tensorFunctor P).LaxLeftLinear Dᴹᵒᵖ where
  μₗ X N := lineatorHom P N X.unmop
  μₗ_naturality_left {X Y} f N := by
    apply Mod_.Hom.ext
    change ((tensorFunctor P).obj N).X ◁ f.unmop ≫ lineatorRaw P N Y.unmop =
      lineatorRaw P N X.unmop ≫
        ((tensorFunctor P).map (RelativeTensor.ambientTensorMapRight N f.unmop)).hom
    apply (cancel_epi (moduleπ P N ▷ X.unmop)).mp
    rw [← whisker_exchange_assoc, moduleπ_lineatorRaw, moduleπ_lineatorRaw_assoc,
      moduleπ_map]
    change _ = (α_ P.X.X N.X X.unmop).hom ≫
      P.X.X ◁ (N.X ◁ f.unmop) ≫ moduleπ P (RelativeTensor.ambientTensor N Y.unmop)
    monoidal
  μₗ_naturality_right X {N N'} f := by
    apply Mod_.Hom.ext
    change ((tensorFunctor P).map f).hom ▷ X.unmop ≫ lineatorRaw P N' X.unmop =
      lineatorRaw P N X.unmop ≫
        ((tensorFunctor P).map (RelativeTensor.ambientTensorMap f X.unmop)).hom
    apply (cancel_epi (moduleπ P N ▷ X.unmop)).mp
    rw [← comp_whiskerRight_assoc, moduleπ_map, comp_whiskerRight_assoc,
      moduleπ_lineatorRaw, moduleπ_lineatorRaw_assoc, moduleπ_map]
    change _ = (α_ P.X.X N.X X.unmop).hom ≫
      P.X.X ◁ (f.hom ▷ X.unmop) ≫ moduleπ P (RelativeTensor.ambientTensor N' X.unmop)
    monoidal
  μₗ_associativity X Y N := by
    apply Mod_.Hom.ext
    change lineatorRaw P N (Y.unmop ⊗ X.unmop) ≫
        ((tensorFunctor P).map (RelativeTensor.ambientTensorAssoc N Y.unmop X.unmop).inv).hom =
      (α_ ((tensorFunctor P).obj N).X Y.unmop X.unmop).inv ≫
        lineatorRaw P N Y.unmop ▷ X.unmop ≫
          lineatorRaw P (RelativeTensor.ambientTensor N Y.unmop) X.unmop
    apply (cancel_epi (moduleπ P N ▷ (Y.unmop ⊗ X.unmop))).mp
    rw [moduleπ_lineatorRaw_assoc, moduleπ_map,
      associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc,
      moduleπ_lineatorRaw, comp_whiskerRight_assoc, moduleπ_lineatorRaw]
    change (α_ P.X.X N.X (Y.unmop ⊗ X.unmop)).hom ≫
      P.X.X ◁ (α_ N.X Y.unmop X.unmop).inv ≫
        moduleπ P (RelativeTensor.ambientTensor
          (RelativeTensor.ambientTensor N Y.unmop) X.unmop) = _
    monoidal
  μₗ_unitality N := by
    apply Mod_.Hom.ext
    change (ρ_ ((tensorFunctor P).obj N).X).hom =
      lineatorRaw P N (𝟙_ D) ≫
        ((tensorFunctor P).map (InternalModule.ambientTensorUnit N).hom).hom
    apply (cancel_epi (moduleπ P N ▷ (𝟙_ D))).mp
    rw [moduleπ_lineatorRaw_assoc, moduleπ_map]
    change _ = (α_ P.X.X N.X (𝟙_ D)).hom ≫ P.X.X ◁ (ρ_ N.X).hom ≫ moduleπ P N
    monoidal

/-- The relative tensor functor has an actual invertible lineator and
therefore is an actual strong module functor for the native ambient action. -/
instance tensorFunctorLeftLinear : (tensorFunctor P).LeftLinear Dᴹᵒᵖ := by
  letI := tensorFunctorLaxLeftLinear P
  letI (X : Dᴹᵒᵖ) (N : Mod_ D S) :
      IsIso (Functor.LaxLeftLinear.μₗ (tensorFunctor P) X N) :=
    (lineatorIso P N X.unmop).isIso_hom
  exact ModuleFunctor.leftLinearOfLax (tensorFunctor P)

end Paper18.Category.BimoduleRelativeTensor

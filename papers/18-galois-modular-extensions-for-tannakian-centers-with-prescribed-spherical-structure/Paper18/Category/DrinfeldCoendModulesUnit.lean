import Paper18.Category.DrinfeldCoendModulesAction
import Paper18.Category.DeligneTensorProductMap

/-! # The actual unit of the coend algebra and its annular action -/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open CategoryTheory.BraidedCategory
open scoped MonObj
universe v u w
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
open DiagonalAlgebra
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

@[reassoc]
lemma capPairIso_unit : Functor.LaxMonoidal.ε (tensorProductFunctor (C := D)) ≫
    (capPairIso (𝟙_ D) (𝟙_ D)).hom = (λ_ (𝟙_ D)).inv := by
  have h := NatTrans.IsMonoidal.unit (τ := (DeligneTensorProductMap.capEmbeddingIso D).hom)
  simp only [Functor.LaxMonoidal.comp_ε] at h
  change (Functor.LaxMonoidal.ε (tensorProductFunctor (C := D)) ≫
    (tensorProductFunctor (C := D)).map (𝟙 _)) ≫
      (DeligneTensorProductMap.capEmbeddingIso D).hom.app ⟨𝟙_ D,𝟙_ D⟩ =
    Functor.LaxMonoidal.ε (DeligneTensorProductMap.rawTensor D) at h
  rw [CategoryTheory.Functor.map_id, comp_id, DeligneTensorProductMap.rawTensor_unit] at h
  have he : (DeligneTensorProductMap.capEmbeddingIso D).hom.app ⟨𝟙_ D,𝟙_ D⟩ =
      (capPairIso (𝟙_ D) (𝟙_ D)).hom :=
    congrArg Iso.hom (DeligneTensorProductMap.capEmbeddingIso_app (𝟙_ D) (𝟙_ D))
  rw [he] at h
  exact h

/-- The actual chosen-dual unit insertion. -/
def unitInjection : 𝟙_ D ⟶ dual D (𝟙_ D) ⊗ 𝟙_ D :=
  (λ_ (𝟙_ D)).inv ≫ (dualUnitIso (C := D)).inv ▷ 𝟙_ D

lemma unitInjection_cap : unitInjection (D := D) ≫ ε_ (𝟙_ D) (dual D (𝟙_ D)) = 𝟙 _ := by
  rw [unitInjection, assoc, dualUnitIso_inv_evaluation, ← unitors_equal, Iso.inv_hom_id]

def unitCapMap : 𝟙_ (DeligneProduct D D) ⟶
    DeligneProduct.externalObject (dual D (𝟙_ D)) (𝟙_ D) :=
  capPairMap (dualUnitIso (C := D)).inv (𝟙 _)

@[reassoc]
lemma unitCapMap_pair : Functor.LaxMonoidal.ε (tensorProductFunctor (C := D)) ≫
    (tensorProductFunctor (C := D)).map (unitCapMap (D := D)) ≫
      (capPairIso (dual D (𝟙_ D)) (𝟙_ D)).hom = unitInjection (D := D) := by
  dsimp only [unitCapMap, unitInjection]
  rw [capPairIso_naturality, tensorHom_id, capPairIso_unit_assoc]

lemma algebra_one_counit :
    (tensorProductFunctor (C := D)).map η[canonicalAlgebra S] ≫ canonicalAlgebraCounit S =
      Functor.OplaxMonoidal.η (tensorProductFunctor (C := D)) := by
  letI := DeligneProduct.hasKernels S S
  exact semisimpleAdjointAlgebra_one_counit
    (DeligneProduct.skeleton S S) (tensorProductFunctor (C := D))

/-- The actual canonical diagonal unit is exactly the unit cap generator. -/
lemma capGenerator_one : unitCapMap (D := D) ≫ capGenerator S (𝟙_ D) =
    η[canonicalAlgebra S] := by
  apply ((tensorProductRightAdjunction S).homEquiv _ _).symm.injective
  change (tensorProductFunctor (C := D)).map
      (unitCapMap (D := D) ≫ capGenerator S (𝟙_ D)) ≫ canonicalAlgebraCounit S =
    (tensorProductFunctor (C := D)).map η[canonicalAlgebra S] ≫ canonicalAlgebraCounit S
  apply (cancel_epi (Functor.LaxMonoidal.ε (tensorProductFunctor (C := D)))).mp
  simp only [Functor.map_comp, assoc]
  rw [capGenerator_counit, unitCapMap_pair_assoc, unitInjection_cap, algebra_one_counit,
    Functor.Monoidal.ε_η]

/-- The actual transported algebra unit has the expected actual coend insertion. -/
lemma injection_one : η[algebra S] = unitInjection (D := D) ≫ injection S (𝟙_ D) := by
  change Functor.LaxMonoidal.ε (tensorProductFunctor (C := D)) ≫
    (tensorProductFunctor (C := D)).map η[canonicalAlgebra S] = _
  rw [← capGenerator_one S, Functor.map_comp, ← assoc]
  have h : Functor.LaxMonoidal.ε (tensorProductFunctor (C := D)) ≫
      (tensorProductFunctor (C := D)).map (unitCapMap (D := D)) =
        unitInjection (D := D) ≫ (capPairIso (dual D (𝟙_ D)) (𝟙_ D)).inv := by
    apply (cancel_mono (capPairIso (dual D (𝟙_ D)) (𝟙_ D)).hom).mp
    rw [assoc, unitCapMap_pair, assoc, Iso.inv_hom_id, comp_id]
  rw [h, assoc]
  rfl

lemma holonomy_unit (Z : Center D) : (holonomy Z (𝟙_ D)).hom = 𝟙 _ := by
  dsimp only [holonomy, Iso.trans_hom, Iso.symm_hom]
  have hu : Z.2.β (𝟙_ D) = ρ_ Z.1 ≪≫ (λ_ Z.1).symm := by
    apply Iso.ext
    exact Drinfeld.halfBraiding_unit Z.1 Z.2
  rw [hu]
  simp only [Iso.trans_inv, Iso.symm_inv, braiding_inv_tensorUnit_left]
  simp

lemma actionComponent_unit (Z : Center D) : actionComponent Z (𝟙_ D) =
    ε_ (𝟙_ D) (dual D (𝟙_ D)) ▷ Z.1 ≫ (λ_ Z.1).hom := by
  rw [actionComponent_def, holonomy_unit]
  simp only [whiskerLeft_id, id_comp, Iso.hom_inv_id_assoc]

/-- The constructed annular map satisfies the actual module unit law. -/
lemma action_one (Z : Center D) : η[algebra S] ▷ Z.1 ≫ action S Z = (λ_ Z.1).hom := by
  rw [injection_one, comp_whiskerRight, assoc, injection_action, actionComponent_unit]
  rw [← comp_whiskerRight_assoc, unitInjection_cap, id_whiskerRight, id_comp]

end Paper18.Category.DrinfeldCoendModules

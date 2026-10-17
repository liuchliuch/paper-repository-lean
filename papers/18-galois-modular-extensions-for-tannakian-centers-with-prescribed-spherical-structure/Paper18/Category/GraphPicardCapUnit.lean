import Paper18.Category.GraphPicardGraphTensorFormula
import Paper18.Category.GraphPicardCapComparison
import Paper18.Category.GraphPicardCapUnitBasic

/-! # Actual unit normalization of the graph cap comparison -/
noncomputable section
set_option maxHeartbeats 2000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped MonObj MonoidalLeftAction TensorProduct
universe v u w
namespace Paper18.Category.GraphPicard
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ] [α.IsEquivalence]

@[reassoc] lemma graphPairIso_unit :
    ε (GraphLagrangian.graphFunctor α) ≫ (graphPairIso α (𝟙_ D) (𝟙_ D)).hom =
      ε (graphRaw α) := by
  have h := NatTrans.IsMonoidal.unit (τ := (graphEmbeddingIso α).hom)
  simp only [Functor.LaxMonoidal.comp_ε] at h
  change (ε (GraphLagrangian.graphFunctor α) ≫
    (GraphLagrangian.graphFunctor α).map (𝟙 _)) ≫
      (graphEmbeddingIso α).hom.app ⟨𝟙_ D,𝟙_ D⟩ = ε (graphRaw α) at h
  rw [CategoryTheory.Functor.map_id, comp_id] at h
  simpa only [show (graphEmbeddingIso α).hom.app ⟨𝟙_ D,𝟙_ D⟩ =
    (graphPairIso α (𝟙_ D) (𝟙_ D)).hom from
      congrArg Iso.hom (graphEmbeddingIso_app α (𝟙_ D) (𝟙_ D))] using h

lemma graphRaw_unit : ε (graphRaw α) =
    (λ_ (𝟙_ (Center D))).inv ≫
      (ε (Drinfeld.positive D) ⊗ₘ
        (ε (Drinfeld.negative D) ≫ (Drinfeld.negative D).map (ε α))) := by
  change ε (Drinfeld.linearFactorization D) ≫
    (Drinfeld.linearFactorization D).map
      (show (𝟙_ (LinearTensor D D)) ⟶ (⟨𝟙_ D,α.obj (𝟙_ D)⟩ : LinearTensor D D)
        from (𝟙 (𝟙_ D)) ⊗ₜ[ℂ] ε α) = _
  rw [Drinfeld.linearFactorization_map_tmul]
  change (ε (Drinfeld.factorizationBifunctor D) ≫
    ((Drinfeld.positive D).map (𝟙 (𝟙_ D)) ⊗ₘ
      (Drinfeld.negative D).map (ε α))) = _
  have hid : (Drinfeld.positive D).map (𝟙 (𝟙_ D)) =
      𝟙 ((Drinfeld.positive D).obj (𝟙_ D)) := rfl
  have he : ε (Drinfeld.factorizationBifunctor D) =
      (λ_ (𝟙_ (Center D))).inv ≫
        (ε (Drinfeld.positive D) ⊗ₘ ε (Drinfeld.negative D)) := rfl
  rw [he, hid, assoc, tensorHom_comp_tensorHom, comp_id]

/-- The graph cap's actual unit insertion is the unit of its actual algebra. -/
lemma graphCap_one :
    ε (graphRaw α) ≫
      ((Drinfeld.positive D).map (dualUnitIso (C := D)).inv ⊗ₘ
        𝟙 ((Drinfeld.negative D).obj (α.obj (𝟙_ D)))) ≫
      graphCap S α (𝟙_ D) = η[GraphLagrangian.algebra S α] := by
  have hn := graphPairIso_naturality α (dualUnitIso (C := D)).inv (𝟙 (𝟙_ D))
  simp only [CategoryTheory.Functor.map_id] at hn
  rw [← graphPairIso_unit, assoc, ← reassoc_of% hn]
  dsimp only [graphCap]
  rw [Iso.hom_inv_id_assoc]
  exact mappedGraphCap_one S α

/-- Actual strong unit maps and the actual dual-unit comparison form
the original graph cap's genuine unit insertion. -/
lemma graphCap_unitInsertion :
    (λ_ (𝟙_ (Center D))).inv ≫
      ((ε (Drinfeld.positive D) ≫
          (Drinfeld.positive D).map (dualUnitIso (C := D)).inv) ⊗ₘ
        ε (α ⋙ Drinfeld.negative D)) ≫ graphCap S α (𝟙_ D) =
      η[GraphLagrangian.algebra S α] := by
  have h := graphCap_one S α
  rw [graphRaw_unit] at h
  simpa only [Functor.LaxMonoidal.comp_ε, tensorHom_comp_tensorHom_assoc,
    comp_id, assoc] using h

attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
local notation "A" => GraphLagrangian.algebra S α
local instance graphUnitUnderlyingMonObj : MonObj A.1 :=
  Functor.monObjObj (F := Center.forget D) A
local notation "H" => rightCentralAction D (Mod_ D A.1)

/-- The genuine cap insertion is transported through the actual strong
central action and its actual algebra character. -/
lemma graphCapPairing_unitInsertion :
    (λ_ (𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D A.1)))).inv ≫
      ((ε (graphCapPositive S α) ≫
          (graphCapPositive S α).map (dualUnitIso (C := D)).inv) ⊗ₘ
        ε (graphCapNegative S α)) ≫ graphCapPairing S α (𝟙_ D) = 𝟙 _ := by
  have h := map_capUnitInsertion H
    (ε (Drinfeld.positive D) ≫
      (Drinfeld.positive D).map (dualUnitIso (C := D)).inv)
    (ε (α ⋙ Drinfeld.negative D))
  have hh := congrArg (fun q => q ≫
    (H).map (graphCap S α (𝟙_ D)) ≫ centralCharacter A) h
  simp only [assoc, ← Functor.map_comp_assoc, graphCap_unitInsertion] at hh
  have hc : ε H ≫ (H).map η[A] ≫ centralCharacter A = 𝟙 _ :=
    centralCharacter_one A
  rw [hc] at hh
  simpa only [graphCapPairing, centralCapHom, graphCapPositive, graphCapNegative,
    Functor.comp_map, Functor.LaxMonoidal.comp_ε, Functor.map_comp, assoc] using hh

/-- The original actual graph comparison has the actual normalized unit
component. Its tensor law is handled separately, with its genuine
monodromy defect. -/
theorem graphCapComparison_unit :
    ε (graphCapNegative S α) ≫ (graphCapComparison S α).app (𝟙_ D) =
      ε (graphCapPositive S α) :=
  capFamilyNatTrans_unit_of_insertion (graphCapPositive S α) (graphCapNegative S α)
    (graphCapPairing S α) (graphCapPairing_dinaturality S α)
    (graphCapPairing_unitInsertion S α)

end Paper18.Category.GraphPicard

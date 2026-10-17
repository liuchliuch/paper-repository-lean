import Paper18.Category.DrinfeldCoendModulesCoend
import Paper18.Category.DeligneProductNondegenerateBasic

/-! # Actual simple-diagonal projections of the coend algebra -/
noncomputable section
set_option maxHeartbeats 2000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Opposite
open scoped MonObj
universe v u w
namespace Paper18.Category.DrinfeldNoPivotal
open DrinfeldCoendModules DiagonalAlgebra
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- The actual simple-diagonal projection in the canonical algebra. -/
def capProjection (i : ι) : canonicalAlgebra S ⟶
    DeligneProduct.externalObject (dual D (S.simpleObject i)) (S.simpleObject i) := by
  letI := capHasCoend S
  exact (capCoendIso S).inv ≫ (S.semisimpleCoendIso (capDiagram (D := D))).hom ≫
    biproduct.π (S.semisimpleCoendDiagonal (capDiagram (D := D))) i

@[reassoc]
lemma capGenerator_projection_self (i : ι) :
    capGenerator S (S.simpleObject i) ≫ capProjection S i = 𝟙 _ := by
  letI := capHasCoend S
  rw [← capCoendIso_ι S (S.simpleObject i)]
  dsimp only [capProjection]
  simp only [assoc, Iso.hom_inv_id_assoc,
    FiniteSemisimpleSkeleton.semisimpleCoendIso_ι_simple_assoc, biproduct.ι_π_self]
  rfl

/-- The corresponding actual projection after the strong tensor-product functor. -/
def projection (i : ι) : algebra S ⟶ dual D (S.simpleObject i) ⊗ S.simpleObject i :=
  (tensorProductFunctor (C := D)).map (capProjection S i) ≫
    (capPairIso (dual D (S.simpleObject i)) (S.simpleObject i)).hom

@[reassoc]
lemma injection_projection_self (i : ι) : injection S (S.simpleObject i) ≫ projection S i = 𝟙 _ := by
  dsimp only [injection, projection]
  rw [assoc, ← Functor.map_comp_assoc, capGenerator_projection_self, CategoryTheory.Functor.map_id,
    id_comp, Iso.inv_hom_id]

omit [BraidedCategory D] in
/-- A nonunit simple diagonal has no maps from the actual Deligne tensor unit. -/
lemma unit_to_nonunit_cap_zero (i : ι) (hi : i ≠ S.unitLabel)
    (f : 𝟙_ (DeligneProduct D D) ⟶
      DeligneProduct.externalObject (dual D (S.simpleObject i)) (S.simpleObject i)) : f = 0 := by
  have hn : (S.unitLabel,S.unitLabel) ≠ (S.dualLabel i,i) := by
    intro h
    exact hi (congrArg Prod.snd h).symm
  have hd : Module.finrank ℂ (𝟙_ (DeligneProduct D D) ⟶
      DeligneProduct.externalObject (dual D (S.simpleObject i)) (S.simpleObject i)) = 0 := by
    rw [finrank_hom_iso (DeligneProduct.unitPairIso S S).symm (capSimplePairIso S i).symm]
    simpa only [if_neg hn] using
      DeligneProduct.finrank_pair_hom S S (S.unitLabel,S.unitLabel) (S.dualLabel i,i)
  letI := (Module.finrank_zero_iff.mp hd)
  exact Subsingleton.elim _ _

/-- The actual algebra unit has zero component on every nonunit simple diagonal. -/
lemma unit_projection_zero (i : ι) (hi : i ≠ S.unitLabel) : η[algebra S] ≫ projection S i = 0 := by
  have hz : η[canonicalAlgebra S] ≫ capProjection S i = 0 := unit_to_nonunit_cap_zero S i hi _
  change (Functor.LaxMonoidal.ε (tensorProductFunctor (C := D)) ≫
      (tensorProductFunctor (C := D)).map η[canonicalAlgebra S]) ≫ _ = _
  dsimp only [projection]
  rw [assoc, ← Functor.map_comp_assoc, hz, Functor.map_zero, zero_comp, comp_zero]

end Paper18.Category.DrinfeldNoPivotal

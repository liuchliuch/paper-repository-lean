import Paper18.Category.ENOPseudounitaryCenterLoops
import Paper18.Category.DrinfeldSemisimple

/-! # Actual simple-diagonal projections for induction-loop traces -/
noncomputable section
universe v u w
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
open Classical
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- The actual finite diagonal of the central-induction coend. -/
def inductionDiagonal (X : C) (i : ι) : C :=
  (S.simpleObject i ⊗ X) ⊗ dual C (S.simpleObject i)

/-- Actual projection to a simple-labelled diagonal summand of induction. -/
def inductionProjection (X : C) (i : ι) : inductionUnderlying S X ⟶ inductionDiagonal S X i :=
  (inductionUnderlyingIso S X).hom ≫ biproduct.π (inductionDiagonal S X) i

@[reassoc (attr := simp)]
lemma inductionι_coendIso (X : C) (i : ι) :
    inductionι S X (S.simpleObject i) ≫ (inductionUnderlyingIso S X).hom =
      biproduct.ι (inductionDiagonal S X) i :=
  S.semisimpleCoendIso_ι_simple (inductionDiagram X) i

@[reassoc (attr := simp)]
lemma inductionCoendIso_inv_ι (X : C) (i : ι) :
    biproduct.ι (inductionDiagonal S X) i ≫ (inductionUnderlyingIso S X).inv =
      inductionι S X (S.simpleObject i) :=
  S.semisimpleCoendIso_inv_ι (inductionDiagram X) i

@[reassoc (attr := simp)]
lemma inductionι_projection_self (X : C) (i : ι) :
    inductionι S X (S.simpleObject i) ≫ inductionProjection S X i = 𝟙 (inductionDiagonal S X i) := by
  simp only [inductionProjection, inductionι_coendIso_assoc, biproduct.ι_π_self]

lemma inductionDiagonalResolution (X : C) :
    (∑ i : ι, inductionProjection S X i ≫ inductionι S X (S.simpleObject i)) =
      𝟙 (inductionUnderlying S X) := by
  have htotal : (∑ i : ι, biproduct.π (inductionDiagonal S X) i ≫
      biproduct.ι (inductionDiagonal S X) i) = 𝟙 (⨁ inductionDiagonal S X) := by
    have h := biproduct_lift_desc_universe (inductionDiagonal S X)
      (biproduct.π (inductionDiagonal S X)) (biproduct.ι (inductionDiagonal S X))
    have hl : biproduct.lift (biproduct.π (inductionDiagonal S X)) = 𝟙 (⨁ inductionDiagonal S X) := by
      apply biproduct.hom_ext
      intro i
      simp only [biproduct.lift_π, id_comp]
    have hr : biproduct.desc (biproduct.ι (inductionDiagonal S X)) = 𝟙 (⨁ inductionDiagonal S X) := by
      apply biproduct.hom_ext'
      intro i
      simp only [biproduct.ι_desc, comp_id]
    rw [hl, hr, id_comp] at h
    exact h.symm
  simp_rw [inductionProjection, ← inductionCoendIso_inv_ι]
  simp only [assoc, ← Preadditive.comp_sum]
  simp_rw [← assoc]
  rw [← Preadditive.sum_comp]
  rw [htotal]
  change (inductionUnderlyingIso S X).hom ≫ (𝟙 _) ≫ (inductionUnderlyingIso S X).inv = _
  simp only [Category.id_comp, Iso.hom_inv_id]

/-- The actual trace of every underlying induction endomorphism is the
sum of its actual diagonal matrix traces. -/
lemma inductionTrace_diagonal (J : PivotalStructure C) (X : C)
    (f : inductionUnderlying S X ⟶ inductionUnderlying S X) :
    J.rightTrace f = ∑ i : ι, J.rightTrace
      (inductionι S X (S.simpleObject i) ≫ f ≫ inductionProjection S X i) :=
  J.rightTrace_of_resolution (inductionDiagonal S X)
    (fun i => inductionι S X (S.simpleObject i)) (inductionProjection S X)
      (inductionDiagonalResolution S X) f

end Paper18.Category.Drinfeld

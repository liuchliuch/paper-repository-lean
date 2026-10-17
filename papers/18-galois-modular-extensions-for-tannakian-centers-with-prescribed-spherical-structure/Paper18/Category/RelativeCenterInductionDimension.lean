import Paper18.Category.RelativeCenterInduction
import Paper18.Category.DrinfeldDimension

/-! # Actual underlying FP dimension of supported relative induction -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.RelativeCenter
open Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)] [BraidedCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {P : ObjectProperty C} [P.IsMonoidal] [IsAdditiveFullProperty P]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

abbrev SupportIndex := {i : ι // P (S.simpleObject i)}
def selectedDiagonal (X : C) (i : SupportIndex (P := P) S) : C :=
  (S.simpleObject i.1 ⊗ X) ⊗ dual C (S.simpleObject i.1)

def selectedToUnderlying (X : C) : (⨁ selectedDiagonal (P := P) S X) ⟶ inductionUnderlying S X :=
  biproduct.desc (fun i => inductionι S X (S.simpleObject i.1))

def underlyingToSelected (X : C) : inductionUnderlying S X ⟶ ⨁ selectedDiagonal (P := P) S X :=
  (inductionUnderlyingIso S X).hom ≫ biproduct.lift (fun i : SupportIndex (P := P) S =>
    biproduct.π (fun j => (S.simpleObject j ⊗ X) ⊗ dual C (S.simpleObject j)) i.1)

@[reassoc]
lemma inductionι_toSelected_of_property (X : C) (i : ι) (hi : P (S.simpleObject i)) :
    inductionι S X (S.simpleObject i) ≫ underlyingToSelected (P := P) S X =
      biproduct.ι (selectedDiagonal (P := P) S X) ⟨i, hi⟩ := by
  apply biproduct.hom_ext
  intro j
  have hc : inductionι S X (S.simpleObject i) ≫ (inductionUnderlyingIso S X).hom =
      biproduct.ι (fun k => (S.simpleObject k ⊗ X) ⊗ dual C (S.simpleObject k)) i :=
    S.semisimpleCoendIso_ι_simple (inductionDiagram X) i
  simp only [underlyingToSelected, assoc, biproduct.lift_π]
  rw [← assoc, hc]
  by_cases hij : i = j.val
  · subst i
    rcases j with ⟨j, hj⟩
    simp only [biproduct.ι_π_self]
    rfl
  · have hj : (⟨i, hi⟩ : SupportIndex (P := P) S) ≠ j :=
      fun h => hij (congrArg Subtype.val h)
    rw [biproduct.ι_π_ne _ hij, biproduct.ι_π_ne _ hj]

@[reassoc]
lemma inductionι_toSelected_outside (X : C) (i : ι) (hi : ¬ P (S.simpleObject i)) :
    inductionι S X (S.simpleObject i) ≫ underlyingToSelected (P := P) S X = 0 := by
  apply biproduct.hom_ext
  intro j
  have hc : inductionι S X (S.simpleObject i) ≫ (inductionUnderlyingIso S X).hom =
      biproduct.ι (fun k => (S.simpleObject k ⊗ X) ⊗ dual C (S.simpleObject k)) i :=
    S.semisimpleCoendIso_ι_simple (inductionDiagram X) i
  simp only [underlyingToSelected, assoc, biproduct.lift_π, zero_comp]
  rw [← assoc, hc]
  exact biproduct.ι_π_ne _ (fun h => hi (h ▸ j.property))

@[simp, reassoc]
lemma selectedToUnderlying_toSelected (X : C) :
    selectedToUnderlying (P := P) S X ≫ underlyingToSelected (P := P) S X = 𝟙 _ := by
  apply biproduct.hom_ext'
  intro i
  rw [← assoc, selectedToUnderlying, biproduct.ι_desc,
    inductionι_toSelected_of_property S X i.val i.property, comp_id]

lemma underlyingToSelected_selectedToUnderlying (X : C) :
    underlyingToSelected (P := P) S X ≫ selectedToUnderlying (P := P) S X = (inductionSupportEnd (P := P) S J X).f := by
  apply induction_hom_ext_simple S
  intro i
  rw [← assoc, inductionι_supportEnd]
  by_cases hi : P (S.simpleObject i)
  · rw [inductionι_toSelected_of_property S X i hi, selectedToUnderlying, biproduct.ι_desc, if_pos hi]
  · rw [inductionι_toSelected_outside S X i hi, zero_comp, if_neg hi]

/-- The actual supported kernel image is isomorphic to the actual finite
sum of precisely the supported coend diagonals. -/
def inductionUnderlyingSelectedIso (X : C) :
    (inductionObject (P := P) S J X).1 ≅ ⨁ selectedDiagonal (P := P) S X where
  hom := (inductionInclusion S J X).f ≫ underlyingToSelected (P := P) S X
  inv := selectedToUnderlying (P := P) S X ≫ (inductionProjection S J X).f
  hom_inv_id := by
    have he : (inductionInclusion (P := P) S J X).f ≫ (inductionSupportEnd (P := P) S J X).f =
        (inductionInclusion S J X).f := congrArg Hom.f (inductionInclusion_supportEnd S J X)
    have hi : (inductionInclusion (P := P) S J X).f ≫ (inductionProjection S J X).f = 𝟙 _ :=
      congrArg Hom.f (inductionInclusion_projection S J X)
    simp only [assoc]
    rw [← assoc (underlyingToSelected (P := P) S X), underlyingToSelected_selectedToUnderlying S J,
      ← assoc, he, hi]
  inv_hom_id := by
    have he : (inductionProjection (P := P) S J X).f ≫ (inductionInclusion S J X).f =
        (inductionSupportEnd (P := P) S J X).f := congrArg Hom.f (inductionProjection_inclusion S J X)
    simp only [assoc]
    rw [← assoc (inductionProjection S J X).f, he,
      ← underlyingToSelected_selectedToUnderlying S J X]
    simp only [← assoc, selectedToUnderlying_toSelected, id_comp]

/-- The relative induction of the actual unit has exactly the intrinsic
positive support dimension of the specified actual fusion subcategory. -/
lemma inductionObject_unit_fpdim :
    S.fpdim (inductionObject (P := P) S J (𝟙_ C)).1 = S.supportFPdim P := by
  rw [S.fpdim_iso (inductionUnderlyingSelectedIso S J (𝟙_ C)), S.fpdim_biproduct]
  simp only [selectedDiagonal, S.fpdim_tensor, S.fpdim_simple, S.fpdim_unit,
    fpdim_simple_rightDual, mul_one]
  change (∑ i : SupportIndex (P := P) S, S.fusionBasis.fpdim i.val * S.fusionBasis.fpdim i.val) = _
  simp only [← pow_two]
  rw [FiniteSemisimpleSkeleton.supportFPdim, ← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter (fun i => P (S.simpleObject i)))
    (fun i => by simp) (fun i => S.fusionBasis.fpdim i ^ 2)).symm

end Paper18.Category.RelativeCenter

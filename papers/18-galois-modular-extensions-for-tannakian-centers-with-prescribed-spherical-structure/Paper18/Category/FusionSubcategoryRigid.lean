import Paper18.Category.FusionSubcategoryBasic
import Paper18.Category.FusionSubcategoryRules
import Paper18.Category.FusionCategory

/-!
# Rigidity inherited by actual tensor full subcategories

Dual closure is derived from finite semisimplicity and tensor/summand closure.
Neither dual closure nor numerical fusion laws are supplied as certificates.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category
namespace FiniteSemisimpleSkeleton
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- Actual Hom multiplicities of a right dual are dual-reindexed
multiplicities of the original object. -/
lemma multiplicity_rightDual (X : C) (i : ι) :
    S.multiplicity (Xᘁ) i = S.multiplicity X (S.dualLabel i) := by
  have e : S.simpleObject i ≅ (S.simpleObject (S.dualLabel i))ᘁ :=
    (eqToIso (congrArg S.simpleObject (S.dualLabel_involutive i).symm)) ≪≫
      S.dualIso (S.dualLabel i)
  calc
    _ = Module.finrank ℂ (Xᘁ ⟶ S.simpleObject i) := S.finrank_hom_comm _ _
    _ = Module.finrank ℂ (Xᘁ ⟶ (S.simpleObject (S.dualLabel i))ᘁ) :=
      finrank_hom_iso (Iso.refl _) e
    _ = _ := finrank_rightDual_hom _ _

variable (P : ObjectProperty C) [IsAdditiveFullProperty P] [P.IsMonoidal]

/-- A tensor-closed summand-closed full subcategory contains the actual
dual of each simple representative that it contains. -/
lemma property_dualLabel (i : ι) (hi : P (S.simpleObject i)) :
    P (S.simpleObject (S.dualLabel i)) := by
  apply S.fusionBasis.dual_closed_of_tensor_closed
    (fun j => P (S.simpleObject j)) ?_ ?_ i hi
  · exact IsAdditiveFullProperty.of_iso P S.unitIso (ObjectProperty.prop_unit P)
  · intro j k l hj hk hn
    have hp : P (S.simpleObject j ⊗ S.simpleObject k) :=
      ObjectProperty.prop_tensor hj hk
    apply IsAdditiveFullProperty.of_retract
      (S.retractOfMultiplicityPos _ l (Nat.pos_of_ne_zero hn)) hp

include S in
/-- Every actual right dual belongs to the tensor full subcategory. -/
lemma property_rightDual {X : C} (hX : P X) : P (Xᘁ) := by
  apply IsAdditiveFullProperty.of_iso P (S.decomposition (Xᘁ))
  apply IsAdditiveFullProperty.biproduct
  intro a
  have hpos : 0 < S.multiplicity (Xᘁ) (S.label (Xᘁ) a) :=
    (S.multiplicity_pos_iff_label _ _).mpr ⟨a, rfl⟩
  rw [S.multiplicity_rightDual] at hpos
  have hp : P (S.simpleObject (S.dualLabel (S.label (Xᘁ) a))) :=
    IsAdditiveFullProperty.of_retract (S.retractOfMultiplicityPos X _ hpos) hX
  simpa only [S.dualLabel_involutive] using S.property_dualLabel P _ hp

/-- Exact pairings are the ambient cups and caps, now in the actual full
subcategory. -/
def fullSubcategoryExactPairing (X : P.FullSubcategory) :
    ExactPairing X (⟨X.objᘁ, S.property_rightDual P X.property⟩ : P.FullSubcategory) where
  coevaluation' := η_ X.obj (X.objᘁ)
  evaluation' := ε_ X.obj (X.objᘁ)
  coevaluation_evaluation' := ExactPairing.coevaluation_evaluation X.obj (X.objᘁ)
  evaluation_coevaluation' := ExactPairing.evaluation_coevaluation X.obj (X.objᘁ)

/-- A genuine inherited right-rigid structure, with no additional existence
or dual closure assumption. -/
def fullSubcategoryRightRigid : RightRigidCategory P.FullSubcategory where
  rightDual X :=
    { rightDual := ⟨X.objᘁ, S.property_rightDual P X.property⟩
      exact := S.fullSubcategoryExactPairing P X }

/-- The tensor unit remains simple in the actual full subcategory. -/
def fullSubcategorySimpleUnit : Simple (𝟙_ P.FullSubcategory) :=
  S.simple_in_fullSubcategory P (𝟙_ C) (ObjectProperty.prop_unit P)

end FiniteSemisimpleSkeleton
end Paper18.Category

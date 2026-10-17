import Paper18.Category.RelativeCenterInductionDimension
import Paper18.Category.RelativeCenterRigid
import Paper18.Category.CentralizerDimensionFunctor

/-! # Intrinsic FP dimension of the actual relative center -/
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

/-- Forgetting relative half-braidings is actually dominant: every ambient
object is the underlying object of its actual positive relative lift. -/
lemma forget_dominant (X : C) : ∃ Z : RelativeCenter P, Nonempty (Retract X ((forget P).obj Z)) :=
  ⟨(restriction P).obj ((positive C).obj X), ⟨Retract.ofIso (Iso.refl X)⟩⟩

/-- The intrinsic total FP dimension of the actual relative center is the
product of the actual subcategory FP dimension and the ambient FP dimension.
No positive pivotal structure or dimension-law certificate is assumed. -/
theorem totalFPdim :
    (letI := rightRigidCategory (P := P) S J
     (skeleton (P := P) S J).fusionBasis.totalFPdim) =
      S.supportFPdim P * S.fusionBasis.totalFPdim := by
  letI := rightRigidCategory (P := P) S J
  let T := skeleton (P := P) S J
  have hm (r : SimpleIndex (P := P) S J) :
      T.multiplicity (inductionObject (P := P) S J (𝟙_ C)) r =
        S.multiplicity (T.simpleObject r).1 S.unitLabel := by
    rw [T.multiplicity_eq_finrank_hom]
    calc
      _ = Module.finrank ℂ ((𝟙_ C) ⟶ (T.simpleObject r).1) :=
        (inductionHomLinearEquiv S J (𝟙_ C) (T.simpleObject r)).finrank_eq
      _ = _ := (finrank_hom_iso S.unitIso (Iso.refl (T.simpleObject r).1)).symm
  have hq : (∑ r, (T.imageCoeff S (forget P) r S.unitLabel : ℝ) * T.fusionBasis.fpdim r) =
      S.supportFPdim P := by
    change (∑ r, (S.multiplicity (T.simpleObject r).1 S.unitLabel : ℝ) * T.fusionBasis.fpdim r) = _
    simp_rw [← hm]
    change T.fpdim (inductionObject (P := P) S J (𝟙_ C)) = _
    rw [← T.fpdim_map S (forget P)]
    exact inductionObject_unit_fpdim S J
  have h := T.dominant_totalFPdim_eq S (forget P) (forget_dominant (P := P))
  rw [hq] at h
  exact h

end Paper18.Category.RelativeCenter

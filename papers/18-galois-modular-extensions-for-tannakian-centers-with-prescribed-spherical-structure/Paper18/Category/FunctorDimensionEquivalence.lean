import Paper18.Category.CentralizerDimensionFunctor
import Paper18.Category.FactorizationFullyFaithfulRotation
import Paper18.Category.FactorizationFullyFaithfulCriterion
import Paper18.Category.FactorizationEssentialSurjectiveBasic

/-! # Actual equivalence from dominance and equal total FP dimensions

Unit multiplicities are forced by the actual dominant-functor dimension
quotient. Rigid Hom rotation then proves actual fullness, rather than
assuming an equivalence or a simple-image certificate.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits CategoryTheory.Functor.Monoidal
open scoped BigOperators
universe v u w v' u' w'
namespace Paper18.Category.FiniteSemisimpleSkeleton
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)] [BraidedCategory D]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Monoidal]
  (hF : ∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X)))
  (heq : S.fusionBasis.totalFPdim = T.fusionBasis.totalFPdim)

include hF heq

/-- Equal total dimensions force the actual unit column to be the unit vector. -/
lemma imageCoeff_unit_of_dominant_dimension_eq (i : ι) :
    S.imageCoeff T F i T.unitLabel = if i = S.unitLabel then 1 else 0 := by
  let f (i : ι) : ℝ := (S.imageCoeff T F i T.unitLabel : ℝ) * S.fusionBasis.fpdim i
  have hsum : ∑ i, f i = 1 := by
    have h := S.dominant_totalFPdim_eq T F hF
    rw [heq] at h
    have hp : 0 < T.fusionBasis.totalFPdim :=
      Finset.sum_pos' (fun j _ => (sq_nonneg (T.fusionBasis.fpdim j)))
        ⟨T.unitLabel, Finset.mem_univ _, sq_pos_of_pos (T.fusionBasis.fpdim_pos _)⟩
    change T.fusionBasis.totalFPdim = (∑ i, f i) * T.fusionBasis.totalFPdim at h
    nlinarith
  have hunit : S.imageCoeff T F S.unitLabel T.unitLabel = 1 := by
    simpa using S.imageCoeff_one T F S.unitLabel T.unitLabel S.unitIso T.unitIso T.unitLabel
  have hu : f S.unitLabel = 1 := by
    dsimp [f]
    rw [hunit]
    simp only [Nat.cast_one, one_mul]
    exact S.fusionBasis.fpdim_one
  by_cases hi : i = S.unitLabel
  · subst i
    simp [hunit]
  · rw [if_neg hi]
    have hzero : ∑ j ∈ Finset.univ.erase S.unitLabel, f j = 0 := by
      have h := Finset.sum_erase_add (Finset.univ (α := ι)) f (Finset.mem_univ S.unitLabel)
      rw [hu, hsum] at h
      linarith
    have hnonneg (j : ι) : 0 ≤ f j :=
      mul_nonneg (Nat.cast_nonneg _) (S.fusionBasis.fpdim_pos j).le
    have hz : f i = 0 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => hnonneg j)).mp hzero i (by simp [hi])
    have hc : (S.imageCoeff T F i T.unitLabel : ℝ) = 0 :=
      (mul_eq_zero.mp hz).resolve_right (ne_of_gt (S.fusionBasis.fpdim_pos i))
    exact_mod_cast hc

/-- The unit multiplicity of every actual object is preserved. -/
lemma multiplicity_unit_of_dominant_dimension_eq (X : C) :
    T.multiplicity (F.obj X) T.unitLabel = S.multiplicity X S.unitLabel := by
  rw [S.multiplicity_map T F X]
  change (∑ i, S.multiplicity X i * S.imageCoeff T F i T.unitLabel) = _
  simp_rw [S.imageCoeff_unit_of_dominant_dimension_eq T F hF heq]
  simp

/-- Rigid rotation converts the actual unit-column assertion into all Hom dimensions. -/
lemma finrank_hom_of_dominant_dimension_eq (X Y : C) :
    Module.finrank ℂ (F.obj X ⟶ F.obj Y) = Module.finrank ℂ (X ⟶ Y) := by
  have h := S.multiplicity_unit_of_dominant_dimension_eq T F hF heq (dual C Y ⊗ X)
  let e : F.obj (dual C Y ⊗ X) ≅ dual D (F.obj Y) ⊗ F.obj X :=
    (μIso F (dual C Y) X).symm ≪≫ ((dualComparison F Y) ⊗ᵢ Iso.refl _)
  rw [T.multiplicity_iso e,
    Drinfeld.multiplicity_unit_dual_tensor T,
    Drinfeld.multiplicity_unit_dual_tensor S] at h
  exact h

/-- Actual full faithfulness follows from the proved Hom dimensions and
actual simple decompositions. -/
def fullyFaithfulOfDominantDimensionEq : F.FullyFaithful :=
  S.fullyFaithfulOfSimpleHomDimensions F (fun i j => by
    rw [S.finrank_hom_of_dominant_dimension_eq T F hF heq]
    exact S.finrank_simple_hom_simple i j)

/-- A dominant actual tensor functor with equal total FP dimensions is an
actual equivalence. No prior fullness or faithfulness is needed. -/
def isEquivalenceOfDominantDimensionEq : F.IsEquivalence := by
  let ff := S.fullyFaithfulOfDominantDimensionEq T F hF heq
  letI := ff.full
  letI := ff.faithful
  exact S.isEquivalenceOfTotalFPdimEq T F heq

end Paper18.Category.FiniteSemisimpleSkeleton

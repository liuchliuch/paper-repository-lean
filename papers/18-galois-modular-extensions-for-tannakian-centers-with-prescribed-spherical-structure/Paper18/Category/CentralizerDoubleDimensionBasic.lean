import Paper18.Category.CentralizerDimensionBasic
import Paper18.Category.HopfLinkNondegenerateVerlinde

/-! # Actual fusion support in the reciprocal averaging resolution -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [BraidedCategory C]
  {ι : Type w} [Fintype ι]
namespace FiniteSemisimpleSkeleton
open Drinfeld
variable (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)
  (P : ObjectProperty C) [IsAdditiveFullProperty P] [P.IsMonoidal]

include J in
/-- An actual occurrence in the tensor resolution preserves membership in
an actual fusion full subcategory when its moving object lies there. -/
lemma averagingSlots_property_iff {U : C} (hU : P U) (i j : ι)
    (a : averagingSlots S U i j) : P (S.simpleObject i) ↔ P (S.simpleObject j) := by
  constructor
  · intro hi
    have hm : 0 < S.multiplicity (dual C U ⊗ S.simpleObject i) j := by
      rw [← averagingSlots_card S J U i j]
      exact Fintype.card_pos_iff.mpr ⟨a⟩
    exact IsAdditiveFullProperty.of_retract (S.retractOfMultiplicityPos _ j hm)
      (ObjectProperty.prop_tensor (S.property_rightDual P hU) hi)
  · intro hj
    have hp : P (S.simpleObject (S.label (U ⊗ S.simpleObject j) a.1)) :=
      S.property_label P ⟨U ⊗ S.simpleObject j, ObjectProperty.prop_tensor hU hj⟩ a.1
    simpa only [a.2] using hp

/-- The actual squared-dimension support of a full object property. -/
def supportGlobalDimension (Q : ObjectProperty C) : ℂ :=
  ∑ i, if Q (S.simpleObject i) then (J.pivotalData S).ndim i else 0

lemma supportGlobalDimension_eq (Q : ObjectProperty C) :
    S.supportGlobalDimension J Q = ∑ i, if Q (S.simpleObject i) then
      J.rightDim (S.simpleObject (S.dualLabel i)) * J.rightDim (S.simpleObject i) else 0 := by
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · exact mul_comm _ _
  · rfl

lemma supportGlobalDimension_re_pos : 0 < (S.supportGlobalDimension J P).re := by
  change 0 < Complex.reAddGroupHom (∑ i, if P (S.simpleObject i) then (J.pivotalData S).ndim i else 0)
  rw [map_sum]
  apply Finset.sum_pos'
  · intro i _
    split_ifs
    · exact ((J.pivotalData S).ndim_re_pos i).le
    · simp
  · refine ⟨S.unitLabel, Finset.mem_univ _, ?_⟩
    rw [if_pos (IsAdditiveFullProperty.of_iso P S.unitIso (ObjectProperty.prop_unit P))]
    exact (J.pivotalData S).ndim_re_pos _

lemma supportGlobalDimension_ne_zero : S.supportGlobalDimension J P ≠ 0 := by
  intro h
  have hp := S.supportGlobalDimension_re_pos J P
  rw [h] at hp
  simp at hp

/-- Positive actual squared dimensions detect equality of additive full
properties under inclusion, without positivity of the pivotal dimensions. -/
lemma supportGlobalDimension_eq_iff_of_le (Q R : ObjectProperty C)
    [IsAdditiveFullProperty Q] [IsAdditiveFullProperty R] (h : ∀ X, Q X → R X) :
    S.supportGlobalDimension J Q = S.supportGlobalDimension J R ↔ Q = R := by
  constructor
  · intro hd
    have hs (i : ι) : Q (S.simpleObject i) ↔ R (S.simpleObject i) := by
      refine ⟨h _, fun hr => ?_⟩
      by_contra hq
      have hlt : (S.supportGlobalDimension J Q).re < (S.supportGlobalDimension J R).re := by
        change Complex.reAddGroupHom (∑ j, if Q (S.simpleObject j) then (J.pivotalData S).ndim j else 0) <
          Complex.reAddGroupHom (∑ j, if R (S.simpleObject j) then (J.pivotalData S).ndim j else 0)
        rw [map_sum, map_sum]
        apply Finset.sum_lt_sum
        · intro j _
          by_cases hqj : Q (S.simpleObject j)
          · simp only [if_pos hqj, if_pos (h _ hqj)]
            exact le_rfl
          · simp only [if_neg hqj, map_zero]
            split_ifs
            · exact ((J.pivotalData S).ndim_re_pos j).le
            · simp
        · refine ⟨i, Finset.mem_univ _, ?_⟩
          simp only [if_neg hq, if_pos hr, map_zero]
          exact (J.pivotalData S).ndim_re_pos i
      exact (ne_of_lt hlt) (congrArg Complex.re hd)
    funext X
    apply propext
    rw [S.property_iff_labels Q X, S.property_iff_labels R X]
    exact forall_congr' (fun a => hs (S.label X a))
  · rintro rfl
    rfl

end FiniteSemisimpleSkeleton
end Paper18.Category

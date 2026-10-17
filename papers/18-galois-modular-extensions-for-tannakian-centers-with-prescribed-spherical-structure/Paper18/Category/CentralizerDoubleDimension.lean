import Paper18.Category.CentralizerDoubleDimensionProjector

/-! # Actual categorical centralizer dimensions and the double-centralizer theorem -/
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
namespace PivotalStructure
variable (J : PivotalStructure C) (S : FiniteSemisimpleSkeleton C ι)

/-- The actual restricted Hopf column detects precisely the actual centralizer. -/
lemma hopfLink_restricted_column (P : ObjectProperty C)
    [IsAdditiveFullProperty P] [P.IsMonoidal] (k : ι) :
    (∑ i, if P (S.simpleObject i) then J.rightDim (S.simpleObject (S.dualLabel i)) *
      J.hopfLink (S.simpleObject i) (S.simpleObject k) else 0) =
    S.supportGlobalDimension J P *
      if S.simpleObject k ∈ centralizer (P : Set C) then J.rightDim (S.simpleObject k) else 0 := by
  let tr : (S.simpleObject k ⟶ S.simpleObject k) →ₗ[ℂ] ℂ :=
    (unitScalarEquiv (C := C)).toLinearMap.comp (J.rightTraceLinearMap (S.simpleObject k))
  have ht := congrArg tr (J.restrictedHopfProjector_loops S P (S.simpleObject k))
  simp only [map_sum, apply_ite, map_smul, map_zero, smul_eq_mul] at ht
  have hl (i : ι) : tr (J.hopfLoop (S.simpleObject k) (S.simpleObject i)) =
      J.hopfLink (S.simpleObject i) (S.simpleObject k) := by
    change unitScalarEquiv (J.rightTrace (J.hopfLoop (S.simpleObject k) (S.simpleObject i))) = _
    rw [J.rightTrace_hopfLoop]
    exact J.hopfLink_symm _ _
  simp_rw [hl] at ht
  rw [← ht]
  change unitScalarEquiv (J.rightTrace (J.restrictedHopfProjector S P (S.simpleObject k))) = _
  rw [J.restrictedHopfProjector_simple S P, J.rightTrace_smul, map_smul, smul_eq_mul]
  congr 1
  rw [S.supportProjector_simple]
  change unitScalarEquiv (J.rightTrace (if S.simpleObject k ∈ centralizer (P : Set C)
    then 𝟙 (S.simpleObject k) else 0)) = _
  by_cases hk : S.simpleObject k ∈ centralizer (P : Set C)
  · simp only [if_pos hk]
    rfl
  · simp only [if_neg hk, J.rightTrace_zero, map_zero]

end PivotalStructure
namespace FiniteSemisimpleSkeleton
variable (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

/-- Actual centralizer global dimensions multiply to the ambient global
dimension under genuine Müger nondegeneracy, for an arbitrary pivotal structure. -/
lemma supportGlobalDimension_mul_centralizer (hC : IsNondegenerate (C := C))
    (P : ObjectProperty C) [IsAdditiveFullProperty P] [P.IsMonoidal] :
    S.supportGlobalDimension J P *
      S.supportGlobalDimension J (centralizerProperty (P : Set C)) =
        (J.pivotalData S).globalDimension := by
  have hu : P (S.simpleObject S.unitLabel) :=
    IsAdditiveFullProperty.of_iso P S.unitIso (ObjectProperty.prop_unit P)
  have hd : J.rightDim (S.simpleObject (S.dualLabel S.unitLabel)) = 1 := by
    rw [S.dualLabel_unit, J.rightDim_iso S.unitIso, J.rightDim_unit S]
  calc
    _ = ∑ k, J.rightDim (S.simpleObject (S.dualLabel k)) *
        (S.supportGlobalDimension J P *
          if S.simpleObject k ∈ centralizer (P : Set C) then J.rightDim (S.simpleObject k) else 0) := by
      rw [S.supportGlobalDimension_eq J (centralizerProperty (P : Set C))]
      simp only [Finset.mul_sum, centralizerProperty]
      apply Finset.sum_congr rfl
      intro k _
      change S.supportGlobalDimension J P *
        (if S.simpleObject k ∈ centralizer (P : Set C) then
          J.rightDim (S.simpleObject (S.dualLabel k)) * J.rightDim (S.simpleObject k) else 0) = _
      by_cases hk : S.simpleObject k ∈ centralizer (P : Set C)
      · simp only [if_pos hk]
        ring
      · simp only [if_neg hk]
        ring
    _ = ∑ k, J.rightDim (S.simpleObject (S.dualLabel k)) *
        (∑ i, if P (S.simpleObject i) then J.rightDim (S.simpleObject (S.dualLabel i)) *
          J.hopfLink (S.simpleObject i) (S.simpleObject k) else 0) := by
      simp_rw [J.hopfLink_restricted_column S P]
    _ = ∑ i, if P (S.simpleObject i) then J.rightDim (S.simpleObject (S.dualLabel i)) *
        (∑ k, J.rightDim (S.simpleObject (S.dualLabel k)) *
          J.hopfLink (S.simpleObject k) (S.simpleObject i)) else 0 := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : P (S.simpleObject i)
      · simp only [if_pos hi]
        apply Finset.sum_congr rfl
        intro k _
        rw [J.hopfLink_symm (S.simpleObject i)]
        ring
      · simp only [if_neg hi, mul_zero, Finset.sum_const_zero]
    _ = ∑ i, if P (S.simpleObject i) then J.rightDim (S.simpleObject (S.dualLabel i)) *
        ((J.pivotalData S).globalDimension * (S.multiplicity (S.simpleObject i) S.unitLabel : ℂ)) else 0 := by
      simp_rw [J.hopfLink_weighted_unit_column S hC]
    _ = _ := by
      simp only [S.multiplicity_simple, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      have he (i : ι) : (if P (S.simpleObject i) then J.rightDim (S.simpleObject (S.dualLabel i)) *
          ((J.pivotalData S).globalDimension * if S.unitLabel = i then 1 else 0) else 0) =
          if i = S.unitLabel then (J.pivotalData S).globalDimension else 0 := by
        by_cases hi : i = S.unitLabel
        · subst i
          simp [hu, hd]
        · simp [hi, Ne.symm hi]
      simp_rw [he]
      simp

include S J in
/-- The actual double centralizer of an actual additive tensor full
subcategory in a Müger nondegenerate braided pivotal fusion category is itself. -/
lemma double_centralizer_eq (hC : IsNondegenerate (C := C))
    (P : ObjectProperty C) [IsAdditiveFullProperty P] [P.IsMonoidal] :
    centralizer (centralizer (P : Set C)) = (P : Set C) := by
  let Q : ObjectProperty C := centralizerProperty (P : Set C)
  let R : ObjectProperty C := centralizerProperty (Q : Set C)
  have h1 := S.supportGlobalDimension_mul_centralizer J hC P
  have h2 := S.supportGlobalDimension_mul_centralizer J hC Q
  have hn := S.supportGlobalDimension_ne_zero J Q
  have he : S.supportGlobalDimension J P = S.supportGlobalDimension J R := by
    apply mul_right_cancel₀ hn
    change S.supportGlobalDimension J P * S.supportGlobalDimension J Q =
      S.supportGlobalDimension J R * S.supportGlobalDimension J Q
    rw [mul_comm (S.supportGlobalDimension J R)]
    exact h1.trans h2.symm
  have hi : ∀ X, P X → R X := fun X hX => subset_double_centralizer (P : Set C) hX
  have hp := (S.supportGlobalDimension_eq_iff_of_le J P R hi).mp he
  exact hp.symm

end FiniteSemisimpleSkeleton
end Paper18.Category

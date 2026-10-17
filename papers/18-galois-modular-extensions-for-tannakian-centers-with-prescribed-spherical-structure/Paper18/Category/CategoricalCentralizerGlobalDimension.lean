import Paper18.Category.CentralizerDoubleDimension

/-! # Global dimensions of centralizers without nondegeneracy

The full weighted Hopf column is the actual transparent support projector.
Pairing it with a restricted column gives the general centralizer product
formula, including the intersection with the actual Müger center.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)] [BraidedCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι]
namespace PivotalStructure
variable (J : PivotalStructure C) (S : FiniteSemisimpleSkeleton C ι)

lemma hopfLink_weighted_muger_column (k : ι) :
    (∑ i, J.rightDim (S.simpleObject (S.dualLabel i)) *
      J.hopfLink (S.simpleObject i) (S.simpleObject k)) =
    (J.pivotalData S).globalDimension *
      if S.simpleObject k ∈ mugerCenter then J.rightDim (S.simpleObject k) else 0 := by
  let P : ObjectProperty C := fun _ => True
  letI : IsAdditiveFullProperty P := { of_retract := fun _ _ => trivial, biproduct := fun _ _ => trivial }
  letI : P.IsMonoidal := { prop_unit := trivial, prop_tensor := fun _ _ _ _ => trivial }
  simpa only [FiniteSemisimpleSkeleton.supportGlobalDimension, P, if_true,
    Paper18.PivotalData.globalDimension] using J.hopfLink_restricted_column S P k

end PivotalStructure
namespace FiniteSemisimpleSkeleton
variable (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

/-- The actual categorical centralizer dimension formula in a general
braided pivotal fusion category. No ambient nondegeneracy is assumed. -/
theorem supportGlobalDimension_mul_centralizer_general
    (P : ObjectProperty C) [IsAdditiveFullProperty P] [P.IsMonoidal] :
    S.supportGlobalDimension J P *
      S.supportGlobalDimension J (centralizerProperty (P : Set C)) =
        (J.pivotalData S).globalDimension *
          S.supportGlobalDimension J (fun X => P X ∧ X ∈ mugerCenter) := by
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
        ((J.pivotalData S).globalDimension *
          if S.simpleObject i ∈ mugerCenter then J.rightDim (S.simpleObject i) else 0) else 0 := by
      simp_rw [J.hopfLink_weighted_muger_column S]
    _ = _ := by
      rw [S.supportGlobalDimension_eq J]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : P (S.simpleObject i) <;>
        by_cases hz : S.simpleObject i ∈ mugerCenter <;> simp [hi, hz] <;> ring

end FiniteSemisimpleSkeleton
end Paper18.Category

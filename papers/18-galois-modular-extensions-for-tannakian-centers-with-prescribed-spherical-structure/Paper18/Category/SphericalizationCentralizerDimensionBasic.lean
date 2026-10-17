import Paper18.Category.EquivariantFPdim
import Paper18.Category.CentralizerDimensionBasic

/-! # Actual support dimensions under finite categorical equivariantization

Stability under the actual action is an object property. Multiplicity
support is derived using actual induction and actual retracts; the weighted
dimension identity is then proved from the actual induction Hom equivalence.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w t
namespace Paper18.Category.WeakAction
attribute [local instance 2000] RightRigidCategory.rightDual
variable {G : Type} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  (A : WeakAction G C)
  [∀ g : G, (A.ρ g).Additive] [∀ g : G, (A.ρ g).Linear ℂ]
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  {ι : Type t} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (P : ObjectProperty C) [IsAdditiveFullProperty P]
  (hstable : ∀ g X, P X → P ((A.ρ g).obj X))

include hstable in
lemma induction_property (X : C) (hX : P X) : P (A.induction X).obj := by
  change P (⨁ fun g : G => (A.ρ g).obj X)
  apply IsAdditiveFullProperty.biproduct
  intro g
  exact hstable _ X hX

include hstable in
/-- A constituent of the underlying object of an equivariant simple has
the property exactly when the entire underlying simple has it. The reverse
direction follows by retracting from the actual induction object. -/
lemma underlying_property_iff_of_multiplicity_pos (q : A.SimpleIndex S) (i : ι)
    (hn : 0 < S.multiplicity ((A.equivariantSkeleton S).simpleObject q).obj i) :
    P (S.simpleObject i) ↔ P ((A.equivariantSkeleton S).simpleObject q).obj := by
  constructor
  · intro hi
    have hq : 0 < (A.equivariantSkeleton S).multiplicity (A.induction (S.simpleObject i)) q := by
      rw [A.induction_multiplicity]
      exact hn
    exact IsAdditiveFullProperty.of_retract
      (((A.equivariantSkeleton S).retractOfMultiplicityPos _ q hq).map A.forget)
      (A.induction_property P hstable (S.simpleObject i) hi)
  · exact IsAdditiveFullProperty.of_retract (S.retractOfMultiplicityPos _ i hn)

include hstable in
/-- Actual stable support FP dimension is multiplied by the group order.
The proof uses actual induction and preservation of actual FP dimensions,
with no orbit/stabilizer or simple-image dimension law supplied as data. -/
theorem equivariant_supportFPdim :
    (A.equivariantSkeleton S).supportFPdim (fun X => P X.obj) =
      (Fintype.card G : ℝ) * S.supportFPdim P := by
  let T := A.equivariantSkeleton S
  let m (q : A.SimpleIndex S) (i : ι) := S.multiplicity (T.simpleObject q).obj i
  let p (i : ι) : ℝ := if P (S.simpleObject i) then 1 else 0
  let r (q : A.SimpleIndex S) : ℝ := if P (T.simpleObject q).obj then 1 else 0
  have ht (q : A.SimpleIndex S) (i : ι) : r q * (m q i : ℝ) = p i * (m q i : ℝ) := by
    by_cases hm : m q i = 0
    · simp [hm]
    have he := A.underlying_property_iff_of_multiplicity_pos S P hstable q i
      (Nat.pos_of_ne_zero hm)
    by_cases hi : P (S.simpleObject i)
    · have hq : P (T.simpleObject q).obj := he.mp hi
      simp [p, r, hi, hq]
    · have hq : ¬ P (T.simpleObject q).obj := fun h => hi (he.mpr h)
      simp [p, r, hi, hq]
  have hq (q : A.SimpleIndex S) :
      (∑ i, (m q i : ℝ) * S.fusionBasis.fpdim i) = T.fusionBasis.fpdim q := by
    have h := T.fpdim_map_simple S A.forget q
    rw [T.fpdim_simple] at h
    exact h
  have hi (i : ι) :
      (∑ q, (m q i : ℝ) * T.fusionBasis.fpdim q) =
        (Fintype.card G : ℝ) * S.fusionBasis.fpdim i := A.induction_fpdim_sum S i
  calc
    T.supportFPdim (fun X => P X.obj) =
        ∑ q, r q * T.fusionBasis.fpdim q *
          (∑ i, (m q i : ℝ) * S.fusionBasis.fpdim i) := by
      simp_rw [hq]
      unfold FiniteSemisimpleSkeleton.supportFPdim
      apply Finset.sum_congr rfl
      intro q _
      dsimp only [r]
      split_ifs <;> simp [pow_two]
    _ = ∑ i, (∑ q, r q * (m q i : ℝ) * T.fusionBasis.fpdim q) * S.fusionBasis.fpdim i := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = ∑ i, p i * (∑ q, (m q i : ℝ) * T.fusionBasis.fpdim q) * S.fusionBasis.fpdim i := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [ht]
      ring
    _ = (Fintype.card G : ℝ) * ∑ i, p i * S.fusionBasis.fpdim i ^ 2 := by
      simp_rw [hi]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      congr 1
      unfold FiniteSemisimpleSkeleton.supportFPdim
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [p]
      split_ifs <;> simp

end Paper18.Category.WeakAction

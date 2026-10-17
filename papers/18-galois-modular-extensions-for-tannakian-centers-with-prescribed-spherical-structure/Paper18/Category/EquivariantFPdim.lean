import Paper18.Category.EquivariantFPdimBasic
import Paper18.Category.EquivariantIntegrality

/-! # Total Frobenius--Perron dimension of the actual equivariantization

The proof uses the genuine induction Hom equivalence and actual preservation
of FP dimension by tensor functors. No orbit formula is a hypothesis.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators
universe v u w t
namespace Paper18.Category.WeakAction
attribute [local instance 2000] RightRigidCategory.rightDual
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  (A : WeakAction G C)
  [∀ g : G, (A.ρ g).Additive] [∀ g : G, (A.ρ g).Linear ℂ]
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  {ι : Type t} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

theorem induction_fpdim (X : C) :
    (A.equivariantSkeleton S).fpdim (A.induction X) =
      (Fintype.card G : ℝ) * S.fpdim X := by
  rw [← (A.equivariantSkeleton S).fpdim_map S A.forget]
  change S.fpdim (⨁ fun g : G => (A.ρ g).obj X) = _
  rw [S.fpdim_biproduct]
  simp_rw [S.fpdim_map S]
  simp

theorem induction_multiplicity (i : ι) (q : A.SimpleIndex S) :
    (A.equivariantSkeleton S).multiplicity (A.induction (S.simpleObject i)) q =
      S.multiplicity ((A.equivariantSkeleton S).simpleObject q).obj i := by
  rw [(A.equivariantSkeleton S).multiplicity_eq_finrank_hom]
  exact A.finrank_induction_hom _ _

theorem induction_fpdim_sum (i : ι) :
    (∑ q : A.SimpleIndex S,
      (S.multiplicity ((A.equivariantSkeleton S).simpleObject q).obj i : ℝ) *
        (A.equivariantSkeleton S).fusionBasis.fpdim q) =
      (Fintype.card G : ℝ) * S.fusionBasis.fpdim i := by
  have h := A.induction_fpdim S (S.simpleObject i)
  rw [S.fpdim_simple] at h
  simpa only [FiniteSemisimpleSkeleton.fpdim, A.induction_multiplicity S,
    ] using h

theorem totalFPdim_equivariant :
    (A.equivariantSkeleton S).fusionBasis.totalFPdim =
      (Fintype.card G : ℝ) * S.fusionBasis.totalFPdim := by
  let T := A.equivariantSkeleton S
  have hU (q : A.SimpleIndex S) :
      (∑ i : ι, (S.multiplicity (T.simpleObject q).obj i : ℝ) *
        S.fusionBasis.fpdim i) = T.fusionBasis.fpdim q := by
    have h := T.fpdim_map_simple S A.forget q
    rw [T.fpdim_simple] at h
    exact h
  calc
    T.fusionBasis.totalFPdim =
        ∑ q : A.SimpleIndex S, T.fusionBasis.fpdim q *
          (∑ i : ι, (S.multiplicity (T.simpleObject q).obj i : ℝ) *
            S.fusionBasis.fpdim i) := by
      simp_rw [hU]
      simp only [Paper18.FusionBasis.totalFPdim, pow_two]
    _ = ∑ i : ι, (∑ q : A.SimpleIndex S,
        (S.multiplicity (T.simpleObject q).obj i : ℝ) * T.fusionBasis.fpdim q) *
          S.fusionBasis.fpdim i := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro q _
      ring
    _ = (Fintype.card G : ℝ) * S.fusionBasis.totalFPdim := by
      dsimp only [T]
      simp_rw [A.induction_fpdim_sum S]
      simp only [Paper18.FusionBasis.totalFPdim, Finset.mul_sum, pow_two, mul_assoc]

end Paper18.Category.WeakAction

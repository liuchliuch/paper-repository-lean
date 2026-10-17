import Paper18.Category.FixedBoundaryOddModule
import Paper18.Category.TensorCharacters

/-!
# Actual connectivity of a homogeneous component under neutral tensoring

Frobenius reciprocity and the actual positive FP character produce a
neutral simple object whose tensor product connects any two actual simple
objects in the same component. The resulting positive fusion coefficient
is the dimension of a genuine Hom space.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]

theorem homogeneous_simple_scalar {d : ZMod 2} (i : ι)
    (hi : Homogeneous χ d (S.simpleObject i)) :
    TensorAutomorphism.scalar χ (S.simpleObject i) = paritySign d := by
  unfold TensorAutomorphism.scalar
  rw [hi, simpleScalarEquiv_smul_id]

/-- Every two actual simple objects of one homogeneous degree are
connected by tensoring on the left with an actual neutral simple object. -/
theorem neutral_tensor_connects {d : ZMod 2} (i j : ι)
    (hi : Homogeneous χ d (S.simpleObject i))
    (hj : Homogeneous χ d (S.simpleObject j)) :
    ∃ k : ι, Homogeneous χ 0 (S.simpleObject k) ∧ 0 < S.fusionCoeff k i j := by
  let B := S.fusionBasis
  have hp : 0 < B.fpdim j * B.fpdim (S.dualLabel i) :=
    mul_pos (B.fpdim_pos j) (B.fpdim_pos _)
  rw [← B.fpdim_mul j (S.dualLabel i)] at hp
  have hex : ∃ k : ι, 0 < (B.N j (S.dualLabel i) k : ℝ) * B.fpdim k := by
    by_contra h
    push_neg at h
    have hz : (∑ k : ι, (B.N j (S.dualLabel i) k : ℝ) * B.fpdim k) ≤ 0 :=
      Finset.sum_nonpos fun k _ => h k
    exact (not_lt_of_ge hz) hp
  obtain ⟨k, hk⟩ := hex
  have hn : 0 < S.fusionCoeff j (S.dualLabel i) k := by
    have hr : 0 < (B.N j (S.dualLabel i) k : ℝ) :=
      (mul_pos_iff_of_pos_right (B.fpdim_pos k)).mp hk
    exact_mod_cast hr
  have hi' := homogeneous_simple_scalar S χ i hi
  have hj' := homogeneous_simple_scalar S χ j hj
  have hdual := TensorAutomorphism.scalar_dualLabel χ S i
  have hscalar := TensorAutomorphism.scalar_fusion χ S j (S.dualLabel i) k hn
  rw [hj', hdual, hi'] at hscalar
  have hs : TensorAutomorphism.scalar χ (S.simpleObject k) = 1 := by
    rcases Paper18.ZMod.two_eq_zero_or_one d with rfl | rfl <;>
      simpa [paritySign] using hscalar
  refine ⟨k, ?_, ?_⟩
  · change χ.hom.app (S.simpleObject k) = (1 : ℂ) • 𝟙 _
    rw [← TensorAutomorphism.scalar_spec χ (S.simpleObject k), hs]
  · have hf := S.fusionCoeff_right j (S.dualLabel i) k
    rw [S.dualLabel_involutive] at hf
    exact hf ▸ hn

end Paper18.Category.FixedBoundary

import Paper18.Category.HopfLinkMultiplicative

/-! # Actual simple decomposition of Hopf-link rows -/
noncomputable section
open Classical
open scoped BigOperators
universe v u w
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [BraidedCategory C] [Preadditive C] [Linear ℂ C] [HasKernels C]
  [HasFiniteBiproducts C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι]
namespace PivotalStructure
variable (J : PivotalStructure C) (S : FiniteSemisimpleSkeleton C ι)

/-- Actual simple decompositions in the moving strand give additivity of
the actual Hopf-link row. -/
lemma hopfLink_eq_sum_multiplicity_right (A X : C) :
    J.hopfLink A X =
      ∑ i, (S.multiplicity X i : ℂ) * J.hopfLink A (S.simpleObject i) := by
  let Y := fun a : Fin (S.length X) => S.simpleObject (S.label X a)
  let e := S.decomposition X
  let ii := fun a => biproduct.ι Y a ≫ e.inv
  let pp := fun a => e.hom ≫ biproduct.π Y a
  have hr : ∑ a, pp a ≫ ii a = 𝟙 X := by
    dsimp only [ii, pp]
    simp only [assoc, ← Preadditive.comp_sum]
    simp_rw [← assoc]
    rw [← Preadditive.sum_comp, biproduct.total, id_comp]
    exact e.hom_inv_id
  have hpi (a : Fin (S.length X)) : ii a ≫ pp a = 𝟙 (Y a) := by
    simp [ii, pp, assoc]
  have ht : ∑ a, (A ◁ pp a) ≫ (A ◁ ii a) = 𝟙 (A ⊗ X) := by
    simp only [← whiskerLeft_comp]
    change (∑ a, (tensorLeft A).map (pp a ≫ ii a)) = 𝟙 (A ⊗ X)
    rw [← Functor.map_sum, hr, CategoryTheory.Functor.map_id]
    rfl
  calc
    _ = ∑ a : Fin (S.length X), J.hopfLink A (Y a) := by
      unfold hopfLink
      rw [J.rightTrace_of_resolution (fun a => A ⊗ Y a)
        (fun a => A ◁ ii a) (fun a => A ◁ pp a) ht, map_sum]
      apply Finset.sum_congr rfl
      intro a _
      have hn := doubleBraiding_naturality (𝟙 A) (ii a)
      simp only [id_tensorHom] at hn
      rw [reassoc_of% hn, ← whiskerLeft_comp, hpi, whiskerLeft_id, comp_id]
    _ = _ := by
      symm
      simp_rw [S.multiplicity_eq_sum, Nat.cast_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      simp [Y]

/-- The actual row satisfies the fusion character equation, with its
nonzero retained-object dimension displayed as the normalization. -/
theorem hopfLink_fusion_character (A : C) [Simple A] (i j : ι) :
    (∑ k, (S.fusionCoeff i j k : ℂ) * J.hopfLink A (S.simpleObject k)) =
      J.hopfLink A (S.simpleObject i) * J.hopfLink A (S.simpleObject j) / J.rightDim A := by
  rw [← J.hopfLink_tensor S]
  exact (J.hopfLink_eq_sum_multiplicity_right S A _).symm

end PivotalStructure
end Paper18.Category

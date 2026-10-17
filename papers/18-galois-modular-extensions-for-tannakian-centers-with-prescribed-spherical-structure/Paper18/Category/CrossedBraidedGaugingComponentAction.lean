import Paper18.Category.CrossedBraidedGaugingComponentGrading
import Paper18.Category.CrossedBraidedGaugingBasic

/-! # Actual permutation of components gives actual projector equivariance -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w t
namespace Paper18.Category.CrossedBraidedGauging.ComponentProperties
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C]
  {ι : Type t} [Fintype ι] {S : FiniteSemisimpleSkeleton C ι}
  (T : ComponentProperties (G := G) S)
  (A : WeakAction G C) [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  [∀ g : G, (A.ρ g).Additive]

/-- An actual component-permuting weak monoidal action conjugates the
constructed actual degree projectors. No projector equation is assumed. -/
def gradedAction
    (hm : ∀ (a h : G) (X : C), T.property h X →
      T.property (a * h * a⁻¹) ((A.ρ a).obj X)) : GradedAction T.grading A where
  map_projection a g X := by
    change (A.ρ a).map ((T.projection g).app X) =
      (T.projection (a * g * a⁻¹)).app ((A.ρ a).obj X)
    apply S.coend_map_hom_ext (A.ρ a) X
    intro b
    rw [← (A.ρ a).map_comp, T.projection_naturality, Functor.map_comp,
      T.projection_simple, T.projection_naturality]
    rw [T.projection_of_property (a * g * a⁻¹)
      (a * T.degree (S.label X b) * a⁻¹) _
        (hm a _ _ (T.degree_property (S.label X b)))]
    by_cases hg : g = T.degree (S.label X b)
    · subst g
      simp only [if_pos rfl, if_true, Functor.map_id, Category.id_comp]
      exact congrArg (fun z => z ≫ (A.ρ a).map (S.coendInclusion X b))
        ((A.ρ a).map_id (S.simpleObject (S.label X b)))
    · have hc : a * g * a⁻¹ ≠ a * T.degree (S.label X b) * a⁻¹ := by
        intro h
        apply hg
        exact mul_left_cancel (mul_right_cancel h)
      simp only [if_neg hg, if_neg hc, Functor.map_zero, zero_comp]

/-- Actual nonzero objects in every original component prove
faithfulness of the constructed actual grading. -/
theorem grading_faithful
    (hf : ∀ g : G, ∃ X : C, T.property g X ∧ ¬ IsZero X) : T.grading.Faithful := by
  intro g
  obtain ⟨X, hX, hnX⟩ := hf g
  exact ⟨X, (T.grading_homogeneous_iff g X).mpr hX, hnX⟩

end Paper18.Category.CrossedBraidedGauging.ComponentProperties

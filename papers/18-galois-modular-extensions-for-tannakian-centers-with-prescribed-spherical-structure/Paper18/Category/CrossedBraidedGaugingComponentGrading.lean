import Paper18.Category.CrossedBraidedGaugingComponentProperties

/-! # Actual tensor closure constructs the actual tensor grading equation -/
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

theorem tensor_projection_naturality (g h : G) {X X' Y Y' : C}
    (f : X ⟶ X') (q : Y ⟶ Y') :
    (f ⊗ₘ q) ≫ ((T.projection g).app X' ⊗ₘ (T.projection h).app Y') =
      ((T.projection g).app X ⊗ₘ (T.projection h).app Y) ≫ (f ⊗ₘ q) := by
  rw [tensorHom_comp_tensorHom, T.projection_naturality, T.projection_naturality,
    ← tensorHom_comp_tensorHom]

theorem tensor_simple (k : G) (i j : ι) :
    (T.projection k).app (S.simpleObject i ⊗ S.simpleObject j) =
      ∑ g : G, ∑ h : G, if g * h = k then
        ((T.projection g).app (S.simpleObject i) ⊗ₘ
          (T.projection h).app (S.simpleObject j)) else 0 := by
  rw [T.projection_of_property k (T.degree i * T.degree j) _
    (T.tensor _ _ _ _ (T.degree_property i) (T.degree_property j))]
  rw [Finset.sum_eq_single (T.degree i)]
  · rw [Finset.sum_eq_single (T.degree j)]
    · simp only [T.projection_simple, if_pos rfl, if_true, id_tensorHom_id]
      simp only [eq_comm]
      congr 1 <;> erw [id_tensorHom_id]
      rfl
    · intro h _ hh
      simp [T.projection_simple, hh]
    · simp
  · intro g _ hg
    apply Finset.sum_eq_zero
    intro h _
    simp [T.projection_simple, hg]
  · simp

/-- Actual tensor closure of actual components gives the convolution
equation on every actual tensor product, by actual simple resolutions. -/
theorem tensor_convolution (k : G) (X Y : C) :
    (T.projection k).app (X ⊗ Y) =
      ∑ g : G, ∑ h : G, if g * h = k then
        ((T.projection g).app X ⊗ₘ (T.projection h).app Y) else 0 := by
  apply S.coend_map_hom_ext ((tensoringRight C).obj Y) X
  intro a
  apply S.coend_map_hom_ext ((tensoringLeft C).obj (S.simpleObject (S.label X a))) Y
  intro b
  change (S.simpleObject (S.label X a) ◁ S.coendInclusion Y b) ≫
    (S.coendInclusion X a ▷ Y) ≫ _ =
      (S.simpleObject (S.label X a) ◁ S.coendInclusion Y b) ≫
        (S.coendInclusion X a ▷ Y) ≫ _
  simp only [← Category.assoc]
  rw [← tensorHom_def', T.projection_naturality]
  have hs := congrArg
    (fun q => q ≫ (S.coendInclusion X a ⊗ₘ S.coendInclusion Y b))
      (T.tensor_simple k (S.label X a) (S.label Y b))
  simpa only [Preadditive.comp_sum, Preadditive.sum_comp, comp_ite, ite_comp,
    comp_zero, zero_comp, T.tensor_projection_naturality] using hs

/-- Actual component properties construct an actual grading. All degree
projectors and their tensor equations are proved from actual decompositions. -/
def grading : Grading G C where
  projection := T.projection
  orthogonal := T.orthogonal
  total := T.total
  unit g := T.projection_of_property g 1 (𝟙_ C) T.unit
  tensor := T.tensor_convolution

/-- The constructed homogeneous objects are exactly the original actual
component objects. -/
theorem grading_homogeneous_iff (g : G) (X : C) :
    T.grading.Homogeneous g X ↔ T.property g X :=
  S.supportProjector_eq_id_iff (T.property g) X

end Paper18.Category.CrossedBraidedGauging.ComponentProperties

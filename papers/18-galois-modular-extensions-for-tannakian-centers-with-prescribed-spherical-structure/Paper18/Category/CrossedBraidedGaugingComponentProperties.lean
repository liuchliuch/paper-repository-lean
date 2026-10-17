import Paper18.Category.CrossedBraidedGaugingGrading
import Paper18.Category.CentralizerDimensionProjector
import Paper18.Category.SemisimpleCoendBasic

/-! # Actual component properties construct actual grading projectors

The inputs are additive and retract-closed actual full components, a unique
degree of each actual simple, and genuine tensor closure. All projector
maps are constructed from the actual semisimple decomposition.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w t
namespace Paper18.Category.CrossedBraidedGauging
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C]
  {ι : Type t} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- Actual full component properties, as supplied by a genuine finite
component assembly. No projector or decomposition is included as data. -/
structure ComponentProperties where
  property : G → ObjectProperty C
  additive (g : G) : IsAdditiveFullProperty (property g)
  simple_degree (i : ι) : ∃! g : G, property g (S.simpleObject i)
  unit : property 1 (𝟙_ C)
  tensor (g h : G) (X Y : C) :
    property g X → property h Y → property (g * h) (X ⊗ Y)

namespace ComponentProperties
variable {S} (T : ComponentProperties (G := G) S)
attribute [instance] ComponentProperties.additive

def degree (i : ι) : G := Classical.choose (T.simple_degree i)

theorem degree_property (i : ι) : T.property (T.degree i) (S.simpleObject i) :=
  (Classical.choose_spec (T.simple_degree i)).1

theorem property_simple_iff (g : G) (i : ι) :
    T.property g (S.simpleObject i) ↔ g = T.degree i := by
  constructor
  · exact (Classical.choose_spec (T.simple_degree i)).2 g
  · intro h
    subst g
    exact T.degree_property i

/-- The actual semisimple support projection of an actual component. -/
def projection (g : G) : 𝟭 C ⟶ 𝟭 C := S.supportProjector (T.property g)

@[simp] theorem projection_simple (g : G) (i : ι) :
    (T.projection g).app (S.simpleObject i) =
      if g = T.degree i then 𝟙 (S.simpleObject i) else 0 := by
  simp only [projection, S.supportProjector_simple, T.property_simple_iff]
  rfl

@[reassoc] theorem projection_naturality (g : G) {X Y : C} (f : X ⟶ Y) :
    f ≫ (T.projection g).app Y = (T.projection g).app X ≫ f :=
  (T.projection g).naturality f

theorem orthogonal (g h : G) (X : C) :
    (T.projection g).app X ≫ (T.projection h).app X =
      if g = h then (T.projection g).app X else 0 := by
  have hn : T.projection g ≫ T.projection h =
      if g = h then T.projection g else 0 := by
    apply S.natEnd_ext_simples
    intro i
    change (T.projection g).app _ ≫ (T.projection h).app _ = _
    simp only [T.projection_simple]
    by_cases hgh : g = h
    · subst h
      simp only [if_pos rfl, NatTrans.comp_app, T.projection_simple]
      split_ifs <;> simp_all
    · rw [if_neg hgh]
      change _ = 0
      split_ifs with hgd hhd
      · exact False.elim (hgh (hgd.trans hhd.symm))
      · simp
      · simp
      · simp
  have hx := congrArg (fun q : 𝟭 C ⟶ 𝟭 C => q.app X) hn
  by_cases hgh : g = h
  · simpa only [if_pos hgh, NatTrans.comp_app] using hx
  · simpa only [if_neg hgh, NatTrans.comp_app, NatTrans.app_zero] using hx

theorem total (X : C) : ∑ g : G, (T.projection g).app X = 𝟙 X := by
  have hn : ∑ g : G, T.projection g = 𝟙 (𝟭 C) := by
    apply S.natEnd_ext_simples
    intro i
    change (∑ g : G, T.projection g).app _ = 𝟙 _
    simp only [NatTrans.app_sum, T.projection_simple]
    rw [Finset.sum_eq_single (T.degree i)]
    · simp
    · intro g _ hg
      simp only [if_neg hg]
    · simp
  have hx := congrArg (fun q : 𝟭 C ⟶ 𝟭 C => q.app X) hn
  simpa only [NatTrans.app_sum, NatTrans.id_app] using hx

theorem projection_of_property (g h : G) (X : C) (hX : T.property h X) :
    (T.projection g).app X = if g = h then 𝟙 X else 0 := by
  have hh : (T.projection h).app X = 𝟙 X :=
    (S.supportProjector_eq_id_iff (T.property h) X).mpr hX
  by_cases hgh : g = h
  · subst h
    simp only [if_pos rfl, if_true, hh]
  · have ho := T.orthogonal g h X
    rw [hh, if_neg hgh] at ho
    erw [Category.comp_id] at ho
    simpa only [if_neg hgh] using ho

end ComponentProperties
end Paper18.Category.CrossedBraidedGauging

import Paper18.Category.EquivariantMonoidal
import Paper18.Category.Semisimple

/-! # Actual finite-group grading projectors

A grading is given by actual natural orthogonal projections, resolving
identity and satisfying the actual tensor convolution equation. No simple
labels, graded decomposition certificate, crossed realization, or gauging
conclusion is included in the data.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.CrossedBraidedGauging
variable (G : Type w) [Group G] [Fintype G]
  (C : Type u) [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- Actual finite-group degree projectors of a monoidal category. -/
structure Grading where
  projection : G → (𝟭 C ⟶ 𝟭 C)
  orthogonal (g h : G) (X : C) :
    (projection g).app X ≫ (projection h).app X =
      if g = h then (projection g).app X else 0
  total (X : C) : ∑ g : G, (projection g).app X = 𝟙 X
  unit (g : G) : (projection g).app (𝟙_ C) = if g = 1 then 𝟙 _ else 0
  tensor (k : G) (X Y : C) :
    (projection k).app (X ⊗ Y) =
      ∑ g : G, ∑ h : G,
        if g * h = k then (projection g).app X ⊗ₘ (projection h).app Y else 0

namespace Grading
variable {G C} (P : Grading G C)

@[reassoc] theorem projection_naturality (g : G) {X Y : C} (f : X ⟶ Y) :
    f ≫ (P.projection g).app Y = (P.projection g).app X ≫ f := by
  simpa only [Functor.id_map] using (P.projection g).naturality f

/-- Homogeneous means that the actual degree projection is identity. -/
def Homogeneous (g : G) (X : C) : Prop := (P.projection g).app X = 𝟙 X

@[simp] theorem projection_idempotent (g : G) (X : C) :
    (P.projection g).app X ≫ (P.projection g).app X = (P.projection g).app X := by
  simpa only [if_pos rfl] using P.orthogonal g g X

@[simp] theorem projection_comp_of_ne {g h : G} (hgh : g ≠ h) (X : C) :
    (P.projection g).app X ≫ (P.projection h).app X = 0 := by
  simpa only [if_neg hgh] using P.orthogonal g h X

/-- An actual homogeneous object has no other degree component. -/
theorem projection_eq_zero_of_homogeneous {g h : G} (hgh : g ≠ h) {X : C}
    (hX : P.Homogeneous h X) : (P.projection g).app X = 0 := by
  have h := P.projection_comp_of_ne hgh X
  rw [hX] at h
  erw [Category.comp_id] at h
  exact h

theorem homogeneous_iso {g : G} {X Y : C} (e : X ≅ Y)
    (hY : P.Homogeneous g Y) : P.Homogeneous g X := by
  change (P.projection g).app X = 𝟙 X
  apply (cancel_mono e.hom).mp
  have h := (P.projection g).naturality e.hom
  change e.hom ≫ (P.projection g).app Y = (P.projection g).app X ≫ e.hom at h
  rw [hY, Category.comp_id] at h
  erw [Category.id_comp]
  exact h.symm

/-- Distinct actual homogeneous components are categorically orthogonal. -/
theorem homogeneous_hom_zero {g h : G} (hgh : g ≠ h) {X Y : C}
    (hX : P.Homogeneous g X) (hY : P.Homogeneous h Y) (f : X ⟶ Y) : f = 0 := by
  have hn := (P.projection g).naturality f
  change f ≫ (P.projection g).app Y = (P.projection g).app X ≫ f at hn
  rw [hX, P.projection_eq_zero_of_homogeneous hgh hY, comp_zero] at hn
  erw [Category.id_comp] at hn
  exact hn.symm

/-- Actual degree projections on a homogeneous object are Kronecker deltas. -/
theorem projection_homogeneous {h : G} {X : C} (hX : P.Homogeneous h X) (g : G) :
    (P.projection g).app X = if g = h then 𝟙 X else 0 := by
  by_cases hgh : g = h
  · subst g
    simpa only [if_pos rfl] using hX
  · simpa only [if_neg hgh] using P.projection_eq_zero_of_homogeneous hgh hX

theorem homogeneous_unit : P.Homogeneous 1 (𝟙_ C) := by
  simpa only [Homogeneous, if_pos rfl] using P.unit 1

variable [MonoidalPreadditive C]

/-- Actual homogeneous degrees multiply under the actual tensor product. -/
theorem homogeneous_tensor {g h : G} {X Y : C}
    (hX : P.Homogeneous g X) (hY : P.Homogeneous h Y) :
    P.Homogeneous (g * h) (X ⊗ Y) := by
  rw [Homogeneous, P.tensor]
  rw [Finset.sum_eq_single g]
  · rw [Finset.sum_eq_single h]
    · simp [P.projection_homogeneous hX, P.projection_homogeneous hY]
    · intro b _ hb
      simp [P.projection_homogeneous hY b, hb]
    · simp
  · intro a _ ha
    simp [P.projection_homogeneous hX a, ha]
  · simp

variable [HasFiniteBiproducts C]

/-- Finite actual sums stay in one actual homogeneous component. -/
theorem homogeneous_biproduct {J : Type*} [Fintype J] (f : J → C) (g : G)
    (hf : ∀ j, P.Homogeneous g (f j)) : P.Homogeneous g (⨁ f) := by
  change (P.projection g).app (⨁ f) = 𝟙 _
  apply biproduct.hom_ext
  intro j
  have h := (P.projection g).naturality (biproduct.π f j)
  change biproduct.π f j ≫ (P.projection g).app (f j) =
    (P.projection g).app (⨁ f) ≫ biproduct.π f j at h
  rw [hf j, Category.comp_id] at h
  erw [Category.id_comp]
  exact h.symm

/-- Actual homogeneous components are closed under actual retracts. -/
theorem homogeneous_retract {g : G} {X Y : C} (r : Retract X Y)
    (hY : P.Homogeneous g Y) : P.Homogeneous g X := by
  have h := (P.projection g).naturality r.i
  change r.i ≫ (P.projection g).app Y = (P.projection g).app X ≫ r.i at h
  rw [hY] at h
  have hh := congrArg (fun f => f ≫ r.r) h
  change (P.projection g).app X = 𝟙 X
  simp only [Category.comp_id, Category.assoc, r.retract] at hh
  erw [Category.comp_id] at hh
  exact hh.symm

end Grading
end Paper18.Category.CrossedBraidedGauging

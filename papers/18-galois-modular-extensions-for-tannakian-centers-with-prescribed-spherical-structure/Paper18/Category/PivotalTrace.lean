import Paper18.Category.Pivotal
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Properties of actual pivotal traces

Cyclicity, additivity, invariance under isomorphism, and finite-resolution formulas
are proved for the categorical traces in `End(𝟙 C)`. The resolution formulas make
it possible to reduce sphericality to generators of a semisimple category without
replacing the category by numerical fusion data.
-/

noncomputable section
universe v u
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
namespace PivotalStructure
variable (J : PivotalStructure C)

/-- Cyclicity of the right categorical trace, for arbitrary morphisms. -/
lemma rightTrace_comp {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) :
    J.rightTrace (f ≫ g) = J.rightTrace (g ≫ f) := by
  simp only [rightTrace, leftEvaluation, comp_whiskerRight, assoc]
  rw [← coevaluation_comp_rightAdjointMate_assoc f]
  rw [whisker_exchange_assoc]
  rw [whisker_exchange_assoc]
  dsimp only [doubleDualFunctor, dual, dualMap] at *
  rw [← rightAdjointMate_comp_evaluation (rightAdjointMate f)]
  have hn := congrArg (fun k => k ▷ dual C Y) (J.j.hom.naturality f).symm
  dsimp only [doubleDualFunctor, dualMap, Functor.id_map] at hn
  simp only [comp_whiskerRight] at hn
  rw [reassoc_of% hn]

/-- Cyclicity of the left categorical trace. -/
lemma leftTrace_comp {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) :
    J.leftTrace (f ≫ g) = J.leftTrace (g ≫ f) := by
  simp only [leftTrace, leftCoevaluation, whiskerLeft_comp, assoc]
  rw [← rightAdjointMate_comp_evaluation g]
  rw [whisker_exchange_assoc]
  rw [whisker_exchange_assoc]
  rw [← coevaluation_comp_rightAdjointMate_assoc (rightAdjointMate g)]
  have hn := congrArg (fun k => dual C Y ◁ k) (J.j.inv.naturality g)
  dsimp only [doubleDualFunctor, dualMap, Functor.id_map] at hn
  simp only [whiskerLeft_comp] at hn
  rw [reassoc_of% hn]

/-- Categorical dimensions do not depend on the representative of an isomorphism class. -/
lemma rightDimension_iso {X Y : C} (i : X ≅ Y) :
    J.rightDimension X = J.rightDimension Y := by
  simpa [rightDimension] using J.rightTrace_comp i.hom i.inv

lemma leftDimension_iso {X Y : C} (i : X ≅ Y) :
    J.leftDimension X = J.leftDimension Y := by
  simpa [leftDimension] using J.leftTrace_comp i.hom i.inv

variable [Preadditive C] [MonoidalPreadditive C]

@[simp] lemma rightTrace_zero (X : C) : J.rightTrace (0 : X ⟶ X) = 0 := by
  simp [rightTrace]

@[simp] lemma leftTrace_zero (X : C) : J.leftTrace (0 : X ⟶ X) = 0 := by
  simp [leftTrace]

lemma rightTrace_add {X : C} (f g : X ⟶ X) :
    J.rightTrace (f + g) = J.rightTrace f + J.rightTrace g := by
  simp [rightTrace, Preadditive.comp_add, Preadditive.add_comp]

lemma leftTrace_add {X : C} (f g : X ⟶ X) :
    J.leftTrace (f + g) = J.leftTrace f + J.leftTrace g := by
  simp [leftTrace, Preadditive.comp_add, Preadditive.add_comp]

/-- The right categorical trace as an additive homomorphism. -/
def rightTraceAddHom (X : C) : (X ⟶ X) →+ (𝟙_ C ⟶ 𝟙_ C) where
  toFun := J.rightTrace
  map_zero' := J.rightTrace_zero X
  map_add' := J.rightTrace_add

/-- The left categorical trace as an additive homomorphism. -/
def leftTraceAddHom (X : C) : (X ⟶ X) →+ (𝟙_ C ⟶ 𝟙_ C) where
  toFun := J.leftTrace
  map_zero' := J.leftTrace_zero X
  map_add' := J.leftTrace_add

open scoped BigOperators

lemma rightTrace_sum {ι : Type*} {X : C} (s : Finset ι) (f : ι → (X ⟶ X)) :
    J.rightTrace (∑ i ∈ s, f i) = ∑ i ∈ s, J.rightTrace (f i) :=
  map_sum (J.rightTraceAddHom X) f s

lemma leftTrace_sum {ι : Type*} {X : C} (s : Finset ι) (f : ι → (X ⟶ X)) :
    J.leftTrace (∑ i ∈ s, f i) = ∑ i ∈ s, J.leftTrace (f i) :=
  map_sum (J.leftTraceAddHom X) f s

/-- A resolution of the identity reduces every right trace to the summands.
This applies in particular to any finite biproduct decomposition. -/
lemma rightTrace_of_resolution {ι : Type*} [Fintype ι] {X : C} (Y : ι → C)
    (i : ∀ a, Y a ⟶ X) (p : ∀ a, X ⟶ Y a)
    (h : ∑ a, p a ≫ i a = 𝟙 X) (f : X ⟶ X) :
    J.rightTrace f = ∑ a, J.rightTrace (i a ≫ f ≫ p a) := by
  calc
    J.rightTrace f = J.rightTrace ((∑ a, p a ≫ i a) ≫ f) := by rw [h, id_comp]
    _ = ∑ a, J.rightTrace (p a ≫ (i a ≫ f)) := by
      rw [Preadditive.sum_comp]
      simpa only [assoc] using map_sum (J.rightTraceAddHom X) (fun a => (p a ≫ i a) ≫ f) Finset.univ
    _ = _ := Finset.sum_congr rfl fun a _ => by
      simpa only [assoc] using J.rightTrace_comp (p a) (i a ≫ f)

/-- The parallel resolution formula for the left trace. -/
lemma leftTrace_of_resolution {ι : Type*} [Fintype ι] {X : C} (Y : ι → C)
    (i : ∀ a, Y a ⟶ X) (p : ∀ a, X ⟶ Y a)
    (h : ∑ a, p a ≫ i a = 𝟙 X) (f : X ⟶ X) :
    J.leftTrace f = ∑ a, J.leftTrace (i a ≫ f ≫ p a) := by
  calc
    J.leftTrace f = J.leftTrace ((∑ a, p a ≫ i a) ≫ f) := by rw [h, id_comp]
    _ = ∑ a, J.leftTrace (p a ≫ (i a ≫ f)) := by
      rw [Preadditive.sum_comp]
      simpa only [assoc] using map_sum (J.leftTraceAddHom X) (fun a => (p a ≫ i a) ≫ f) Finset.univ
    _ = _ := Finset.sum_congr rfl fun a _ => by
      simpa only [assoc] using J.leftTrace_comp (p a) (i a ≫ f)

/-- Sphericality on a finite collection of summands implies equality of traces
on every endomorphism of an object they resolve. -/
lemma traces_eq_of_resolution {ι : Type*} [Fintype ι] {X : C} (Y : ι → C)
    (i : ∀ a, Y a ⟶ X) (p : ∀ a, X ⟶ Y a)
    (h : ∑ a, p a ≫ i a = 𝟙 X)
    (hY : ∀ a (g : Y a ⟶ Y a), J.leftTrace g = J.rightTrace g) (f : X ⟶ X) :
    J.leftTrace f = J.rightTrace f := by
  rw [J.leftTrace_of_resolution Y i p h, J.rightTrace_of_resolution Y i p h]
  exact Finset.sum_congr rfl fun a _ => hY a _

end PivotalStructure
end Paper18.Category

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Actual finite semisimple categories

The simple objects here are objects of a category in the usual mathlib sense.
Semisimplicity is specified by actual isomorphisms to finite biproducts of
chosen simple representatives. In particular, no multiplicity, fusion
coefficient, or numerical decomposition law is a field of this structure.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

universe v u w

namespace Paper18.Category

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- A chosen finite semisimple skeleton: a finite family of pairwise
nonisomorphic simple objects and an actual finite biproduct decomposition of
every object. The linear and finite Hom hypotheses are imposed separately
when proving numerical statements. -/
structure FiniteSemisimpleSkeleton (ι : Type w) [Fintype ι] [HasFiniteBiproducts C] where
  /-- Chosen simple representative. -/
  simpleObject : ι → C
  /-- These objects are simple in the categorical sense. -/
  simple : ∀ i, Simple (simpleObject i)
  /-- Distinct labels represent nonisomorphic simple objects. -/
  iso_injective : ∀ i j, Nonempty (simpleObject i ≅ simpleObject j) → i = j
  /-- Number of simple summands in a chosen decomposition of an object. -/
  length : C → ℕ
  /-- Label of each simple summand in that decomposition. -/
  label : ∀ X, Fin (length X) → ι
  /-- The decomposition is an isomorphism of actual category objects. -/
  decomposition : ∀ X, X ≅ ⨁ fun a : Fin (length X) => simpleObject (label X a)

namespace FiniteSemisimpleSkeleton

variable {C} {ι : Type w} [Fintype ι] [HasFiniteBiproducts C]
  (S : FiniteSemisimpleSkeleton C ι)

attribute [instance] simple

@[simp]
theorem nonempty_iso_iff (i j : ι) :
    Nonempty (S.simpleObject i ≅ S.simpleObject j) ↔ i = j := by
  constructor
  · exact S.iso_injective i j
  · rintro rfl
    exact ⟨Iso.refl _⟩

end FiniteSemisimpleSkeleton

section LinearBiproduct

variable {C} [Linear ℂ C]
variable {J : Type w} (f : J → C) [HasBiproduct f]

/-- The universal property of an actual biproduct, as a complex linear
isomorphism on Hom spaces. -/
def homBiproductLinearEquiv (X : C) :
    (X ⟶ ⨁ f) ≃ₗ[ℂ] (∀ j, X ⟶ f j) where
  toFun g j := g ≫ biproduct.π f j
  invFun g := biproduct.lift g
  left_inv g := by
    apply biproduct.hom_ext
    intro j
    simp
  right_inv g := by
    funext j
    simp
  map_add' g h := by
    funext j
    simp
  map_smul' r g := by
    funext j
    simp

/-- The dual universal property, as a complex linear isomorphism. -/
def biproductHomLinearEquiv (X : C) :
    (⨁ f ⟶ X) ≃ₗ[ℂ] (∀ j, f j ⟶ X) where
  toFun g j := biproduct.ι f j ≫ g
  invFun g := biproduct.desc g
  left_inv g := by
    apply biproduct.hom_ext'
    intro j
    simp
  right_inv g := by
    funext j
    simp
  map_add' g h := by
    funext j
    simp
  map_smul' r g := by
    funext j
    simp

variable [Fintype J] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]

/-- Additivity of Hom dimension in a finite biproduct target, proved from its
linear universal property. -/
theorem finrank_hom_biproduct (X : C) :
    Module.finrank ℂ (X ⟶ ⨁ f) = ∑ j, Module.finrank ℂ (X ⟶ f j) := by
  rw [(homBiproductLinearEquiv f X).finrank_eq, Module.finrank_pi_fintype]

/-- Additivity of Hom dimension in a finite biproduct source. -/
theorem finrank_biproduct_hom (X : C) :
    Module.finrank ℂ (⨁ f ⟶ X) = ∑ j, Module.finrank ℂ (f j ⟶ X) := by
  rw [(biproductHomLinearEquiv f X).finrank_eq, Module.finrank_pi_fintype]

end LinearBiproduct

/-- Hom dimensions are invariant under actual isomorphisms in both variables. -/
theorem finrank_hom_iso {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
    {X X' Y Y' : C} (e : X ≅ X') (f : Y ≅ Y') :
    Module.finrank ℂ (X ⟶ Y) = Module.finrank ℂ (X' ⟶ Y') :=
  (CategoryTheory.Linear.homCongr ℂ e f).finrank_eq

end Paper18.Category

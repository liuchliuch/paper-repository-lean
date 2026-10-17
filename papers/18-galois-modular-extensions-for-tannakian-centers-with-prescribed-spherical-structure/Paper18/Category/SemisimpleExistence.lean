import Paper18.Category.Semisimple
import Paper18.Category.SemisimpleComplement
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.Data.Fin.Tuple.Basic

/-! # Finite simple decompositions from split monomorphisms

This file derives semisimplicity from actual splitting maps and finite Hom
spaces. It is used for categories constructed in the paper, where a complete
family of simples is an output rather than an additional hypothesis.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Limits
universe v u
namespace Paper18.Category

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A nonzero object which is not simple has a nonzero proper subobject. -/
theorem exists_proper_mono_of_not_simple (X : C) (hz : ¬ IsZero X) (hs : ¬ Simple X) :
    ∃ (Y : C) (f : Y ⟶ X), Mono f ∧ f ≠ 0 ∧ ¬ IsIso f := by
  by_contra hn
  apply hs
  constructor
  intro Y f hm
  constructor
  · intro hf hf0
    letI := hf
    apply hz
    apply (IsZero.iff_id_eq_zero X).mpr
    have he := IsIso.inv_hom_id f
    simpa only [hf0, comp_zero] using he.symm
  · intro hf
    by_contra hi
    exact hn ⟨Y, f, hm, hf, hi⟩

variable [HasFiniteBiproducts C]
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- The actual empty biproduct decomposition of a zero object. -/
def zeroBiproductIso (X : C) (h : IsZero X) :
    X ≅ ⨁ fun i : Fin 0 => (Fin.elim0 i : C) where
  hom := 0
  inv := 0
  hom_inv_id := by rw [zero_comp, (IsZero.iff_id_eq_zero X).mp h]
  inv_hom_id := by
    apply biproduct.hom_ext
    intro i
    exact Fin.elim0 i

/-- Concatenating two actual finite biproducts. -/
def biprodBiproductSumIso {I J : Type} [Fintype I] [Fintype J]
    (f : I → C) (g : J → C) :
    (⨁ f) ⊞ (⨁ g) ≅ ⨁ (Sum.elim f g) where
  hom := biprod.desc
    (biproduct.desc fun i => biproduct.ι (Sum.elim f g) (Sum.inl i))
    (biproduct.desc fun j => biproduct.ι (Sum.elim f g) (Sum.inr j))
  inv := biproduct.desc (fun k => match k with
    | Sum.inl i => biproduct.ι f i ≫ biprod.inl
    | Sum.inr j => biproduct.ι g j ≫ biprod.inr)
  hom_inv_id := by
    apply biprod.hom_ext'
    · apply biproduct.hom_ext'
      intro i
      simp
    · apply biproduct.hom_ext'
      intro j
      simp
  inv_hom_id := by
    apply biproduct.hom_ext'
    intro k
    cases k <;> simp [Category.assoc]

/-- Concatenation with the standard `Fin (n + m)` indexing. -/
def biprodBiproductFinIso {n m : ℕ} (f : Fin n → C) (g : Fin m → C) :
    (⨁ f) ⊞ (⨁ g) ≅ ⨁ (Fin.append f g) :=
  biprodBiproductSumIso f g ≪≫ biproduct.whiskerEquiv finSumFinEquiv
    (by intro i; cases i <;> exact eqToIso (by simp))

variable [HasKernels C] [Linear ℂ C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]

/-- Finite-dimensional Hom spaces and actual splitting of every
monomorphism imply actual finite decompositions into categorical simples.
The proof descends on the endomorphism dimension of both proper summands. -/
theorem exists_simple_biproduct_of_splitMonos
    (split : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], SplitMono f) (X : C) :
    ∃ (n : ℕ) (f : Fin n → C), (∀ i, Simple (f i)) ∧ Nonempty (X ≅ ⨁ f) := by
  have H : ∀ n : ℕ, ∀ X : C, Module.finrank ℂ (X ⟶ X) = n →
      ∃ (m : ℕ) (f : Fin m → C), (∀ i, Simple (f i)) ∧ Nonempty (X ≅ ⨁ f) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro X hn
      by_cases hz : IsZero X
      · exact ⟨0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ⟨zeroBiproductIso X hz⟩⟩
      by_cases hs : Simple X
      · exact ⟨1, fun _ => X, fun _ => hs, ⟨(biproductUniqueIso (fun _ : Fin 1 => X)).symm⟩⟩
      obtain ⟨Y, f, hm, hf, hi⟩ := exists_proper_mono_of_not_simple X hz hs
      letI := hm
      let s := split f
      have hY := end_finrank_lt_of_splitMono f s hf hi
      have hZ := complement_end_finrank_lt_of_splitMono f s hf hi
      rw [hn] at hY hZ
      obtain ⟨m, a, ha, ⟨ea⟩⟩ := ih _ hY Y rfl
      obtain ⟨k, b, hb, ⟨eb⟩⟩ := ih _ hZ (kernel s.retraction) rfl
      refine ⟨m + k, Fin.append a b, ?_, ⟨?_⟩⟩
      · intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa using ha j
        · simpa using hb j
      · exact splitMonoComplementIso f s ≪≫ biprod.mapIso ea eb ≪≫
          biprodBiproductFinIso a b
  exact H _ X rfl

end Paper18.Category

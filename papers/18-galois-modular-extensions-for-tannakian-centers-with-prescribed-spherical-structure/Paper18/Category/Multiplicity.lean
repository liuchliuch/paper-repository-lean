import Paper18.Category.Semisimple
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.CategoryTheory.Retract

/-!
# Hom multiplicities in finite semisimple categories

All multiplicities in this file are dimensions of actual Hom spaces. Their
values on simples, their biproduct additivity, and the matrix formula for
additive functors are theorems, rather than fields of a numerical certificate.
-/

noncomputable section

open Classical
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators

universe v u w v' u' w'

namespace Paper18.Category
namespace FiniteSemisimpleSkeleton

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- The multiplicity of a simple representative in an actual object. -/
def multiplicity (X : C) (i : ι) : ℕ :=
  Module.finrank ℂ (S.simpleObject i ⟶ X)

/-- Schur's lemma gives the Kronecker delta for the chosen simple family. -/
theorem finrank_simple_hom_simple (i j : ι) :
    Module.finrank ℂ (S.simpleObject i ⟶ S.simpleObject j) = if i = j then 1 else 0 := by
  rw [CategoryTheory.finrank_hom_simple_simple ℂ, S.nonempty_iso_iff]

@[simp]
theorem multiplicity_simple (i j : ι) :
    S.multiplicity (S.simpleObject j) i = if i = j then 1 else 0 :=
  S.finrank_simple_hom_simple i j

omit [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] in
/-- Multiplicity does not depend on the representative of an object up to
actual categorical isomorphism. -/
theorem multiplicity_iso {X Y : C} (e : X ≅ Y) (i : ι) :
    S.multiplicity X i = S.multiplicity Y i :=
  finrank_hom_iso (Iso.refl _) e

omit [HasKernels C] in
/-- Multiplicities are additive on arbitrary finite biproducts. -/
theorem multiplicity_biproduct {J : Type*} [Fintype J] (f : J → C) (i : ι) :
    S.multiplicity (⨁ f) i = ∑ j, S.multiplicity (f j) i :=
  finrank_hom_biproduct f (S.simpleObject i)

/-- Any actual decomposition into simple representatives recovers its
multiplicities as the number of occurrences of each representative. -/
theorem multiplicity_of_decomposition {J : Type*} [Fintype J]
    {X : C} (label : J → ι) (e : X ≅ ⨁ fun j => S.simpleObject (label j)) (i : ι) :
    S.multiplicity X i = ∑ j, if i = label j then 1 else 0 := by
  rw [S.multiplicity_iso e, S.multiplicity_biproduct]
  simp only [S.multiplicity_simple]

/-- The chosen decomposition is counted by Hom dimension. -/
theorem multiplicity_eq_sum (X : C) (i : ι) :
    S.multiplicity X i = ∑ a : Fin (S.length X), if i = S.label X a then 1 else 0 :=
  S.multiplicity_of_decomposition (S.label X) (S.decomposition X) i

/-- Positive Hom multiplicity detects a summand in the actual chosen
biproduct decomposition. -/
theorem multiplicity_pos_iff_label (X : C) (i : ι) :
    0 < S.multiplicity X i ↔ ∃ a : Fin (S.length X), i = S.label X a := by
  rw [S.multiplicity_eq_sum, Finset.sum_pos_iff]
  constructor
  · rintro ⟨a, ha, h⟩
    refine ⟨a, ?_⟩
    split_ifs at h with he
    · exact he
    · omega
  · rintro ⟨a, ha⟩
    exact ⟨a, Finset.mem_univ _, by simp [ha]⟩

/-- Positive multiplicity produces actual inclusion and retraction maps of
the corresponding simple summand. -/
def retractOfMultiplicityPos (X : C) (i : ι) (h : 0 < S.multiplicity X i) :
    Retract (S.simpleObject i) X := by
  let a := Classical.choose ((S.multiplicity_pos_iff_label X i).mp h)
  have ha := Classical.choose_spec ((S.multiplicity_pos_iff_label X i).mp h)
  let e : S.simpleObject i ≅ S.simpleObject (S.label X a) :=
    eqToIso (congrArg S.simpleObject ha)
  refine (Retract.ofIso e).trans ?_
  exact
    { i := biproduct.ι (fun b => S.simpleObject (S.label X b)) a ≫ (S.decomposition X).inv
      r := (S.decomposition X).hom ≫ biproduct.π (fun b => S.simpleObject (S.label X b)) a
      retract := by simp }

/-- Positivity of numerical multiplicity is equivalent to a categorical
simple retract, with no numerical decomposition axioms. -/
theorem multiplicity_pos_iff_retract (X : C) (i : ι) :
    0 < S.multiplicity X i ↔ Nonempty (Retract (S.simpleObject i) X) := by
  constructor
  · intro h
    exact ⟨S.retractOfMultiplicityPos X i h⟩
  · rintro ⟨r⟩
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨r.i, ?_⟩
    intro h
    apply CategoryTheory.id_nonzero (S.simpleObject i)
    rw [← r.retract, h, zero_comp]

/-- The count of each summand is independent of the chosen biproduct
presentation. -/
theorem decomposition_count_unique {J K : Type*} [Fintype J] [Fintype K]
    {X : C} (label₁ : J → ι) (label₂ : K → ι)
    (e₁ : X ≅ ⨁ fun j => S.simpleObject (label₁ j))
    (e₂ : X ≅ ⨁ fun k => S.simpleObject (label₂ k)) (i : ι) :
    (∑ j, if i = label₁ j then 1 else 0) = ∑ k, if i = label₂ k then 1 else 0 := by
  rw [← S.multiplicity_of_decomposition label₁ e₁,
    ← S.multiplicity_of_decomposition label₂ e₂]

/-- Summing a function on the chosen summands is the same as summing it
against Hom multiplicities. This is the finite change of indexing needed for
functor and tensor-product multiplicity formulas. -/
theorem sum_multiplicity (X : C) (c : ι → ℕ) :
    (∑ i, S.multiplicity X i * c i) = ∑ a : Fin (S.length X), c (S.label X a) := by
  simp_rw [S.multiplicity_eq_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp

/-- The length of a decomposition is determined by categorical Hom spaces. -/
theorem sum_multiplicity_eq_length (X : C) :
    (∑ i, S.multiplicity X i) = S.length X := by
  simpa using S.sum_multiplicity X (fun _ => 1)

/-- The dimension of an arbitrary Hom space is the dot product of the simple
multiplicity vectors of its source and target. -/
theorem finrank_hom_eq_sum (X Y : C) :
    Module.finrank ℂ (X ⟶ Y) = ∑ i, S.multiplicity X i * S.multiplicity Y i := by
  rw [finrank_hom_iso (S.decomposition X) (Iso.refl Y), finrank_biproduct_hom]
  exact (S.sum_multiplicity X (S.multiplicity Y)).symm

include S in
/-- The dimensions of Hom spaces in opposite directions agree in a finite
semisimple complex-linear category. -/
theorem finrank_hom_comm (X Y : C) :
    Module.finrank ℂ (X ⟶ Y) = Module.finrank ℂ (Y ⟶ X) := by
  rw [S.finrank_hom_eq_sum, S.finrank_hom_eq_sum]
  simp only [Nat.mul_comm]

/-- A simple multiplicity can equivalently be computed by maps onto the
simple representative. -/
theorem multiplicity_eq_finrank_hom (X : C) (i : ι) :
    S.multiplicity X i = Module.finrank ℂ (X ⟶ S.simpleObject i) :=
  S.finrank_hom_comm _ _

include S in
/-- In a finite semisimple category, one-dimensional endomorphism space
implies categorical simplicity. The proof constructs an isomorphism to an
actual simple retract. -/
theorem simple_of_finrank_end_eq_one (X : C)
    (h : Module.finrank ℂ (X ⟶ X) = 1) : Simple X := by
  have hp : 0 < ∑ i, S.multiplicity X i * S.multiplicity X i := by
    rw [← S.finrank_hom_eq_sum, h]
    exact zero_lt_one
  obtain ⟨i, hi, hpos⟩ := Finset.sum_pos_iff.mp hp
  let r := S.retractOfMultiplicityPos X i (pos_of_mul_pos_right hpos (Nat.zero_le _))
  obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0 < Module.finrank ℂ (X ⟶ X) by omega)
  have hid : 𝟙 X ≠ 0 := by
    intro hz
    apply hf
    calc
      f = 𝟙 X ≫ f := (Category.id_comp f).symm
      _ = 0 := by rw [hz, zero_comp]
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (𝟙 X) hid).mp h (r.r ≫ r.i)
  have hc' : c • 𝟙 (S.simpleObject i) = 𝟙 (S.simpleObject i) := by
    calc
      c • 𝟙 (S.simpleObject i) = r.i ≫ (c • 𝟙 X) ≫ r.r := by simp
      _ = r.i ≫ (r.r ≫ r.i) ≫ r.r := by rw [hc]
      _ = 𝟙 (S.simpleObject i) := by simp [← Category.assoc]
  have hc1 : c = 1 := smul_left_injective ℂ (CategoryTheory.id_nonzero _) (by simpa using hc')
  have hr : r.r ≫ r.i = 𝟙 X := by simpa [hc1] using hc.symm
  exact Simple.of_iso
    { hom := r.r
      inv := r.i
      hom_inv_id := hr
      inv_hom_id := r.retract }

/-- Every actual simple object is isomorphic to one of the chosen
representatives. This follows from the actual decompositions. -/
theorem simple_isomorphic_representative (X : C) [Simple X] :
    ∃ i, Nonempty (X ≅ S.simpleObject i) := by
  have hd : (∑ a : Fin (S.length X),
      Module.finrank ℂ (X ⟶ S.simpleObject (S.label X a))) = 1 := by
    rw [← finrank_hom_biproduct,
      ← finrank_hom_iso (Iso.refl X) (S.decomposition X)]
    exact CategoryTheory.finrank_endomorphism_simple_eq_one ℂ X
  have hp : 0 < ∑ a : Fin (S.length X),
      Module.finrank ℂ (X ⟶ S.simpleObject (S.label X a)) := by omega
  obtain ⟨a, ha, hpos⟩ := Finset.sum_pos_iff.mp hp
  refine ⟨S.label X a, ?_⟩
  by_contra h
  have hz := CategoryTheory.finrank_hom_simple_simple_eq_zero_of_not_iso ℂ
    (fun e => h ⟨e⟩)
  omega

section Functor

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (F : C ⥤ D) [F.Additive]

/-- The actual image of a chosen decomposition under an additive functor. -/
def mapDecomposition (X : C) :
    F.obj X ≅ ⨁ fun a : Fin (S.length X) => F.obj (S.simpleObject (S.label X a)) :=
  F.mapIso (S.decomposition X) ≪≫
    F.mapBiproduct (fun a : Fin (S.length X) => S.simpleObject (S.label X a))

omit [HasKernels D] in
/-- An additive functor acts on multiplicities by its matrix of images of
simple objects. No multiplicity compatibility is assumed. -/
theorem multiplicity_map (X : C) (j : κ) :
    T.multiplicity (F.obj X) j =
      ∑ i, S.multiplicity X i * T.multiplicity (F.obj (S.simpleObject i)) j := by
  rw [T.multiplicity_iso (S.mapDecomposition F X), T.multiplicity_biproduct]
  exact (S.sum_multiplicity X (fun i => T.multiplicity (F.obj (S.simpleObject i)) j)).symm

/-- The matrix of an actual additive functor on simple multiplicities. -/
def imageCoeff (i : ι) (j : κ) : ℕ :=
  T.multiplicity (F.obj (S.simpleObject i)) j

omit [HasKernels D] in
/-- Every target object being an actual retract of an image implies the
numerical dominance of the matrix of simple multiplicities. -/
theorem imageCoeff_dominant_of_retracts
    (hF : ∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X))) (j : κ) :
    ∃ i : ι, 0 < S.imageCoeff T F i j := by
  obtain ⟨X, ⟨r⟩⟩ := hF (T.simpleObject j)
  have hn : r.i ≠ 0 := by
    intro hz
    apply CategoryTheory.id_nonzero (T.simpleObject j)
    rw [← r.retract, hz, zero_comp]
  have hp : 0 < T.multiplicity (F.obj X) j :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨r.i, hn⟩
  rw [S.multiplicity_map T F] at hp
  obtain ⟨i, hi, hp⟩ := Finset.sum_pos_iff.mp hp
  exact ⟨i, pos_of_mul_pos_right hp (Nat.zero_le _)⟩

/-- Matrix dominance of an actual additive functor is equivalent to every
target object being a categorical retract of an image. -/
theorem imageCoeff_dominant_iff_retracts :
    (∀ j : κ, ∃ i : ι, 0 < S.imageCoeff T F i j) ↔
      ∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X)) := by
  constructor
  · intro h Y
    choose i hi using fun a : Fin (T.length Y) => h (T.label Y a)
    let f : Fin (T.length Y) → C := fun a => S.simpleObject (i a)
    let r : ∀ a : Fin (T.length Y),
        Retract (T.simpleObject (T.label Y a)) (F.obj (f a)) :=
      fun a => T.retractOfMultiplicityPos (F.obj (f a)) (T.label Y a) (hi a)
    let rb : Retract (⨁ fun a : Fin (T.length Y) => T.simpleObject (T.label Y a))
        (⨁ fun a : Fin (T.length Y) => F.obj (f a)) :=
      { i := biproduct.map (fun a => (r a).i)
        r := biproduct.map (fun a => (r a).r)
        retract := by
          apply biproduct.hom_ext
          intro a
          simp [Category.assoc] }
    refine ⟨⨁ f, ⟨?_⟩⟩
    exact ((Retract.ofIso (T.decomposition Y)).trans rb).trans
      (Retract.ofIso (F.mapBiproduct f).symm)
  · exact S.imageCoeff_dominant_of_retracts T F

omit [Linear ℂ C] [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] in
/-- Faithfulness prevents any simple source object from having a zero image
multiplicity vector. -/
theorem imageCoeff_row_positive [F.Faithful] (i : ι) :
    ∃ j : κ, 0 < S.imageCoeff T F i j := by
  have hid : 𝟙 (F.obj (S.simpleObject i)) ≠ 0 := by
    intro h
    apply CategoryTheory.id_nonzero (S.simpleObject i)
    apply F.map_injective
    simpa using h
  have hp : 0 < Module.finrank ℂ
      (F.obj (S.simpleObject i) ⟶ F.obj (S.simpleObject i)) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hid⟩
  rw [T.finrank_hom_eq_sum] at hp
  obtain ⟨j, hj, hp⟩ := Finset.sum_pos_iff.mp hp
  exact ⟨j, pos_of_mul_pos_right hp (Nat.zero_le _)⟩

end Functor

section Tensor

variable [MonoidalCategory C] [MonoidalPreadditive C]

omit [MonoidalPreadditive C] in
/-- A simple tensor unit has a representative in the chosen finite family. -/
theorem exists_unit_label [Simple (𝟙_ C)] :
    ∃ i : ι, Nonempty (S.simpleObject i ≅ 𝟙_ C) := by
  obtain ⟨i, ⟨e⟩⟩ := S.simple_isomorphic_representative (𝟙_ C)
  exact ⟨i, ⟨e.symm⟩⟩

/-- A chosen label for the actual tensor unit. -/
def unitLabel [Simple (𝟙_ C)] : ι := Classical.choose S.exists_unit_label

/-- The chosen tensor unit label is identified by an actual isomorphism. -/
def unitIso [Simple (𝟙_ C)] : S.simpleObject S.unitLabel ≅ 𝟙_ C :=
  Classical.choice (Classical.choose_spec S.exists_unit_label)

/-- The actual tensor-product multiplicity of three chosen simple objects. -/
def fusionCoeff (i j k : ι) : ℕ :=
  S.multiplicity (S.simpleObject i ⊗ S.simpleObject j) k

/-- Tensoring an arbitrary object on the right distributes its categorical
multiplicities across the chosen simple decomposition. -/
theorem multiplicity_tensor_right (X Y : C) (k : ι) :
    S.multiplicity (X ⊗ Y) k =
      ∑ i, S.multiplicity X i * S.multiplicity (S.simpleObject i ⊗ Y) k :=
  S.multiplicity_map S (tensorRight Y) X k

/-- Tensoring on the left has the corresponding actual multiplicity formula. -/
theorem multiplicity_tensor_left (X Y : C) (k : ι) :
    S.multiplicity (X ⊗ Y) k =
      ∑ j, S.multiplicity Y j * S.multiplicity (X ⊗ S.simpleObject j) k :=
  S.multiplicity_map S (tensorLeft X) Y k

/-- Full bilinear tensor-product multiplicity formula, derived from actual
biproducts and the additive tensor functors. -/
theorem multiplicity_tensor (X Y : C) (k : ι) :
    S.multiplicity (X ⊗ Y) k =
      ∑ i, ∑ j, S.multiplicity X i * S.multiplicity Y j * S.fusionCoeff i j k := by
  rw [S.multiplicity_tensor_right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [S.multiplicity_tensor_left]
  simp only [Finset.mul_sum, Nat.mul_assoc, fusionCoeff]

omit [MonoidalPreadditive C] in
/-- The tensor unit law on actual fusion coefficients. The unit label is
identified by an actual object isomorphism. -/
theorem fusionCoeff_one_left (one : ι) (e : S.simpleObject one ≅ 𝟙_ C) (i k : ι) :
    S.fusionCoeff one i k = if i = k then 1 else 0 := by
  unfold fusionCoeff
  rw [S.multiplicity_iso ((e ⊗ᵢ Iso.refl _) ≪≫ (λ_ (S.simpleObject i))),
    S.multiplicity_simple]
  simp only [eq_comm]

omit [MonoidalPreadditive C] in
/-- The right tensor unit law on actual fusion coefficients. -/
theorem fusionCoeff_one_right (one : ι) (e : S.simpleObject one ≅ 𝟙_ C) (i k : ι) :
    S.fusionCoeff i one k = if i = k then 1 else 0 := by
  unfold fusionCoeff
  rw [S.multiplicity_iso ((Iso.refl _ ⊗ᵢ e) ≪≫ (ρ_ (S.simpleObject i))),
    S.multiplicity_simple]
  simp only [eq_comm]

/-- Associativity of actual fusion coefficients is a consequence of the
categorical associator and the decomposition theorems. -/
theorem fusionCoeff_assoc (i j k l : ι) :
    (∑ p, S.fusionCoeff i j p * S.fusionCoeff p k l) =
      ∑ p, S.fusionCoeff j k p * S.fusionCoeff i p l := by
  calc
    _ = S.multiplicity ((S.simpleObject i ⊗ S.simpleObject j) ⊗ S.simpleObject k) l :=
      (S.multiplicity_tensor_right _ _ _).symm
    _ = S.multiplicity (S.simpleObject i ⊗ (S.simpleObject j ⊗ S.simpleObject k)) l :=
      S.multiplicity_iso (α_ _ _ _) l
    _ = _ := S.multiplicity_tensor_left _ _ _

end Tensor

section MonoidalFunctor

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalPreadditive D]
  (F : C ⥤ D) [F.Additive] [F.Monoidal]

omit [Linear ℂ C] [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalPreadditive D] [F.Additive] in
/-- Unit preservation on multiplicities follows from the actual monoidal
functor unit isomorphism. -/
theorem imageCoeff_one (oneC : ι) (oneD : κ)
    (eC : S.simpleObject oneC ≅ 𝟙_ C) (eD : T.simpleObject oneD ≅ 𝟙_ D) (j : κ) :
    S.imageCoeff T F oneC j = if j = oneD then 1 else 0 := by
  unfold imageCoeff
  rw [T.multiplicity_iso
    (F.mapIso eC ≪≫ (Functor.Monoidal.εIso F).symm ≪≫ eD.symm), T.multiplicity_simple]

/-- Tensor preservation on multiplicities is derived from the actual
monoidal functor tensor comparison isomorphism. -/
theorem imageCoeff_tensor (i i' : ι) (j : κ) :
    (∑ z, S.fusionCoeff i i' z * S.imageCoeff T F z j) =
      ∑ a, ∑ b, S.imageCoeff T F i a * S.imageCoeff T F i' b * T.fusionCoeff a b j := by
  calc
    _ = T.multiplicity (F.obj (S.simpleObject i ⊗ S.simpleObject i')) j :=
      (S.multiplicity_map T F _ j).symm
    _ = T.multiplicity (F.obj (S.simpleObject i) ⊗ F.obj (S.simpleObject i')) j :=
      T.multiplicity_iso (Functor.Monoidal.μIso F _ _).symm j
    _ = _ := T.multiplicity_tensor _ _ j

end MonoidalFunctor

end FiniteSemisimpleSkeleton
end Paper18.Category

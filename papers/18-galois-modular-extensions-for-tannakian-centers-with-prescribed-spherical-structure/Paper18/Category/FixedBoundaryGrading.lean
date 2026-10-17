import Paper18.Category.InvertibleMonodromy
import Paper18.Results.AppendixA

/-!
# Actual homogeneous subcategories of an involutive tensor character

Degrees are properties of actual objects, defined by equality of actual
natural-transformation components. Orthogonality, tensor closure, and
complete homogeneous biproduct decompositions are derived categorically.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.FixedBoundary

def paritySign (g : ZMod 2) : ℂ := if g = 0 then 1 else -1

@[simp] theorem paritySign_zero : paritySign 0 = 1 := by simp [paritySign]
@[simp] theorem paritySign_one : paritySign 1 = -1 := by simp [paritySign]

theorem paritySign_add (g h : ZMod 2) : paritySign (g + h) = paritySign g * paritySign h := by
  have hh : (1 : ZMod 2) + 1 = 0 := by decide
  rcases Paper18.ZMod.two_eq_zero_or_one g with rfl | rfl <;>
    rcases Paper18.ZMod.two_eq_zero_or_one h with rfl | rfl <;> simp [paritySign, hh]

theorem paritySign_injective : Function.Injective paritySign := by
  intro g h he
  rcases Paper18.ZMod.two_eq_zero_or_one g with rfl | rfl <;>
    rcases Paper18.ZMod.two_eq_zero_or_one h with rfl | rfl <;> norm_num [paritySign] at *

section Homogeneous
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  (χ : 𝟭 C ≅ 𝟭 C)

/-- An actual object is homogeneous when the actual character component
equals its degree's scalar identity. -/
def Homogeneous (g : ZMod 2) (X : C) : Prop := χ.hom.app X = paritySign g • 𝟙 X

/-- The actual full category of objects of one specified degree. -/
abbrev HomogeneousCategory (g : ZMod 2) := ObjectProperty.FullSubcategory (Homogeneous χ g)

theorem homogeneous_iso {g : ZMod 2} {X Y : C} (e : X ≅ Y)
    (hY : Homogeneous χ g Y) : Homogeneous χ g X := by
  apply (cancel_mono e.hom).mp
  have hn := χ.hom.naturality e.hom
  change e.hom ≫ χ.hom.app Y = χ.hom.app X ≫ e.hom at hn
  rw [hY] at hn
  simpa [Homogeneous] using hn.symm

/-- Morphisms between different homogeneous degrees vanish. -/
theorem homogeneous_hom_zero {g h : ZMod 2} (hne : g ≠ h) {X Y : C}
    (hX : Homogeneous χ g X) (hY : Homogeneous χ h Y) (f : X ⟶ Y) : f = 0 := by
  by_contra hf
  have hn := χ.hom.naturality f
  change f ≫ χ.hom.app Y = χ.hom.app X ≫ f at hn
  rw [hX, hY] at hn
  have hs : paritySign g = paritySign h := smul_left_injective ℂ hf (by simpa using hn.symm)
  exact hne (paritySign_injective hs)

variable [HasFiniteBiproducts C]

/-- An actual finite biproduct of objects of one degree has that degree. -/
theorem homogeneous_biproduct {J : Type*} [Fintype J] (f : J → C) (g : ZMod 2)
    (hf : ∀ j, Homogeneous χ g (f j)) : Homogeneous χ g (⨁ f) := by
  apply biproduct.hom_ext
  intro j
  have hn := χ.hom.naturality (biproduct.π f j)
  change biproduct.π f j ≫ χ.hom.app (f j) = χ.hom.app (⨁ f) ≫ biproduct.π f j at hn
  rw [hf j] at hn
  simpa [Homogeneous] using hn.symm

variable [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [NatTrans.IsMonoidal χ.hom]

omit [HasFiniteBiproducts C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- The actual tensor unit has neutral degree. -/
theorem homogeneous_unit : Homogeneous χ 0 (𝟙_ C) := by
  rw [Homogeneous, paritySign_zero, one_smul]
  exact TensorAutomorphism.unit_component χ

omit [HasFiniteBiproducts C] in
/-- Tensoring actual homogeneous objects adds their degrees. -/
theorem homogeneous_tensor {g h : ZMod 2} {X Y : C}
    (hX : Homogeneous χ g X) (hY : Homogeneous χ h Y) : Homogeneous χ (g + h) (X ⊗ Y) := by
  rw [Homogeneous, TensorAutomorphism.tensor_component, hX, hY, paritySign_add]
  simp [MonoidalCategory.tensorHom_def, smul_smul, mul_comm]

end Homogeneous

section Completeness
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  (χ : 𝟭 C ≅ 𝟭 C) (hχ : ∀ X : C, χ.hom.app X ≫ χ.hom.app X = 𝟙 X)

omit [HasFiniteBiproducts C] in
include hχ in
/-- Involutivity forces every actual simple object to have a degree. -/
theorem simple_homogeneous (X : C) [Simple X] : ∃ g : ZMod 2, Homogeneous χ g X := by
  let c := TensorAutomorphism.scalar χ X
  have hc : c • 𝟙 X = χ.hom.app X := TensorAutomorphism.scalar_spec χ X
  have hs : c * c = 1 := by
    apply smul_left_injective ℂ (CategoryTheory.id_nonzero X)
    calc
      (c * c) • 𝟙 X = (c • 𝟙 X) ≫ (c • 𝟙 X) := by simp [smul_smul]
      _ = 𝟙 X := by rw [hc]; exact hχ X
      _ = (1 : ℂ) • 𝟙 X := (one_smul ℂ (𝟙 X)).symm
  rcases mul_self_eq_one_iff.mp hs with hp | hm
  · refine ⟨0, ?_⟩
    change χ.hom.app X = paritySign 0 • 𝟙 X
    rw [← hc, hp, paritySign_zero]
  · refine ⟨1, ?_⟩
    change χ.hom.app X = paritySign 1 • 𝟙 X
    rw [← hc, hm, paritySign_one]

variable {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

include S hχ in
/-- Every actual object has an actual finite biproduct decomposition into
homogeneous simple objects. The grading is not external numerical data. -/
theorem exists_homogeneous_decomposition (X : C) :
    ∃ (n : ℕ) (Y : Fin n → C) (g : Fin n → ZMod 2),
      (∀ j, Simple (Y j) ∧ Homogeneous χ (g j) (Y j)) ∧ Nonempty (X ≅ ⨁ Y) := by
  let Y : Fin (S.length X) → C := fun j => S.simpleObject (S.label X j)
  have hy (j : Fin (S.length X)) : ∃ g : ZMod 2, Homogeneous χ g (Y j) :=
    simple_homogeneous χ hχ (Y j)
  choose g hg using hy
  exact ⟨S.length X, Y, g, fun j => ⟨S.simple _, hg j⟩, ⟨S.decomposition X⟩⟩

end Completeness
end Paper18.Category.FixedBoundary

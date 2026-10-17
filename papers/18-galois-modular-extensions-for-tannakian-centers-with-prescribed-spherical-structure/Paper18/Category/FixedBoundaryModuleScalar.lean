import Paper18.Category.FixedBoundaryModuleRegular
import Paper18.Category.TensorCharacters

/-!
# Actual scalar module transformations

A module endomorphism of a regular-module functor is determined by its
component at the tensor unit. When that component acts on a simple object,
Schur's lemma yields a unique actual complex scalar. For natural
automorphisms the scalar is an actual unit of ℂ.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u
namespace Paper18.Category.ModuleFunctor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] (F : C ⥤ C) [F.LeftLinear C]

/-- An actual scalar natural endomorphism of the original functor. -/
def scalarTransformation (c : ℂ) : F ⟶ F where
  app X := c • 𝟙 (F.obj X)
  naturality f := by simp

instance scalarTransformation_moduleNatural (c : ℂ) :
    IsModuleNatural C (scalarTransformation F c) where
  lineator X Y := by
    change Functor.LaxLeftLinear.μₗ F X Y ≫ (c • 𝟙 (F.obj (X ⊗ Y))) =
      (X ◁ (c • 𝟙 (F.obj Y))) ≫ Functor.LaxLeftLinear.μₗ F X Y
    simp

variable [Simple (F.obj (𝟙_ C))]
  [FiniteDimensional ℂ (F.obj (𝟙_ C) ⟶ F.obj (𝟙_ C))]

/-- The Schur scalar of the actual unit component. -/
def moduleScalar (τ : F ⟶ F) : ℂ := simpleScalarEquiv (F.obj (𝟙_ C)) (τ.app (𝟙_ C))

/-- A module natural transformation is its actual Schur scalar on every
object, not only on simple objects or on a chosen skeleton. -/
theorem moduleNatEnd_eq_scalar (τ : F ⟶ F) [IsModuleNatural C τ] (X : C) :
    τ.app X = moduleScalar F τ • 𝟙 (F.obj X) := by
  have h : τ = scalarTransformation F (moduleScalar F τ) := by
    apply moduleNatTrans_ext
    exact (simpleScalarEquiv_spec (F.obj (𝟙_ C)) (τ.app (𝟙_ C))).symm
  exact congrArg (fun σ : F ⟶ F => σ.app X) h

/-- The actual scalar is unique, because the actual unit image is simple. -/
theorem moduleScalar_unique (τ : F ⟶ F) (c : ℂ)
    (h : ∀ X : C, τ.app X = c • 𝟙 (F.obj X)) : moduleScalar F τ = c := by
  unfold moduleScalar
  rw [h, simpleScalarEquiv_smul_id]

/-- For an actual module natural automorphism, its actual scalar is
nonzero. This supplies the ℂˣ coefficient group used in the obstruction
calculation from categorical data. -/
theorem moduleScalar_ne_zero (τ : F ≅ F) [IsModuleNatural C τ.hom] :
    moduleScalar F τ.hom ≠ 0 := by
  intro hz
  have hh := τ.hom_inv_id_app (𝟙_ C)
  rw [moduleNatEnd_eq_scalar F τ.hom (𝟙_ C), hz, zero_smul, zero_comp] at hh
  exact CategoryTheory.id_nonzero (F.obj (𝟙_ C)) hh.symm

/-- The actual scalar unit represented by a module natural automorphism. -/
def moduleScalarUnit (τ : F ≅ F) [IsModuleNatural C τ.hom] : ℂˣ :=
  Units.mk0 (moduleScalar F τ.hom) (moduleScalar_ne_zero F τ)

@[simp] theorem moduleScalarUnit_spec (τ : F ≅ F) [IsModuleNatural C τ.hom] (X : C) :
    τ.hom.app X = (moduleScalarUnit F τ : ℂ) • 𝟙 (F.obj X) :=
  moduleNatEnd_eq_scalar F τ.hom X

/-- Categorical module automorphisms have unique actual scalar-unit
coordinates. No scalar-coordinate classification is assumed as a field. -/
theorem exists_unique_moduleScalarUnit (τ : F ≅ F) [IsModuleNatural C τ.hom] :
    ∃! z : ℂˣ, ∀ X : C, τ.hom.app X = (z : ℂ) • 𝟙 (F.obj X) := by
  refine ⟨moduleScalarUnit F τ, moduleScalarUnit_spec F τ, ?_⟩
  intro z hz
  apply Units.ext
  exact (moduleScalar_unique F τ.hom (z : ℂ) hz).symm

end Paper18.Category.ModuleFunctor

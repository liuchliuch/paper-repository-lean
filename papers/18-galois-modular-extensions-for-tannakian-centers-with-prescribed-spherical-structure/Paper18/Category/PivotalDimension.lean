import Paper18.Category.PivotalDuality
import Paper18.Category.RigidMultiplicity

/-!
# Scalars and dimensions from actual pivotal traces

The scalar of an endomorphism of the unit is extracted using Schur's lemma.
It is not supplied as extra dimension data. Finite semisimplicity supplies
nondegeneracy of the composition pairing used to prove nonvanishing on simples.
-/

noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category

attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [MonoidalCategory C] [Simple (𝟙_ C)]
  [FiniteDimensional ℂ (𝟙_ C ⟶ 𝟙_ C)]

/-- Schur's canonical scalar identification of the actual endomorphisms of a
simple unit. Its inverse sends `c` to `c • 𝟙`. -/
def unitScalarEquiv : (𝟙_ C ⟶ 𝟙_ C) ≃ₗ[ℂ] ℂ :=
  (LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton ℂ (𝟙_ C ⟶ 𝟙_ C) (𝟙 (𝟙_ C)))
    ⟨smul_left_injective ℂ (CategoryTheory.id_nonzero (𝟙_ C)),
      fun f => CategoryTheory.endomorphism_simple_eq_smul_id ℂ f⟩).symm

@[simp] lemma unitScalarEquiv_smul_id (c : ℂ) :
    unitScalarEquiv (C := C) (c • 𝟙 (𝟙_ C)) = c :=
  (unitScalarEquiv (C := C)).apply_symm_apply c

@[simp] lemma unitScalarEquiv_id : unitScalarEquiv (C := C) (𝟙 (𝟙_ C)) = 1 := by
  simpa using unitScalarEquiv_smul_id (C := C) 1

lemma unitScalarEquiv_spec (f : 𝟙_ C ⟶ 𝟙_ C) :
    unitScalarEquiv (C := C) f • 𝟙 (𝟙_ C) = f :=
  (unitScalarEquiv (C := C)).symm_apply_apply f

variable [RightRigidCategory C]

namespace PivotalStructure
variable (J : PivotalStructure C)

/-- The right dimension as the scalar of the actual pivotal right trace. -/
def rightDim (X : C) : ℂ := unitScalarEquiv (C := C) (J.rightDimension X)

/-- The left dimension as the scalar of the actual pivotal left trace. -/
def leftDim (X : C) : ℂ := unitScalarEquiv (C := C) (J.leftDimension X)

lemma rightDim_iso {X Y : C} (i : X ≅ Y) : J.rightDim X = J.rightDim Y :=
  congrArg (unitScalarEquiv (C := C)) (J.rightDimension_iso i)

lemma leftDim_iso {X Y : C} (i : X ≅ Y) : J.leftDim X = J.leftDim Y :=
  congrArg (unitScalarEquiv (C := C)) (J.leftDimension_iso i)

lemma leftDim_eq_rightDim (h : J.Spherical) (X : C) : J.leftDim X = J.rightDim X :=
  congrArg (unitScalarEquiv (C := C)) (h X (𝟙 X))

/-- Categorical duality exchanges the extracted right and left dimensions. -/
lemma rightDim_dual (X : C) : J.rightDim (dual C X) = J.leftDim X :=
  congrArg (unitScalarEquiv (C := C)) (J.rightDimension_dual X)

lemma rightDim_dual_of_spherical (h : J.Spherical) (X : C) :
    J.rightDim (dual C X) = J.rightDim X := by
  rw [J.rightDim_dual, J.leftDim_eq_rightDim h]

variable [MonoidalPreadditive C] [MonoidalLinear ℂ C]

lemma rightTrace_smul {X : C} (c : ℂ) (f : X ⟶ X) :
    J.rightTrace (c • f) = c • J.rightTrace f := by
  simp [rightTrace]

lemma leftTrace_smul {X : C} (c : ℂ) (f : X ⟶ X) :
    J.leftTrace (c • f) = c • J.leftTrace f := by
  simp [leftTrace]

/-- The actual right trace is a complex linear map. -/
def rightTraceLinearMap (X : C) : (X ⟶ X) →ₗ[ℂ] (𝟙_ C ⟶ 𝟙_ C) where
  toFun := J.rightTrace
  map_add' := J.rightTrace_add
  map_smul' := J.rightTrace_smul

/-- The actual left trace is a complex linear map. -/
def leftTraceLinearMap (X : C) : (X ⟶ X) →ₗ[ℂ] (𝟙_ C ⟶ 𝟙_ C) where
  toFun := J.leftTrace
  map_add' := J.leftTrace_add
  map_smul' := J.leftTrace_smul

/-- On a simple object, the trace of any endomorphism is its Schur scalar times
the categorical dimension. -/
lemma rightTrace_smul_id (X : C) (c : ℂ) :
    unitScalarEquiv (C := C) (J.rightTrace (c • 𝟙 X)) = c * J.rightDim X := by
  simp [J.rightTrace_smul, rightDim, rightDimension]

lemma leftTrace_smul_id (X : C) (c : ℂ) :
    unitScalarEquiv (C := C) (J.leftTrace (c • 𝟙 X)) = c * J.leftDim X := by
  simp [J.leftTrace_smul, leftDim, leftDimension]

/-- Tensor multiplicativity is derived from the categorical closure identity
and linearity of tensor product, rather than included as a dimension field. -/
lemma rightDim_tensor (X Y : C) : J.rightDim (X ⊗ Y) = J.rightDim X * J.rightDim Y := by
  have hy : J.rightDimension Y = J.rightDim Y • 𝟙 (𝟙_ C) :=
    (unitScalarEquiv_spec (J.rightDimension Y)).symm
  change unitScalarEquiv (C := C) (J.rightDimension (X ⊗ Y)) = _
  rw [J.rightDimension_tensor_nested, hy]
  simp [rightDim, rightDimension, rightTrace, mul_comm]

/-- Additivity of the actual pivotal dimension on arbitrary finite biproducts. -/
lemma rightDim_biproduct {κ : Type} [Fintype κ] [HasFiniteBiproducts C] (Y : κ → C) :
    J.rightDim (⨁ Y) = ∑ a, J.rightDim (Y a) := by
  have ht := J.rightTrace_of_resolution Y (biproduct.ι Y) (biproduct.π Y)
    biproduct.total (𝟙 (⨁ Y))
  simp only [id_comp, biproduct.ι_π_self] at ht
  simpa only [rightDim, rightDimension, map_sum] using
    congrArg (unitScalarEquiv (C := C)) ht

end PivotalStructure

namespace FiniteSemisimpleSkeleton
variable [HasFiniteBiproducts C] {ι : Type w} [Fintype ι]
variable (S : FiniteSemisimpleSkeleton C ι)
include S

/-- In a finite semisimple category, every nonzero morphism onto a simple
object admits a section. The section is constructed from an actual simple
summand of the source decomposition. -/
lemma section_of_nonzero_to_simple {X Y : C} [Simple X] (f : Y ⟶ X) (hf : f ≠ 0) :
    ∃ s : X ⟶ Y, s ≫ f = 𝟙 X := by
  let Z := fun a : Fin (S.length Y) => S.simpleObject (S.label Y a)
  let e := S.decomposition Y
  have hg : e.inv ≫ f ≠ 0 := by
    intro h
    apply hf
    simpa using congrArg (fun k => e.hom ≫ k) h
  have hex : ∃ a, biproduct.ι Z a ≫ e.inv ≫ f ≠ 0 := by
    by_contra h
    apply hg
    apply biproduct.hom_ext'
    intro a
    simpa only [not_not, assoc, comp_zero] using not_exists.mp h a
  obtain ⟨a, ha⟩ := hex
  let g : Z a ⟶ X := biproduct.ι Z a ≫ e.inv ≫ f
  have hg' : g ≠ 0 := ha
  letI : Simple (Z a) := S.simple (S.label Y a)
  letI := CategoryTheory.isIso_of_hom_simple hg'
  refine ⟨inv g ≫ biproduct.ι Z a ≫ e.inv, ?_⟩
  simpa only [assoc] using IsIso.inv_hom_id g

/-- Nonzero cup and cap cannot compose to zero when the corresponding Hom
space is one-dimensional. This is derived from actual semisimplicity. -/
lemma comp_ne_zero_of_finrank_one {X Y : C} [Simple X]
    [FiniteDimensional ℂ (X ⟶ Y)] (hd : Module.finrank ℂ (X ⟶ Y) = 1)
    (f : X ⟶ Y) (g : Y ⟶ X) (hf : f ≠ 0) (hg : g ≠ 0) : f ≫ g ≠ 0 := by
  obtain ⟨s, hs⟩ := S.section_of_nonzero_to_simple g hg
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' f hf).mp hd s
  intro hfg
  have hzero : s ≫ g = 0 := by rw [← hc, Linear.smul_comp, hfg, smul_zero]
  exact CategoryTheory.id_nonzero X (hs.symm.trans hzero)

end FiniteSemisimpleSkeleton

section Nonvanishing
variable [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι]

/-- The cup of a simple object cannot vanish, by the snake identity. -/
lemma exactPairing_coevaluation_ne_zero (X Y : C) [ExactPairing X Y] [Simple X] :
    η_ X Y ≠ 0 := by
  intro hz
  have ht := ExactPairing.evaluation_coevaluation X Y
  rw [hz] at ht
  have hh := congrArg (fun k => (λ_ X).inv ≫ k ≫ (ρ_ X).hom) ht
  exact CategoryTheory.id_nonzero X (by simpa using hh.symm)

/-- The cap of a simple object cannot vanish, by the other snake identity. -/
lemma exactPairing_evaluation_ne_zero (X Y : C) [ExactPairing X Y] [Simple Y] :
    ε_ X Y ≠ 0 := by
  intro hz
  have ht := ExactPairing.coevaluation_evaluation X Y
  rw [hz] at ht
  have hh := congrArg (fun k => (ρ_ Y).inv ≫ k ≫ (λ_ Y).hom) ht
  exact CategoryTheory.id_nonzero Y (by simpa using hh.symm)

/-- Rigidity and Schur's lemma imply the cup space of a simple is one-dimensional. -/
lemma finrank_unit_to_simple_tensor_dual (X : C) [Simple X] :
    Module.finrank ℂ (𝟙_ C ⟶ X ⊗ dual C X) = 1 := by
  calc
    _ = Module.finrank ℂ ((𝟙_ C) ⊗ X ⟶ X) :=
      (tensorRightHomLinearEquiv (𝟙_ C) X (dual C X) X).finrank_eq.symm
    _ = Module.finrank ℂ (X ⟶ X) := finrank_hom_iso (λ_ X) (Iso.refl X)
    _ = 1 := CategoryTheory.finrank_endomorphism_simple_eq_one ℂ X

namespace PivotalStructure
variable (J : PivotalStructure C) (S : FiniteSemisimpleSkeleton C ι)
include S

/-- Nonvanishing of the actual pivotal dimension of a simple object, derived
from the one-dimensional cup space and semisimple composition, not assumed. -/
lemma rightDim_ne_zero (X : C) [Simple X] : J.rightDim X ≠ 0 := by
  have he : J.leftEvaluation X ≠ 0 := by
    letI := J.leftExactPairing X
    exact exactPairing_evaluation_ne_zero (dual C X) X
  have htr : J.rightDimension X ≠ 0 := by
    simpa only [rightDimension, rightTrace, id_whiskerRight, id_comp] using
      S.comp_ne_zero_of_finrank_one (finrank_unit_to_simple_tensor_dual X)
        (η_ X (dual C X)) (J.leftEvaluation X)
        (exactPairing_coevaluation_ne_zero X (dual C X)) he
  intro hz
  apply htr
  apply (unitScalarEquiv (C := C)).injective
  simpa only [rightDim, map_zero] using hz

/-- The unit dimension is forced to be one by multiplicativity, the unit
isomorphism, and the proved nonvanishing of its actual trace. -/
lemma rightDim_unit : J.rightDim (𝟙_ C) = 1 := by
  have hn := J.rightDim_ne_zero S (𝟙_ C)
  have hm := J.rightDim_tensor (𝟙_ C) (𝟙_ C)
  rw [J.rightDim_iso (λ_ (𝟙_ C))] at hm
  apply mul_left_cancel₀ hn
  simpa only [mul_one] using hm.symm

end PivotalStructure
end Nonvanishing

end Paper18.Category

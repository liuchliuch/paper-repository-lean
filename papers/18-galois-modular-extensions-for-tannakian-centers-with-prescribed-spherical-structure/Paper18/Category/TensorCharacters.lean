import Paper18.Category.FusionCategory
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Characters extracted from actual tensor automorphisms

The scalars are obtained by Schur's lemma from the components of a monoidal
natural automorphism of the identity. The unit, nonvanishing, and fusion
constituent multiplication laws are proved from its categorical coherence.
-/

noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category

section Schur
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [HasKernels C]

/-- The scalar of an actual endomorphism of a simple object. -/
def simpleScalarEquiv (X : C) [Simple X] [FiniteDimensional ℂ (X ⟶ X)] :
    (X ⟶ X) ≃ₗ[ℂ] ℂ :=
  (LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton ℂ (X ⟶ X) (𝟙 X))
    ⟨smul_left_injective ℂ (CategoryTheory.id_nonzero X),
      fun f => CategoryTheory.endomorphism_simple_eq_smul_id ℂ f⟩).symm

@[simp] lemma simpleScalarEquiv_smul_id (X : C) [Simple X]
    [FiniteDimensional ℂ (X ⟶ X)] (c : ℂ) :
    simpleScalarEquiv X (c • 𝟙 X) = c :=
  (simpleScalarEquiv X).apply_symm_apply c

lemma simpleScalarEquiv_spec (X : C) [Simple X] [FiniteDimensional ℂ (X ⟶ X)]
    (f : X ⟶ X) : simpleScalarEquiv X f • 𝟙 X = f :=
  (simpleScalarEquiv X).symm_apply_apply f

end Schur

namespace TensorAutomorphism
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [HasKernels C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  (a : 𝟭 C ≅ 𝟭 C)

/-- Schur scalar of the actual component at a simple object. -/
def scalar (X : C) [Simple X] : ℂ := simpleScalarEquiv X (a.hom.app X)

@[simp] lemma scalar_refl (X : C) [Simple X] :
    scalar (Iso.refl (𝟭 C)) X = 1 := by
  change simpleScalarEquiv X (𝟙 X) = 1
  simpa using simpleScalarEquiv_smul_id X (1 : ℂ)

lemma scalar_spec (X : C) [Simple X] : (scalar a) X • 𝟙 X = a.hom.app X :=
  simpleScalarEquiv_spec X (a.hom.app X)

lemma scalar_ne_zero (X : C) [Simple X] : (scalar a) X ≠ 0 := by
  intro h
  have hz : a.hom.app X = 0 := by rw [← (scalar_spec a) X, h, zero_smul]
  exact CategoryTheory.id_nonzero X (by
    simpa [hz] using (a.app X).hom_inv_id.symm)

lemma inv_scalar (X : C) [Simple X] : (scalar a.symm) X = ((scalar a) X)⁻¹ := by
  have hh : (scalar a) X * (scalar a.symm) X = 1 := by
    apply smul_left_injective ℂ (CategoryTheory.id_nonzero X)
    calc
      ((scalar a) X * (scalar a.symm) X) • 𝟙 X =
          ((scalar a) X • 𝟙 X) ≫ ((scalar a.symm) X • 𝟙 X) := by simp [smul_smul, mul_comm]
      _ = 𝟙 X := by rw [(scalar_spec a) X, (scalar_spec a.symm) X]; exact a.hom_inv_id_app X
      _ = (1 : ℂ) • 𝟙 X := by simp
  exact ((mul_eq_one_iff_inv_eq₀ (scalar_ne_zero a X)).mp hh).symm

lemma scalar_iso {X Y : C} [Simple X] [Simple Y] (e : X ≅ Y) :
    (scalar a) X = (scalar a) Y := by
  apply smul_left_injective ℂ (show e.hom ≠ 0 from by
    intro h
    exact CategoryTheory.id_nonzero X (by simpa [h] using e.hom_inv_id.symm))
  have hn := a.hom.naturality e.hom
  rw [← scalar_spec a X, ← scalar_spec a Y] at hn
  simpa using hn.symm

/-- Components on actual simple representatives determine the whole natural
automorphism, by the actual biproduct decompositions. -/
lemma ext_simple [HasFiniteBiproducts C] {ι : Type w} [Fintype ι]
    (b : 𝟭 C ≅ 𝟭 C) (S : FiniteSemisimpleSkeleton C ι)
    (h : ∀ i, scalar a (S.simpleObject i) = scalar b (S.simpleObject i)) : a = b := by
  ext X
  let e := S.decomposition X
  apply (cancel_mono e.hom).1
  apply biproduct.hom_ext
  intro j
  let f := e.hom ≫ biproduct.π (fun k => S.simpleObject (S.label X k)) j
  have hs : a.hom.app (S.simpleObject (S.label X j)) =
      b.hom.app (S.simpleObject (S.label X j)) := by
    rw [← scalar_spec a, ← scalar_spec b, h]
  calc
    (a.hom.app X ≫ e.hom) ≫ biproduct.π _ j = a.hom.app X ≫ f := assoc _ _ _
    _ = f ≫ a.hom.app (S.simpleObject (S.label X j)) := (a.hom.naturality f).symm
    _ = f ≫ b.hom.app (S.simpleObject (S.label X j)) := by rw [hs]
    _ = (b.hom.app X ≫ e.hom) ≫ biproduct.π _ j := by
      simpa only [f, assoc, Functor.id_map] using b.hom.naturality f

variable [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [NatTrans.IsMonoidal a.hom]

omit [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
lemma unit_component : a.hom.app (𝟙_ C) = 𝟙 (𝟙_ C) := by
  simpa using (NatTrans.IsMonoidal.unit (τ := a.hom))

omit [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
lemma tensor_component (X Y : C) :
    a.hom.app (X ⊗ Y) = a.hom.app X ⊗ₘ a.hom.app Y := by
  simpa using (NatTrans.IsMonoidal.tensor (τ := a.hom) X Y)

lemma scalar_unit [Simple (𝟙_ C)] : (scalar a) (𝟙_ C) = 1 := by
  unfold scalar
  rw [unit_component a]
  simpa using simpleScalarEquiv_smul_id (𝟙_ C) (1 : ℂ)

/-- The component on a tensor product of simples is forced by monoidality. -/
lemma tensor_component_simple (X Y : C) [Simple X] [Simple Y] :
    a.hom.app (X ⊗ Y) = ((scalar a) X * (scalar a) Y) • 𝟙 (X ⊗ Y) := by
  rw [(tensor_component a), ← (scalar_spec a) X, ← (scalar_spec a) Y]
  simp [tensorHom_def, smul_smul, mul_comm]

/-- Every actual simple constituent carries the product scalar. -/
lemma scalar_of_nonzero_hom (X Y Z : C) [Simple X] [Simple Y] [Simple Z]
    (f : Z ⟶ X ⊗ Y) (hf : f ≠ 0) : (scalar a) Z = (scalar a) X * (scalar a) Y := by
  apply smul_left_injective ℂ hf
  have hn := a.hom.naturality f
  rw [← scalar_spec a Z, tensor_component_simple a X Y] at hn
  simpa using hn.symm

variable [HasFiniteBiproducts C] {ι : Type w} [Fintype ι]
  (S : FiniteSemisimpleSkeleton C ι)

/-- The fusion coefficient is the dimension of an actual Hom space, so its
positivity produces the morphism to which naturality applies. -/
lemma scalar_fusion (i j k : ι) (h : 0 < S.fusionCoeff i j k) :
    (scalar a) (S.simpleObject k) = (scalar a) (S.simpleObject i) * (scalar a) (S.simpleObject j) := by
  obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h
  exact (scalar_of_nonzero_hom a) (S.simpleObject i) (S.simpleObject j) (S.simpleObject k) f hf

variable [RightRigidCategory C] [Simple (𝟙_ C)]

omit [RightRigidCategory C] in
lemma scalar_unitLabel : (scalar a) (S.simpleObject S.unitLabel) = 1 := by
  rw [(scalar_iso a) S.unitIso, (scalar_unit a)]

/-- Dual inversion follows from the actual unit constituent of `X ⊗ X*`. -/
lemma scalar_dualLabel (i : ι) :
    (scalar a) (S.simpleObject (S.dualLabel i)) = ((scalar a) (S.simpleObject i))⁻¹ := by
  have hunit : S.fusionCoeff i (S.dualLabel i) S.unitLabel = 1 := by
    have h := S.fusionCoeff_right i (S.dualLabel i) S.unitLabel
    rw [S.dualLabel_involutive] at h
    rw [S.fusionCoeff_one_left S.unitLabel S.unitIso] at h
    simpa using h
  have hm := (scalar_fusion a) S i (S.dualLabel i) S.unitLabel (by omega)
  rw [(scalar_unitLabel a) S] at hm
  exact ((mul_eq_one_iff_inv_eq₀ (scalar_ne_zero a (S.simpleObject i))).mp hm.symm).symm

end TensorAutomorphism
end Paper18.Category

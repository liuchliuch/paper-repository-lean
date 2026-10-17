import Paper18.Category.RelativeTensorCentralFreeHom
import Paper18.Category.LocalModulesCenterLinear
import Paper18.Category.FactorizationFullyFaithfulRotation
import Paper18.Category.SemisimpleSplitting
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Actual full faithfulness of the central free functor

The actual generator comparison injects central free Hom into an ambient
positive-negative Hom. Nondegeneracy and connectedness compute the latter
dimension. An actual splitting of the algebra unit proves faithfulness,
and equality of the actual finite Hom dimensions proves fullness.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory CategoryTheory.Functor.Monoidal
open scoped MonObj
universe v u w
namespace Paper18.Category.RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C] {A : C} [MonObj A] [IsCommMonObj A]

/-- A split algebra unit makes evaluation on the free generators faithful. -/
def centralFreeFunctorFaithfulOfSplitUnit (s : SplitMono (η[A])) :
    (centralFreeFunctor (A := A)).Faithful where
  map_injective {X Y} f g h := by
    have hs : freeUnit (A := A) Y ≫ s.retraction ▷ Y ≫ (λ_ Y).hom = 𝟙 Y := by
      unfold freeUnit
      rw [Category.assoc, ← comp_whiskerRight_assoc, s.id, id_whiskerRight,
        Category.id_comp, Iso.inv_hom_id]
    have hh := congrArg (fun k => freeUnit (A := A) X ≫ k.f.hom) h
    change freeUnit X ≫ (InternalModule.freeMap f).hom =
      freeUnit X ≫ (InternalModule.freeMap g).hom at hh
    rw [freeUnit_naturality, freeUnit_naturality] at hh
    have hh' := congrArg (fun k => k ≫ s.retraction ▷ Y ≫ (λ_ Y).hom) hh
    simpa only [Category.assoc, hs, Category.comp_id] using hh'

section Finite
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton C ι)

omit [BraidedCategory C] [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A]
  [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)] in
/-- Connectedness forces the actual algebra unit to be nonzero. -/
theorem algebraUnit_ne_zero_of_connected
    (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) : η[A] ≠ 0 := by
  intro hη
  have hu := MonObj.one_mul (X := A)
  rw [hη, MonoidalPreadditive.zero_whiskerRight, zero_comp] at hu
  have hid : 𝟙 A = (0 : A ⟶ A) := by
    calc
      𝟙 A = (λ_ A).inv ≫ (λ_ A).hom := (λ_ A).inv_hom_id.symm
      _ = 0 := by rw [← hu, comp_zero]
  have hz (f : 𝟙_ C ⟶ A) : f = 0 := by
    calc
      f = f ≫ 𝟙 A := (Category.comp_id f).symm
      _ = 0 := by rw [hid, comp_zero]
  letI : Subsingleton (𝟙_ C ⟶ A) := ⟨fun f g => (hz f).trans (hz g).symm⟩
  have hf := Module.finrank_zero_of_subsingleton (R := ℂ) (M := (𝟙_ C ⟶ A))
  omega

/-- The actual ambient semisimple splitting of a connected algebra unit. -/
def algebraUnitSplit (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) :
    SplitMono (η[A]) := by
  letI : Mono (η[A]) := CategoryTheory.mono_of_nonzero_from_simple
    (algebraUnit_ne_zero_of_connected (A := A) hconnected)
  exact T.splitMono (η[A])

/-- The actual central free functor for a connected algebra is faithful. -/
def centralFreeFunctorFaithful (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) :
    (centralFreeFunctor (A := A)).Faithful :=
  centralFreeFunctorFaithfulOfSplitUnit (algebraUnitSplit T hconnected)

include T in
omit [HasCoequalizers C] [MonObj A] [IsCommMonObj A] in
/-- Nondegenerate factorization computes the actual ambient comparison Hom. -/
theorem finrank_centralFreeHomAmbient_target (hC : IsNondegenerate (C := C))
    (X Y : C) :
    Module.finrank ℂ ((Drinfeld.positive C).obj X ⟶
      (Drinfeld.negative C).obj A ⊗ (Drinfeld.positive C).obj Y) =
      Module.finrank ℂ (X ⟶ Y) * Module.finrank ℂ (𝟙_ C ⟶ A) := by
  let e : (Drinfeld.positive C).obj X ⊗ (Drinfeld.negative C).obj (𝟙_ C) ≅
      (Drinfeld.positive C).obj X :=
    whiskerLeftIso ((Drinfeld.positive C).obj X) (εIso (Drinfeld.negative C)).symm ≪≫
      (ρ_ ((Drinfeld.positive C).obj X))
  rw [finrank_hom_iso e.symm
    (β_ ((Drinfeld.negative C).obj A) ((Drinfeld.positive C).obj Y))]
  exact Drinfeld.finrank_factorizationHom T hC X Y (𝟙_ C) A

include T in
/-- Central free Hom has the exact ambient Hom dimension. -/
theorem finrank_centralFreeHom (hC : IsNondegenerate (C := C))
    (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) (X Y : C) :
    Module.finrank ℂ ((centralFreeFunctor (A := A)).obj X ⟶
      (centralFreeFunctor (A := A)).obj Y) = Module.finrank ℂ (X ⟶ Y) := by
  letI := centralFreeFunctorFaithful T hconnected
  apply le_antisymm
  · have h := LinearMap.finrank_le_finrank_of_injective
      (f := centralFreeHomAmbientLinear (A := A) X Y) (centralFreeHomAmbient_injective X Y)
    rw [finrank_centralFreeHomAmbient_target T hC X Y, hconnected, mul_one] at h
    exact h
  · exact LinearMap.finrank_le_finrank_of_injective
      (f := (centralFreeFunctor (A := A)).mapLinearMap ℂ)
      (centralFreeFunctor (A := A)).map_injective

/-- The actual central free functor is fully faithful for a connected
commutative algebra in an actual nondegenerate ambient category. -/
def centralFreeFunctorFullyFaithful (hC : IsNondegenerate (C := C))
    (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) :
    (centralFreeFunctor (A := A)).FullyFaithful := by
  letI := centralFreeFunctorFaithful T hconnected
  have hb (X Y : C) : Function.Bijective
      ((centralFreeFunctor (A := A)).map : (X ⟶ Y) → _) := by
    refine ⟨(centralFreeFunctor (A := A)).map_injective, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_centralFreeHom T hC hconnected X Y).symm
      (f := (centralFreeFunctor (A := A)).mapLinearMap ℂ)).mp
      (centralFreeFunctor (A := A)).map_injective
  exact
    { preimage := fun {X Y} f => (Equiv.ofBijective _ (hb X Y)).symm f
      map_preimage := fun {X Y} f => (Equiv.ofBijective _ (hb X Y)).apply_symm_apply f
      preimage_map := fun {X Y} f => (Equiv.ofBijective _ (hb X Y)).symm_apply_apply f }

end Finite
end Paper18.Category.RelativeTensor

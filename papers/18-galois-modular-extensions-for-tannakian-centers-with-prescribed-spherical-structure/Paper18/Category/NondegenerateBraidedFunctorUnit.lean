import Paper18.Category.NondegenerateBraidedFunctorTransparency
import Paper18.Category.DiagonalAlgebraSemisimpleUnit
import Paper18.Category.NondegenerateBasic

/-! # Source nondegeneracy identifies the actual right-adjoint unit -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe v u w v' u'
namespace Paper18.Category.NondegenerateBraidedFunctor
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [BraidedCategory D] [HasFiniteBiproducts D] [HasKernels D]
  [Simple (𝟙_ D)] [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  (F : C ⥤ D) [F.Braided] [F.Additive] [F.Linear ℂ]

/-- Actual source nondegeneracy and connectedness force R(1) to be the
actual tensor unit. Neither conclusion is supplied as a field. -/
theorem semisimpleAdjointUnit_iso (hC : IsNondegenerate (C := C)) :
    Nonempty (DiagonalAlgebra.semisimpleAdjointAlgebra S F ≅ 𝟙_ C) := by
  let adj := DiagonalAlgebra.semisimpleRightAdjunction S F
  have ht : DiagonalAlgebra.semisimpleAdjointAlgebra S F ∈ mugerCenter :=
    adjointUnit_transparent F adj
  obtain ⟨n, ⟨e⟩⟩ := hC _ ht
  have hd := DiagonalAlgebra.semisimpleAdjointAlgebra_connected S F
  rw [finrank_hom_iso (Iso.refl (𝟙_ C)) e, finrank_hom_biproduct] at hd
  have hn : n = 1 := by
    simpa only [CategoryTheory.finrank_endomorphism_simple_eq_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using hd
  subst n
  exact ⟨e ≪≫ biproductUniqueIso (fun _ : Fin 1 => 𝟙_ C)⟩

/-- The actual adjunction transpose of the strong unit comparison. -/
def adjointUnitMap : 𝟙_ C ⟶ DiagonalAlgebra.semisimpleAdjointAlgebra S F :=
  (DiagonalAlgebra.semisimpleRightAdjunction S F).homEquiv _ _ (η F)

@[reassoc]
lemma adjointUnitMap_counit :
    F.map (adjointUnitMap S F) ≫ DiagonalAlgebra.semisimpleAdjointAlgebraCounit S F = η F :=
  ((DiagonalAlgebra.semisimpleRightAdjunction S F).homEquiv _ _).symm_apply_apply _

lemma adjointUnitMap_ne_zero : adjointUnitMap S F ≠ 0 := by
  intro h
  have hz : η F = 0 := by
    rw [← adjointUnitMap_counit S F, h, F.map_zero, zero_comp]
  apply CategoryTheory.id_nonzero (𝟙_ D)
  rw [← Functor.Monoidal.ε_η F, hz, comp_zero]

/-- The actual unit map is an isomorphism, derived by Schur from the
actual unit object isomorphism and its proved nonvanishing. -/
lemma adjointUnitMap_isIso (hC : IsNondegenerate (C := C)) : IsIso (adjointUnitMap S F) := by
  obtain ⟨e⟩ := semisimpleAdjointUnit_iso S F hC
  letI : Simple (DiagonalAlgebra.semisimpleAdjointAlgebra S F) := Simple.of_iso e
  exact CategoryTheory.isIso_of_hom_simple (adjointUnitMap_ne_zero S F)

end Paper18.Category.NondegenerateBraidedFunctor

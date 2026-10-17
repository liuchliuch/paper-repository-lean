import Paper18.Category.DiagonalAlgebraSemisimpleUnit

/-! # Genuine characters transpose to the actual right-adjoint unit algebra

The multiplication and unit equations below follow from the actual
adjunction and its canonical lax monoidal right adjoint. No property of
an eventual Morita equivalence is an input.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped MonObj
universe v u w v' u'
namespace Paper18.Category.GraphPicard.Morita
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [MonoidalCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasFiniteBiproducts D] [MonoidalCategory D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Monoidal]
open DiagonalAlgebra

/-- Transpose an actual character through the constructed adjunction. -/
def characterTranspose {A : C} (q : F.obj A ⟶ 𝟙_ D) :
    A ⟶ semisimpleAdjointAlgebra S F :=
  (semisimpleRightAdjunction S F).homEquiv A (𝟙_ D) q

@[reassoc] lemma characterTranspose_counit {A : C} (q : F.obj A ⟶ 𝟙_ D) :
    F.map (characterTranspose S F q) ≫ semisimpleAdjointAlgebraCounit S F = q := by
  unfold characterTranspose semisimpleAdjointAlgebraCounit
  rw [← (semisimpleRightAdjunction S F).homEquiv_counit]
  exact Equiv.symm_apply_apply _ _

/-- The actual counit detects maps into the right-adjoint unit. -/
lemma adjointUnit_hom_ext {A : C}
    (a b : A ⟶ semisimpleAdjointAlgebra S F)
    (h : F.map a ≫ semisimpleAdjointAlgebraCounit S F =
      F.map b ≫ semisimpleAdjointAlgebraCounit S F) : a = b := by
  apply ((semisimpleRightAdjunction S F).homEquiv A (𝟙_ D)).symm.injective
  simpa only [(semisimpleRightAdjunction S F).homEquiv_counit] using h

variable {A : C} [MonObj A]
local instance mappedAlgebra : MonObj (F.obj A) := Functor.monObjObj (F := F) A

/-- The unit equation is derived by actual adjunction and cancellation
of the genuine strong-monoidal unit comparison. -/
lemma characterTranspose_one (q : F.obj A ⟶ 𝟙_ D) [IsMonHom q] :
    η[A] ≫ characterTranspose S F q = η[semisimpleAdjointAlgebra S F] := by
  apply adjointUnit_hom_ext S F
  rw [Functor.map_comp, Category.assoc, characterTranspose_counit,
    semisimpleAdjointAlgebra_one_counit]
  apply (cancel_epi (ε F)).mp
  have hq := IsMonHom.one_hom q
  change (ε F ≫ F.map η[A]) ≫ q = 𝟙 (𝟙_ D) at hq
  simpa only [Category.assoc, Functor.Monoidal.ε_η] using hq

/-- Multiplicativity is obtained by transposing the genuine character
multiplication equation, using the actual oplax tensor comparison. -/
lemma characterTranspose_mul (q : F.obj A ⟶ 𝟙_ D) [IsMonHom q] :
    μ[A] ≫ characterTranspose S F q =
      (characterTranspose S F q ⊗ₘ characterTranspose S F q) ≫
        μ[semisimpleAdjointAlgebra S F] := by
  apply adjointUnit_hom_ext S F
  simp only [Functor.map_comp, Category.assoc]
  rw [characterTranspose_counit, semisimpleAdjointAlgebra_mul_counit]
  rw [← δ_natural_assoc, tensorHom_comp_tensorHom_assoc,
    characterTranspose_counit]
  apply (cancel_epi (Functor.LaxMonoidal.μ F A A)).mp
  have hq := IsMonHom.mul_hom q
  change (Functor.LaxMonoidal.μ F A A ≫ F.map μ[A]) ≫ q =
    (q ⊗ₘ q) ≫ (λ_ (𝟙_ D)).hom at hq
  simpa only [Category.assoc, Functor.Monoidal.μ_δ_assoc] using hq

/-- A genuine algebra character yields a genuine algebra homomorphism
into the actual right-adjoint unit algebra. -/
instance characterTranspose_isMonHom (q : F.obj A ⟶ 𝟙_ D) [IsMonHom q] :
    IsMonHom (characterTranspose S F q) where
  one_hom := characterTranspose_one S F q
  mul_hom := characterTranspose_mul S F q

end Paper18.Category.GraphPicard.Morita

import Paper18.Category.DiagonalAlgebraSemisimpleAdjoint
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Functor

/-! # Actual right-adjoint unit algebras without rigidity or nondegeneracy premises -/
noncomputable section
set_option maxRecDepth 4000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped MonObj
universe v u w v' u'
namespace Paper18.Category.DiagonalAlgebra
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [MonoidalCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasFiniteBiproducts D] [MonoidalCategory D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Monoidal]

instance semisimpleRightAdjoint_laxMonoidal : (semisimpleRightAdjoint S F).LaxMonoidal :=
  (semisimpleRightAdjunction S F).rightAdjointLaxMonoidal

/-- The actual right-adjoint unit algebra for any finite semisimple
complex-linear strong monoidal functor. -/
def semisimpleAdjointAlgebra : C := (semisimpleRightAdjoint S F).obj (𝟙_ D)

instance semisimpleAdjointAlgebraMonObj : MonObj (semisimpleAdjointAlgebra S F) :=
  Functor.monObjObj (F := semisimpleRightAdjoint S F) (𝟙_ D)

/-- The underlying actual right-adjunction counit. -/
def semisimpleAdjointAlgebraCounit : F.obj (semisimpleAdjointAlgebra S F) ⟶ 𝟙_ D :=
  (semisimpleRightAdjunction S F).counit.app (𝟙_ D)

lemma semisimpleAdjointAlgebra_mul :
    μ[semisimpleAdjointAlgebra S F] =
      (semisimpleRightAdjunction S F).homEquiv _ (𝟙_ D)
        (δ F _ _ ≫ (semisimpleAdjointAlgebraCounit S F ⊗ₘ semisimpleAdjointAlgebraCounit S F) ≫
          (λ_ (𝟙_ D)).hom) := by
  change ((semisimpleRightAdjunction S F).homEquiv _ _
    (δ F _ _ ≫ (semisimpleAdjointAlgebraCounit S F ⊗ₘ semisimpleAdjointAlgebraCounit S F))) ≫
      (semisimpleRightAdjoint S F).map (λ_ (𝟙_ D)).hom = _
  simpa only [Category.assoc] using
    ((semisimpleRightAdjunction S F).homEquiv_naturality_right
      (δ F _ _ ≫ (semisimpleAdjointAlgebraCounit S F ⊗ₘ semisimpleAdjointAlgebraCounit S F))
      (λ_ (𝟙_ D)).hom).symm

lemma semisimpleAdjointAlgebra_one :
    η[semisimpleAdjointAlgebra S F] =
      (semisimpleRightAdjunction S F).homEquiv (𝟙_ C) (𝟙_ D) (Functor.OplaxMonoidal.η F) := by
  change (semisimpleRightAdjunction S F).homEquiv _ _ (Functor.OplaxMonoidal.η F) ≫
    (semisimpleRightAdjoint S F).map (𝟙 (𝟙_ D)) = _
  rw [CategoryTheory.Functor.map_id, comp_id]

lemma semisimpleAdjointAlgebra_mul_counit :
    F.map μ[semisimpleAdjointAlgebra S F] ≫ semisimpleAdjointAlgebraCounit S F =
      δ F _ _ ≫ (semisimpleAdjointAlgebraCounit S F ⊗ₘ semisimpleAdjointAlgebraCounit S F) ≫
        (λ_ (𝟙_ D)).hom := by
  unfold semisimpleAdjointAlgebraCounit
  rw [semisimpleAdjointAlgebra_mul, ← (semisimpleRightAdjunction S F).homEquiv_counit]
  exact Equiv.symm_apply_apply _ _

lemma semisimpleAdjointAlgebra_one_counit :
    F.map η[semisimpleAdjointAlgebra S F] ≫ semisimpleAdjointAlgebraCounit S F =
      Functor.OplaxMonoidal.η F := by
  unfold semisimpleAdjointAlgebraCounit
  rw [semisimpleAdjointAlgebra_one, ← (semisimpleRightAdjunction S F).homEquiv_counit]
  exact Equiv.symm_apply_apply _ _

/-- Unit-Hom multiplicity is derived from the actual linear adjunction. -/
lemma semisimpleAdjointAlgebra_connected [HasKernels D] [Simple (𝟙_ D)] :
    Module.finrank ℂ (𝟙_ C ⟶ semisimpleAdjointAlgebra S F) = 1 := by
  calc
    _ = Module.finrank ℂ (F.obj (𝟙_ C) ⟶ 𝟙_ D) :=
      (semisimpleAdjointHomLinearEquiv S F (𝟙_ C) (𝟙_ D)).finrank_eq.symm
    _ = Module.finrank ℂ (𝟙_ D ⟶ 𝟙_ D) :=
      finrank_hom_iso (Functor.Monoidal.εIso F).symm (Iso.refl _)
    _ = 1 := CategoryTheory.finrank_endomorphism_simple_eq_one ℂ _

end Paper18.Category.DiagonalAlgebra

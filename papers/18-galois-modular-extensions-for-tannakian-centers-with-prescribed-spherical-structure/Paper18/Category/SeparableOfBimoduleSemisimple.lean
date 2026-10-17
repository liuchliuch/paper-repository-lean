import Paper18.Category.ModuleFunctorSemisimpleWattsAction
import Paper18.Category.ModuleFunctorSemisimpleSeparableAction
import Paper18.Category.SemisimpleSplitting

/-! # Actual separability from actual finite semisimple bimodules -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u w
namespace Paper18.Category.SeparableAlgebra
open ModuleFunctor.SeparableAction
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  (R : D) [MonObj R]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- The actual free right module on the left regular module has carrier R⊗R. -/
def freeRegularBimodule : ModuleFunctor.Bimodules R :=
  free (A := mop R) (Mod_.regular R)

/-- Actual multiplication is a genuine two-sided module map. -/
def bimoduleMultiplication : freeRegularBimodule R ⟶ ModuleFunctor.wattsRegular :=
  freeLift (Y := ModuleFunctor.wattsRegular) (𝟙 (Mod_.regular R))

@[simp] lemma bimoduleMultiplication_hom :
    (bimoduleMultiplication R).hom.hom = μ[R] := by
  change (𝟙 R ▷ R) ≫ μ[R] = μ[R]
  simp

/-- The actual algebra unit proves multiplication epimorphic, even
though its one-sided section need not be a bimodule map. -/
instance bimoduleMultiplication_epi : Epi (bimoduleMultiplication R) where
  left_cancellation {Z} f g h := by
    apply Mod_.Hom.ext
    apply Mod_.Hom.ext
    have hh := congrArg (fun k => k.hom.hom) h
    simp only [Mod_.comp_hom', bimoduleMultiplication_hom] at hh
    have hu : ((λ_ R).inv ≫ η[R] ▷ R) ≫ μ[R] = 𝟙 R := by
      rw [Category.assoc, MonObj.one_mul, Iso.inv_hom_id]
    have ht := congrArg (fun k => ((λ_ R).inv ≫ η[R] ▷ R) ≫ k) hh
    simpa only [← Category.assoc, hu, Category.id_comp] using ht

variable [HasKernels (ModuleFunctor.Bimodules R)]
  [HasFiniteBiproducts (ModuleFunctor.Bimodules R)]
  [∀ P Q : ModuleFunctor.Bimodules R, FiniteDimensional ℂ (P ⟶ Q)]
  {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton (ModuleFunctor.Bimodules R) ι)

/-- A finite semisimple category of actual two-sided modules supplies an
actual two-sided section of multiplication, hence actual separability.
No section or separability conclusion is included in the hypotheses. -/
def ofBimoduleSemisimple : SeparableAlgebra R where
  section_ := (T.splitEpi (bimoduleMultiplication R)).section_.hom.hom
  section_mul := by
    have h := congrArg (fun k => k.hom.hom) (T.splitEpi (bimoduleMultiplication R)).id
    simpa only [Mod_.comp_hom', bimoduleMultiplication_hom, Mod_.id_hom] using h
  left_linear := by
    let s := (T.splitEpi (bimoduleMultiplication R)).section_
    have h := s.hom.isMod_Hom.smul_hom
    change μ[R] ≫ s.hom.hom =
      (R ◁ s.hom.hom) ≫ (α_ R R R).inv ≫ μ[R] ▷ R at h
    exact h
  right_linear := by
    let s := (T.splitEpi (bimoduleMultiplication R)).section_
    have h := s.isMod_Hom.smul_hom
    rw [free_smul] at h
    have ht := congrArg Mod_.Hom.hom h
    change μ[R] ≫ s.hom.hom =
      (s.hom.hom ▷ R) ≫ (α_ R R R).hom ≫ R ◁ μ[R] at ht
    exact ht

end Paper18.Category.SeparableAlgebra

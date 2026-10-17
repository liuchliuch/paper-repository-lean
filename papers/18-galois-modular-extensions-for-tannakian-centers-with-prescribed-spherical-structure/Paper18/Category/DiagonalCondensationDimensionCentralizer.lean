import Paper18.Category.LocalModulesDimension
import Paper18.Category.LocalModulesPivotalSpherical
import Paper18.Category.RelativeCenterCentralizerDimension

/-! # Actual centralizer dimensions after connected Frobenius condensation -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u w v' u' w'
namespace Paper18.Category.DiagonalCondensation
section General
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory D] [BraidedCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (F : C ⥤ D) [F.Additive] [F.Monoidal] [F.Linear ℂ] [F.Full] [F.Faithful]

/-- The actual centralizer of an actual fully faithful tensor image has
the quotient FP dimension, by the proved intrinsic image dimension and
actual centralizer product theorem. -/
lemma centralizerFPdim_of_fullyFaithful (J : PivotalStructure D)
    (hD : IsNondegenerate (C := D)) :
    T.centralizerFPdim (Set.range F.obj) = T.fusionBasis.totalFPdim / S.fusionBasis.totalFPdim := by
  have h := T.supportFPdim_mul_centralizer J hD F.essImage
  rw [RelativeTensor.supportFPdim_essImage S T F] at h
  have hc : T.centralizerFPdim (F.essImage : Set D) =
      T.centralizerFPdim (Set.range F.obj) := by
    unfold FiniteSemisimpleSkeleton.centralizerFPdim
    congr 1
    exact congrArg (fun s : Set D => (fun X => X ∈ s))
      (RelativeTensor.centralizer_essImage F)
  rw [hc] at h
  have hs : S.fusionBasis.totalFPdim ≠ 0 := by
    apply ne_of_gt
    exact Finset.sum_pos' (fun i _ => sq_nonneg (S.fusionBasis.fpdim i))
      ⟨S.fusionBasis.one, Finset.mem_univ _, pow_pos (S.fusionBasis.fpdim_pos _) _⟩
  exact (eq_div_iff hs).mpr ((mul_comm _ _).trans h)
end General

section Local
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [HasCoequalizers C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {A : C} [MonObj A] [IsCommMonObj A] (R : SeparableAlgebra A)
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {B : Type u'} [Category.{v'} B]

/-- The actual intrinsic centralizer size in the constructed local fusion
category. This is the ambient support definition, with the constructed
local kernels, duals, and unit made explicit. -/
def localCentralizerFPdim (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1)
    (H : B ⥤ LocalModules A) : ℝ :=
  letI := R.localHasKernels S
  letI := R.localRightRigid S hconnected
  letI := R.localSimpleUnit S hconnected
  (R.localSkeleton S).centralizerFPdim (Set.range H.obj)

variable [Preadditive B] [Linear ℂ B] [MonoidalCategory B]
  [MonoidalPreadditive B] [MonoidalLinear ℂ B]
  [HasKernels B] [HasFiniteBiproducts B] [RightRigidCategory B]
  [∀ X Y : B, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ B)]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton B κ)
  (H : B ⥤ LocalModules A) [H.Additive] [H.Monoidal] [H.Linear ℂ] [H.Full] [H.Faithful]

/-- Actual centralizer dimensions in connected Frobenius condensation:
all local and module fusion structures and local nondegeneracy are derived. -/
lemma localCentralizerFPdim_eq_div (P : ModuleBalancing.MultiplicationPairing A)
    (J : PivotalStructure C) (hA : (J.twistIso A).hom = 𝟙 A)
    (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1)
    (hC : IsNondegenerate (C := C)) :
    localCentralizerFPdim R S hconnected H =
      S.fusionBasis.totalFPdim / (T.fusionBasis.totalFPdim * S.fpdim A ^ 2) := by
  letI := R.moduleRightRigid
  letI := R.localHasKernels S
  letI := R.localRightRigid S hconnected
  letI := R.localSimpleUnit S hconnected
  have hD := R.localNondegenerate S P J hA hconnected hC
  calc
    _ = R.localTotalFPdim S hconnected / T.fusionBasis.totalFPdim :=
      centralizerFPdim_of_fullyFaithful T (R.localSkeleton S) H
        (ModuleBalancing.localPivotal J hA) hD
    _ = _ := by
      rw [R.localTotalFPdim_eq_div S P J hA hconnected hC, div_div, mul_comm]
end Local
end Paper18.Category.DiagonalCondensation

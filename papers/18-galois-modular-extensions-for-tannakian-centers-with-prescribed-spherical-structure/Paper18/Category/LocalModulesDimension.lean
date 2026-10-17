import Paper18.Category.LocalModulesDimensionBasic
import Paper18.Category.LocalModulesNondegenerate
import Paper18.Category.RelativeCenterCentralizerDimension

/-! # The actual FP-dimension formula for local Frobenius condensation -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.SeparableAlgebra
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [HasCoequalizers C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {A : C} [MonObj A] [IsCommMonObj A] (S : SeparableAlgebra A)
  {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton C ι)
open RelativeTensor

/-- The actual local-module total dimension times the actual ambient
size is the square of the actual full-module total dimension. -/
theorem localTotalFPdim_mul_ambient (P : ModuleBalancing.MultiplicationPairing A)
    (J : PivotalStructure C) (hA : (J.twistIso A).hom = 𝟙 A)
    (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1)
    (hC : IsNondegenerate (C := C)) :
    S.localTotalFPdim T hconnected * T.fusionBasis.totalFPdim =
      S.moduleTotalFPdim T hconnected ^ 2 := by
  letI := S.moduleRightRigid
  letI := S.moduleSimpleUnit T hconnected
  let JM := P.modulePivotal S J hA
  letI := Drinfeld.pivotalLeftRigidCategory JM
  let Z := Drinfeld.centerSkeleton (S.skeleton T) JM
  let F := centralFreeFunctor (A := A)
  let ff := centralFreeFunctorFullyFaithful T hC hconnected
  letI := ff.full
  letI := ff.faithful
  have hZ := Drinfeld.center_nondegenerate (S.skeleton T) JM
  have h := Z.supportFPdim_mul_centralizer (Drinfeld.centerPivotal JM) hZ F.essImage
  rw [supportFPdim_essImage T Z F] at h
  have hc : Z.centralizerFPdim (F.essImage : Set (Center (Mod_ C A))) =
      Z.centralizerFPdim (Set.range F.obj) := by
    unfold FiniteSemisimpleSkeleton.centralizerFPdim
    congr 1
    exact congrArg (fun s : Set (Center (Mod_ C A)) => (fun X => X ∈ s))
      (centralizer_essImage F)
  rw [hc, ← S.localTotalFPdim_eq_centralizer T JM hconnected,
    Drinfeld.center_totalFPdim (S.skeleton T) JM Z] at h
  simpa only [moduleTotalFPdim, mul_comm] using h

/-- The actual local fusion category has total FP dimension equal to the
ambient total FP dimension divided by the square of the actual algebra
dimension. No centralizer or module dimension identity is assumed. -/
theorem localTotalFPdim_eq_div (P : ModuleBalancing.MultiplicationPairing A)
    (J : PivotalStructure C) (hA : (J.twistIso A).hom = 𝟙 A)
    (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1)
    (hC : IsNondegenerate (C := C)) :
    S.localTotalFPdim T hconnected = T.fusionBasis.totalFPdim / T.fpdim A ^ 2 := by
  have ht : T.fusionBasis.totalFPdim ≠ 0 := by
    apply ne_of_gt
    exact Finset.sum_pos' (fun i _ => sq_nonneg (T.fusionBasis.fpdim i))
      ⟨T.fusionBasis.one, Finset.mem_univ _, pow_pos (T.fusionBasis.fpdim_pos _) _⟩
  have hm := S.moduleTotalFPdim_mul T hconnected
  have ha : T.fpdim A ≠ 0 := by
    intro h
    rw [h, mul_zero] at hm
    exact ht hm.symm
  apply (eq_div_iff (pow_ne_zero 2 ha)).mpr
  apply (mul_right_cancel₀ ht)
  calc
    (S.localTotalFPdim T hconnected * T.fpdim A ^ 2) * T.fusionBasis.totalFPdim =
        (S.localTotalFPdim T hconnected * T.fusionBasis.totalFPdim) * T.fpdim A ^ 2 := by ring
    _ = (S.moduleTotalFPdim T hconnected * T.fpdim A) ^ 2 := by
      rw [S.localTotalFPdim_mul_ambient T P J hA hconnected hC]
      ring
    _ = T.fusionBasis.totalFPdim * T.fusionBasis.totalFPdim := by rw [hm, pow_two]

end Paper18.Category.SeparableAlgebra

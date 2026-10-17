import Paper18.Category.RelativeTensorRigid
import Paper18.Category.RelativeTensorDimensionBasic
import Paper18.Category.FusionCategory

/-! # Actual FP dimensions of separable modules

The ambient size of an actual module is a positive dimension vector for
the dominant free-module action. Positive eigenspace uniqueness determines
its normalization; the free adjunction then determines total dimension.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj BigOperators
universe v u w
namespace Paper18.Category.SeparableAlgebra
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [HasCoequalizers C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {A : C} [MonObj A] [IsCommMonObj A] (S : SeparableAlgebra A)
  {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton C ι)

section ModuleFusion
variable [RightRigidCategory (Mod_ C A)] [Simple (𝟙_ (Mod_ C A))]

omit [BraidedCategory C] [HasCoequalizers C] [IsCommMonObj A]
  [RightRigidCategory (Mod_ C A)] [Simple (𝟙_ (Mod_ C A))] in
/-- The additive underlying functor computes ambient dimensions by the
actual simple-module decomposition. -/
theorem underlying_fpdim_eq_sum (M : Mod_ C A) :
    T.fpdim M.X = ∑ j, ((S.skeleton T).multiplicity M j : ℝ) *
      T.fpdim ((S.skeleton T).simpleObject j).X := by
  let U := Mod_.forget (D := C) A
  change T.fpdim (U.obj M) = ∑ j, ((S.skeleton T).multiplicity M j : ℝ) *
    T.fpdim (U.obj ((S.skeleton T).simpleObject j))
  simp only [FiniteSemisimpleSkeleton.fpdim, (S.skeleton T).multiplicity_map T U M,
    Nat.cast_sum, Nat.cast_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

omit [BraidedCategory C] [RightRigidCategory C] [HasCoequalizers C] [Simple (𝟙_ C)]
  [IsCommMonObj A] [RightRigidCategory (Mod_ C A)] [Simple (𝟙_ (Mod_ C A))] in
/-- The actual free adjunction identifies its image multiplicities with
the underlying ambient simple multiplicities. -/
theorem free_imageCoeff_eq_underlying (i : ι) (j : S.SimpleIndex T) :
    T.imageCoeff (S.skeleton T) (InternalModule.freeFunctor (A := A)) i j =
      T.multiplicity ((S.skeleton T).simpleObject j).X i := by
  change Module.finrank ℂ ((S.skeleton T).simpleObject j ⟶
      InternalModule.free A (T.simpleObject i)) =
    Module.finrank ℂ (T.simpleObject i ⟶ ((S.skeleton T).simpleObject j).X)
  rw [(S.skeleton T).finrank_hom_comm]
  exact (RelativeTensor.freeHomLinearEquiv (T.simpleObject i) ((S.skeleton T).simpleObject j)).finrank_eq

/-- Underlying ambient dimension is normalized by the actual algebra
object, rather than by an assumed module-dimension formula. -/
theorem underlying_fpdim_scale (M : Mod_ C A) :
    T.fpdim M.X = T.fpdim A * (S.skeleton T).fpdim M := by
  let D := S.skeleton T
  let F := T.fusionMap D (InternalModule.freeFunctor (A := A)) S.free_retract_dominant
  let r : S.SimpleIndex T → ℝ := fun j => T.fpdim (D.simpleObject j).X
  have hr (j : S.SimpleIndex T) : 0 < r j := by
    apply T.fpdim_pos_of_not_isZero
    intro hz
    apply CategoryTheory.id_nonzero (D.simpleObject j)
    apply Mod_.Hom.ext
    exact hz.eq_zero_of_src _
  have hact (i : ι) (j : S.SimpleIndex T) :
      ∑ a, (F.imageCoeff i a : ℝ) * (∑ k, (D.fusionBasis.N j a k : ℝ) * r k) =
        T.fusionBasis.fpdim i * r j := by
    have h := S.underlying_fpdim_eq_sum T
      (D.simpleObject j ⊗ InternalModule.free A (T.simpleObject i))
    erw [T.fpdim_iso ((Mod_.forget (D := C) A).mapIso
      (RelativeTensor.tensorFreeIso (D.simpleObject j) (T.simpleObject i)))] at h
    change T.fpdim ((D.simpleObject j).X ⊗ T.simpleObject i) = _ at h
    rw [T.fpdim_tensor, T.fpdim_simple] at h
    have hm (k : S.SimpleIndex T) :
        D.multiplicity (D.simpleObject j ⊗ InternalModule.free A (T.simpleObject i)) k =
          ∑ a, F.imageCoeff i a * D.fusionBasis.N j a k :=
      D.multiplicity_tensor_left _ _ k
    change r j * T.fusionBasis.fpdim i = ∑ k,
      (D.multiplicity (D.simpleObject j ⊗ InternalModule.free A (T.simpleObject i)) k : ℝ) * r k at h
    simp only [hm, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul, mul_assoc] at h
    rw [Finset.sum_comm] at h
    simpa only [Finset.mul_sum, mul_assoc, mul_comm] using h.symm
  have hs := RelativeTensor.dominant_action_dimension_unique F r hr hact
  have hu : r D.fusionBasis.one = T.fpdim A :=
    T.fpdim_iso ((Mod_.forget (D := C) A).mapIso D.unitIso)
  rw [S.underlying_fpdim_eq_sum T M]
  change (∑ j, (D.multiplicity M j : ℝ) * r j) = _
  have hs' (j : S.SimpleIndex T) : r j = T.fpdim A * D.fusionBasis.fpdim j := by
    rw [hs j, hu]
  simp_rw [hs']
  unfold FiniteSemisimpleSkeleton.fpdim
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The total FP dimension of the actual module category is the ambient
total dimension divided by the dimension of the actual algebra. -/
theorem module_totalFPdim_mul :
    (S.skeleton T).fusionBasis.totalFPdim * T.fpdim A = T.fusionBasis.totalFPdim := by
  let D := S.skeleton T
  let F := T.fusionMap D (InternalModule.freeFunctor (A := A)) S.free_retract_dominant
  have hscale (j : S.SimpleIndex T) :
      T.fpdim ((D.simpleObject j).X) = T.fpdim A * D.fusionBasis.fpdim j := by
    have h := S.underlying_fpdim_scale T (D.simpleObject j)
    change T.fpdim (D.simpleObject j).X = T.fpdim A * D.fpdim (D.simpleObject j) at h
    rwa [D.fpdim_simple] at h
  have hu (j : S.SimpleIndex T) : T.fpdim (D.simpleObject j).X =
      ∑ i, (F.imageCoeff i j : ℝ) * T.fusionBasis.fpdim i := by
    change T.fpdim (D.simpleObject j).X =
      ∑ i, (T.imageCoeff D (InternalModule.freeFunctor (A := A)) i j : ℝ) * T.fusionBasis.fpdim i
    dsimp only [D]
    simp only [FiniteSemisimpleSkeleton.fpdim, S.free_imageCoeff_eq_underlying T]
  symm
  calc
    T.fusionBasis.totalFPdim =
        ∑ i, T.fusionBasis.fpdim i * (∑ j, (F.imageCoeff i j : ℝ) * D.fusionBasis.fpdim j) := by
      simp_rw [F.fpdim_preserved]
      simp only [FusionBasis.totalFPdim, pow_two]
    _ = ∑ j, (∑ i, (F.imageCoeff i j : ℝ) * T.fusionBasis.fpdim i) * D.fusionBasis.fpdim j := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ j, (T.fpdim A * D.fusionBasis.fpdim j) * D.fusionBasis.fpdim j := by
      simp_rw [← hu, hscale]
    _ = D.fusionBasis.totalFPdim * T.fpdim A := by
      simp only [FusionBasis.totalFPdim, Finset.sum_mul, pow_two]
      apply Finset.sum_congr rfl
      intro j _
      ring

end ModuleFusion

/-- Intrinsic FP dimension in the constructed actual module fusion category. -/
def moduleFPdim (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) (M : Mod_ C A) : ℝ :=
  letI := S.moduleRightRigid
  letI := S.moduleSimpleUnit T hconnected
  (S.skeleton T).fpdim M

/-- Total FP dimension of the constructed actual module fusion category. -/
def moduleTotalFPdim (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) : ℝ :=
  letI := S.moduleRightRigid
  letI := S.moduleSimpleUnit T hconnected
  (S.skeleton T).fusionBasis.totalFPdim

/-- The actual algebra dimension is the normalization of underlying FP dimension. -/
theorem moduleFPdim_underlying (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) (M : Mod_ C A) :
    T.fpdim M.X = T.fpdim A * S.moduleFPdim T hconnected M := by
  letI := S.moduleRightRigid
  letI := S.moduleSimpleUnit T hconnected
  exact S.underlying_fpdim_scale T M

/-- The actual total module dimension identity, with all module fusion
structures constructed from separability and connectedness. -/
theorem moduleTotalFPdim_mul (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) :
    S.moduleTotalFPdim T hconnected * T.fpdim A = T.fusionBasis.totalFPdim := by
  letI := S.moduleRightRigid
  letI := S.moduleSimpleUnit T hconnected
  exact S.module_totalFPdim_mul T

/-- The quotient form of the actual total module dimension identity. -/
theorem moduleTotalFPdim_eq_div (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) :
    S.moduleTotalFPdim T hconnected = T.fusionBasis.totalFPdim / T.fpdim A := by
  have hp : 0 < T.fpdim A := by
    apply T.fpdim_pos_of_not_isZero
    intro hz
    obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
      (show 0 < Module.finrank ℂ (𝟙_ C ⟶ A) by omega)
    exact hf (hz.eq_zero_of_tgt f)
  exact (eq_div_iff (ne_of_gt hp)).mpr (S.moduleTotalFPdim_mul T hconnected)

end Paper18.Category.SeparableAlgebra

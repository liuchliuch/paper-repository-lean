import Paper18.Category.SphericalizationNegative
import Paper18.Category.SphericalizationFPdim
import Paper18.Category.SignKernel
import Paper18.Category.FunctorDimensionEquivalence

/-! # Actual equivalence from a sign kernel of sphericalization

A character negative on the canonical negative generator selects one
sphericalization sign. Actual eigensplitting and tensoring the negative
summand by that generator prove retract dominance. The exact dimension
identity then proves actual full faithfulness and essential surjectivity.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.Sphericalized
open FixedBoundary
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (χ : 𝟭 (Sphericalized C) ≅ 𝟭 (Sphericalized C)) [NatTrans.IsMonoidal χ.hom]

/-- The actual forgetful tensor functor restricted to the actual sign kernel. -/
def positiveForget : SignKernel.Positive χ ⥤ C := SignKernel.inclusion χ ⋙ forget

instance positiveForget_monoidal : (positiveForget χ).Monoidal := by
  dsimp [positiveForget]; infer_instance
instance positiveForget_braided : (positiveForget χ).Braided := by
  dsimp [positiveForget]; infer_instance
instance positiveForget_additive : (positiveForget χ).Additive := by
  dsimp [positiveForget]; infer_instance
instance positiveForget_linear : (positiveForget χ).Linear ℂ := by
  dsimp [positiveForget]; infer_instance

variable (hχ : ∀ X, χ.hom.app X ≫ χ.hom.app X = 𝟙 X)
  (hε : χ.hom.app (negativeGenerator (C := C)) = (-1 : ℂ) • 𝟙 _)

include hε in
/-- Tensoring the actual negative eigensummand with epsilon makes it positive. -/
lemma negativeTensorMinus_positive (Y : Sphericalized C) :
    SignKernel.positiveProperty χ (negativeGenerator ⊗ SignKernel.minusObject χ Y) := by
  have he : Homogeneous χ 1 (negativeGenerator (C := C)) := by
    simpa [Homogeneous] using hε
  simpa [SignKernel.positiveProperty] using
    homogeneous_tensor χ he (SignKernel.minusObject_negative χ Y)

include hχ hε in
/-- Eigensplitting constructs a positive object whose actual underlying
object contains the underlying object of any square object as a retract. -/
theorem positiveForget_covers (Y : Sphericalized C) :
    ∃ Z : SignKernel.Positive χ, Nonempty (Retract (forget.obj Y) ((positiveForget χ).obj Z)) := by
  let a : SignKernel.Positive χ := ⟨SignKernel.plusObject χ Y, SignKernel.plusObject_positive χ Y⟩
  let b : SignKernel.Positive χ :=
    ⟨negativeGenerator ⊗ SignKernel.minusObject χ Y, negativeTensorMinus_positive χ hε Y⟩
  let f : Bool → SignKernel.Positive χ := fun j => if j then b else a
  let t : forget.obj (negativeGenerator ⊗ SignKernel.minusObject χ Y) ≅
      forget.obj (SignKernel.minusObject χ Y) := λ_ _
  let ip : forget.obj Y ⟶ (positiveForget χ).obj a := forget.map (SignKernel.plusπ χ hχ Y)
  let im : forget.obj Y ⟶ (positiveForget χ).obj b :=
    forget.map (SignKernel.minusπ χ hχ Y) ≫ t.inv
  let rp : (positiveForget χ).obj a ⟶ forget.obj Y := forget.map (SignKernel.plusι χ Y)
  let rm : (positiveForget χ).obj b ⟶ forget.obj Y := t.hom ≫ forget.map (SignKernel.minusι χ Y)
  let r : Retract (forget.obj Y) (⨁ fun j => (positiveForget χ).obj (f j)) :=
    { i := biproduct.lift (fun j => by cases j; exact ip; exact im)
      r := biproduct.desc (fun j => by cases j; exact rp; exact rm)
      retract := by
        rw [biproduct.lift_desc]
        simp only [Fintype.sum_bool]
        dsimp only [ip, im, rp, rm]
        rw [assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp, ← Functor.map_comp,
          ← Functor.map_add, add_comm, SignKernel.split_resolution]
        exact (forget (C := C)).map_id Y }
  exact ⟨⨁ f, ⟨r.trans (Retract.ofIso ((positiveForget χ).mapBiproduct f).symm)⟩⟩

include S hχ hε in
/-- Actual dominance over the original category, with no simple-lift
classification or image-fullness hypothesis. -/
theorem positiveForget_retract_dominant (X : C) :
    ∃ Z : SignKernel.Positive χ, Nonempty (Retract X ((positiveForget χ).obj Z)) := by
  obtain ⟨Y, ⟨r⟩⟩ := forget_retract_dominant (C := C) X
  obtain ⟨Z, ⟨t⟩⟩ := positiveForget_covers χ hχ hε Y
  exact ⟨Z, ⟨r.trans t⟩⟩

include S hε in
lemma character_negativeGenerator_nontrivial :
    χ.hom.app (negativeGenerator (C := C)) ≠ 𝟙 _ := by
  intro he
  have h := hε.symm.trans he
  have hn := CategoryTheory.id_nonzero (negativeGenerator (C := C))
  have ht : (2 : ℂ) • 𝟙 (negativeGenerator (C := C)) = 0 := by
    have heq : -(𝟙 (negativeGenerator (C := C))) = 𝟙 _ := by simpa using h
    rw [two_smul]
    calc
      _ = -𝟙 (negativeGenerator (C := C)) + 𝟙 _ :=
        congrArg (fun f => f + 𝟙 _) heq.symm
      _ = 0 := neg_add_cancel _
  exact hn ((smul_eq_zero.mp ht).resolve_left (by norm_num))

include S hχ hε in
/-- The actual sign kernel has exactly the original total FP dimension. -/
theorem positiveKernel_totalFPdim :
    SignKernel.positiveTotalFPdim (skeleton S) χ = S.fusionBasis.totalFPdim := by
  have h := SignKernel.totalFPdim_indexTwo_of_nontrivial (skeleton S) χ hχ
    negativeGenerator (character_negativeGenerator_nontrivial S χ hε)
  rw [totalFPdim_eq_twice S] at h
  linarith

/-- Full faithfulness and essential surjectivity are derived from actual
retract dominance and the exact intrinsic FP dimensions. -/
def positiveForget_isEquivalence :
    letI := SignKernel.hasKernels χ (skeleton S)
    letI := SignKernel.rightRigid χ (skeleton S)
    letI := SignKernel.simpleUnit χ (skeleton S)
    (positiveForget χ).IsEquivalence := by
  letI := SignKernel.hasKernels χ (skeleton S)
  letI := SignKernel.rightRigid χ (skeleton S)
  letI := SignKernel.simpleUnit χ (skeleton S)
  exact (SignKernel.skeleton χ (skeleton S)).isEquivalenceOfDominantDimensionEq S
    (positiveForget χ) (positiveForget_retract_dominant S χ hχ hε)
    (positiveKernel_totalFPdim S χ hχ hε)

end Paper18.Category.Sphericalized

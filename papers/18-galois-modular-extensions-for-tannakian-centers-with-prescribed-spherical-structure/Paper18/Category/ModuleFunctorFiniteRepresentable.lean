import Paper18.Category.ModuleFunctorFiniteRepresentableBasic
import Paper18.Category.FunctorRetract

/-! # Actual representation of homogeneous module endofunctors

Every actual strong complex-linear module endofunctor is a genuine
retract of negative alpha induction. Genuine source idempotent splitting
and the proved full faithfulness then construct an actual representing
neutral object. No desired representability or target semisimplicity
conclusion is supplied as a field.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u w
namespace Paper18.Category.FixedBoundary
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom] (d : ZMod 2)

/-- The actual right dual of a homogeneous simple has the same parity. -/
lemma simple_rightDual_homogeneous (j : ι) (hj : Homogeneous χ d (S.simpleObject j)) :
    Homogeneous χ d (dual C (S.simpleObject j)) := by
  letI : Simple (dual C (S.simpleObject j)) := S.simple_rightDual (S.simpleObject j)
  have hs : TensorAutomorphism.scalar χ (S.simpleObject j) = paritySign d := by
    apply smul_left_injective ℂ (CategoryTheory.id_nonzero (S.simpleObject j))
    exact (TensorAutomorphism.scalar_spec χ (S.simpleObject j)).trans hj
  have hd : TensorAutomorphism.scalar χ (dual C (S.simpleObject j)) =
      (TensorAutomorphism.scalar χ (S.simpleObject j))⁻¹ :=
    (TensorAutomorphism.scalar_iso χ (S.dualIso j)).symm.trans
      (TensorAutomorphism.scalar_dualLabel χ S j)
  change χ.hom.app (dual C (S.simpleObject j)) = paritySign d • 𝟙 _
  rw [← TensorAutomorphism.scalar_spec, hd, hs]
  rcases Paper18.ZMod.two_eq_zero_or_one d with rfl | rfl <;> simp

variable [BraidedCategory (SignKernel.Positive χ)]
  (L : SignKernel.Positive χ ⥤ Center C)
  (e : SignKernel.inclusion χ ≅ L ⋙ Center.forget C)
local notation "Alpha" => ModuleAlphaInduction.negative (SignKernel.Positive χ) (HomogeneousCategory χ d)

/-- Every genuine module endofunctor is an actual retract of an actual
negative-alpha object, constructed from its value at one genuine simple. -/
def homogeneousNegativeRetract (hL : NegativeCentralCompatibility χ L e)
    (F : ModuleAlphaInduction.End (SignKernel.Positive χ) (HomogeneousCategory χ d))
    (j : ι) (hj : Homogeneous χ d (S.simpleObject j)) :
    Retract F ((Alpha).obj (neutralTensorRightObject χ d
      (dual C (S.simpleObject j)) (simple_rightDual_homogeneous S χ d j hj)
      (F.toFunctor.obj ⟨S.simpleObject j, hj⟩))) := by
  let n : HomogeneousCategory χ d := ⟨S.simpleObject j, hj⟩
  let hp := simple_rightDual_homogeneous S χ d j hj
  let r := neutralTensorFunctorRetract χ d (dual C (S.simpleObject j)) hp n F
    (ModuleFunctor.normalizedLeftCup S (S.simpleObject j))
    (ε_ (S.simpleObject j) (dual C (S.simpleObject j)))
    (ModuleFunctor.normalizedLeftCup_evaluation S (S.simpleObject j))
  exact r.trans (Retract.ofIso
    (negativeTensorActionIso χ d (dual C (S.simpleObject j)) hp (F.toFunctor.obj n) L e hL).symm)

/-- Actual negative alpha induction is essentially surjective. The proof
splits the actual source idempotent produced by the genuine retract. -/
def homogeneousNegativeEssSurj (hL : NegativeCentralCompatibility χ L e)
    (j : ι) (hj : Homogeneous χ d (S.simpleObject j)) : (Alpha).EssSurj := by
  letI := homogeneousNegativeFull S χ d L e hL j hj
  letI := homogeneousNegativeFaithful S χ d j hj
  letI : HasKernels (SignKernel.Positive χ) := SignKernel.hasKernels χ S
  letI : IsIdempotentComplete (SignKernel.Positive χ) :=
    (Idempotents.isIdempotentComplete_iff_idempotents_have_kernels
      (C := SignKernel.Positive χ)).mpr (fun X p _ => inferInstance)
  exact ⟨fun F => essImage_of_retract (Alpha)
    (homogeneousNegativeRetract S χ d L e hL F j hj)⟩

/-- The actual homogeneous module endofunctor category is actually
equivalent to the actual neutral category through negative alpha induction. -/
def homogeneousNegativeEquivalence (hL : NegativeCentralCompatibility χ L e)
    (j : ι) (hj : Homogeneous χ d (S.simpleObject j)) :
    SignKernel.Positive χ ≌ ModuleAlphaInduction.End (SignKernel.Positive χ)
      (HomogeneousCategory χ d) := by
  letI := homogeneousNegativeFull S χ d L e hL j hj
  letI := homogeneousNegativeFaithful S χ d j hj
  letI := homogeneousNegativeEssSurj S χ d L e hL j hj
  letI : (Alpha).IsEquivalence := {}
  exact (Alpha).asEquivalence

/-- A chosen actual representing neutral object, obtained from the
constructed actual equivalence and actual source idempotent splitting. -/
def homogeneousRepresentative (hL : NegativeCentralCompatibility χ L e)
    (j : ι) (hj : Homogeneous χ d (S.simpleObject j))
    (F : ModuleAlphaInduction.End (SignKernel.Positive χ) (HomogeneousCategory χ d)) :
    SignKernel.Positive χ :=
  (homogeneousNegativeEquivalence S χ d L e hL j hj).inverse.obj F

/-- The chosen actual representative comes with its genuine module
natural representing isomorphism. -/
def homogeneousRepresentativeIso (hL : NegativeCentralCompatibility χ L e)
    (j : ι) (hj : Homogeneous χ d (S.simpleObject j))
    (F : ModuleAlphaInduction.End (SignKernel.Positive χ) (HomogeneousCategory χ d)) :
    (ModuleAlphaInduction.negative (SignKernel.Positive χ) (HomogeneousCategory χ d)).obj
        (homogeneousRepresentative S χ d L e hL j hj F) ≅ F :=
  (homogeneousNegativeEquivalence S χ d L e hL j hj).counitIso.app F

instance homogeneousNegativeEquivalence_functor_additive
    (hL : NegativeCentralCompatibility χ L e) (j : ι)
    (hj : Homogeneous χ d (S.simpleObject j)) :
    (homogeneousNegativeEquivalence S χ d L e hL j hj).functor.Additive :=
  inferInstanceAs ((ModuleAlphaInduction.negative (SignKernel.Positive χ)
    (HomogeneousCategory χ d)).Additive)

instance homogeneousNegativeEquivalence_functor_linear
    (hL : NegativeCentralCompatibility χ L e) (j : ι)
    (hj : Homogeneous χ d (S.simpleObject j)) :
    (homogeneousNegativeEquivalence S χ d L e hL j hj).functor.Linear ℂ :=
  inferInstanceAs ((ModuleAlphaInduction.negative (SignKernel.Positive χ)
    (HomogeneousCategory χ d)).Linear ℂ)

instance homogeneousNegativeEquivalence_inverse_additive
    (hL : NegativeCentralCompatibility χ L e) (j : ι)
    (hj : Homogeneous χ d (S.simpleObject j)) :
    (homogeneousNegativeEquivalence S χ d L e hL j hj).inverse.Additive :=
  CategoryTheory.Equivalence.inverse_additive _

instance homogeneousNegativeEquivalence_inverse_linear
    (hL : NegativeCentralCompatibility χ L e) (j : ι)
    (hj : Homogeneous χ d (S.simpleObject j)) :
    (homogeneousNegativeEquivalence S χ d L e hL j hj).inverse.Linear ℂ :=
  CategoryTheory.Equivalence.inverseLinear ℂ _

end Paper18.Category.FixedBoundary

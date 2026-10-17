import Paper18.Results.CategoricalCaseOne
import Paper18.Category.ModuleCentralizerIntegrality
import Paper18.Category.ModuleTensorCharacters
import Paper18.Category.InvertibleFunctor

/-! # The actual Case 1 condensation-to-integrality argument

The sign descends to actual algebra modules. Its value on the actual free
order-two object is minus one. The even centralizer is proved integral by
the actual restricted free functor; nondegenerate monodromy then constructs
the odd invertible and proves integrality of every actual simple module.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [HasCoequalizers C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {A : C} [MonObj A] [IsCommMonObj A] (R : SeparableAlgebra A)
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  [RightRigidCategory (Mod_ C A)] [Simple (𝟙_ (Mod_ C A))]

include R in
theorem integral_of_transparent_condensation_character
    (hA : A ∈ mugerCenter (C := C))
    (JQ : PivotalStructure (Mod_ C A))
    (hQ : letI := moduleBraidedOfTransparent hA
      IsNondegenerate (C := Mod_ C A))
    (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]
    (hχA : χ.hom.app A = 𝟙 A) {e : C} (E : TensorInverse e)
    (he : e ⊗ e ≅ 𝟙_ C) (hχe : χ.hom.app e = (-1 : ℂ) • 𝟙 e)
    (hI : S.CentralizerIntegral {e}) : S.Integral := by
  letI := moduleBraidedOfTransparent hA
  let F := InternalModule.freeFunctor (A := A)
  let χQ := ModuleTensorCharacters.moduleCharacter χ hχA
  have hχQ : χQ.hom.app (F.obj e) = (-1 : ℂ) • 𝟙 (F.obj e) := by
    change (ModuleTensorCharacters.moduleCharacter χ hχA).hom.app
      (InternalModule.free A e) = _
    rw [ModuleTensorCharacters.free_compatible, hχe]
    exact (F.map_smul (-1 : ℂ) (𝟙 e)).trans
      (congrArg (fun f => (-1 : ℂ) • f) (F.map_id e))
  have hIQ := R.free_centralizer_integral S hA e hI
  have hMQ : (R.skeleton S).Integral :=
    integral_of_character_odd_on_order_two (R.skeleton S) JQ hQ χQ
      (E.map F) (TensorInverse.mapSquare F he) hχQ hIQ
  exact S.integral_of_integral_target (R.skeleton S) F hMQ

end Paper18.Category

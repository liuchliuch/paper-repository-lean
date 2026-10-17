import Paper18.Category.DrinfeldSemisimple
import Paper18.Category.DrinfeldCharacterMonodromy
import Paper18.Category.MonodromyIntegrality

/-! # The actual categorical odd-invertible step in Case 1

The odd invertible is constructed from the genuine nondegenerate center
factorization. Integrality then uses the actual order-two monodromy signs.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (J : PivotalStructure C) (hC : IsNondegenerate (C := C))
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]
  {e : C} (E : TensorInverse e) (he : e ⊗ e ≅ 𝟙_ C)

include J hC E he in
theorem integral_of_character_odd_on_order_two
    (hχ : χ.hom.app e = (-1 : ℂ) • 𝟙 e)
    (hI : S.CentralizerIntegral {e}) : S.Integral := by
  obtain ⟨i,A,hA⟩ := Drinfeld.monodromyCharacter_surjective_of_centerSkeleton
    S χ J (Drinfeld.centerSkeleton S J) hC
  have ha : (doubleBraiding (S.simpleObject i) e).hom =
      (-1 : ℂ) • 𝟙 ((S.simpleObject i) ⊗ e) := by
    rw [← A.monodromyCharacter_spec, hA]
    change (S.simpleObject i) ◁ χ.hom.app e = _
    rw [hχ, MonoidalLinear.whiskerLeft_smul]
    exact congrArg (fun f => (-1 : ℂ) • f) (whiskerLeft_id (S.simpleObject i) e)
  exact integral_of_odd_invertible S E he A
    (doubleBraiding_scalar_swap (S.simpleObject i) e (-1) ha) hI

end Paper18.Category

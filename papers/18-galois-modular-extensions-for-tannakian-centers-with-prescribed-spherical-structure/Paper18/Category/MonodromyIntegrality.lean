import Paper18.Category.FixedBoundaryBosonGrading
import Paper18.Category.CentralizerFusion

/-! # Actual integrality from an odd invertible object

For an order-two invertible object, monodromy gives the actual sign on each
simple. Tensoring an odd simple with an odd invertible moves it into the
actual centralizer and preserves its actual Frobenius--Perron dimension.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

variable [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

lemma doubleBraiding_scalar_swap (X Y : C) (c : ℂ)
    (h : (doubleBraiding X Y).hom = c • 𝟙 (X ⊗ Y)) :
    (doubleBraiding Y X).hom = c • 𝟙 (Y ⊗ X) := by
  apply (cancel_epi (β_ X Y).hom).mp
  have hh := congrArg (fun k => k ≫ (β_ X Y).hom) h
  simpa [doubleBraiding, Category.assoc] using hh

lemma tensorCharacter_scalar_sign (χ : 𝟭 C ≅ 𝟭 C)
    (hχ : ∀ X : C, χ.hom.app X ≫ χ.hom.app X = 𝟙 X) (X : C) [Simple X] :
    TensorAutomorphism.scalar χ X = 1 ∨ TensorAutomorphism.scalar χ X = -1 := by
  apply sq_eq_one_iff.mp
  apply smul_left_injective ℂ (CategoryTheory.id_nonzero X)
  calc
    TensorAutomorphism.scalar χ X ^ 2 • 𝟙 X =
        (TensorAutomorphism.scalar χ X • 𝟙 X) ≫
          (TensorAutomorphism.scalar χ X • 𝟙 X) := by simp [pow_two, smul_smul]
    _ = 𝟙 X := by rw [TensorAutomorphism.scalar_spec, hχ]
    _ = (1 : ℂ) • 𝟙 X := by simp

lemma tensorCharacter_scalar_tensor (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]
    (X Y : C) [Simple X] [Simple Y] [Simple (X ⊗ Y)] :
    TensorAutomorphism.scalar χ (X ⊗ Y) =
      TensorAutomorphism.scalar χ X * TensorAutomorphism.scalar χ Y := by
  apply smul_left_injective ℂ (CategoryTheory.id_nonzero (X ⊗ Y))
  exact (TensorAutomorphism.scalar_spec χ (X ⊗ Y)).trans
    (TensorAutomorphism.tensor_component_simple χ X Y)

lemma fpdim_integer_of_centralizes {e X : C} [Simple X]
    (hI : S.CentralizerIntegral {e}) (hX : Centralizes e X) :
    ∃ n : ℤ, S.fpdim X = n := by
  obtain ⟨i,⟨u⟩⟩ := S.simple_isomorphic_representative X
  have hi : S.simpleObject i ∈ centralizer {e} := by
    intro Y hY
    rcases Set.mem_singleton_iff.mp hY with rfl
    exact hX.symm.of_iso_left u.symm
  obtain ⟨n,hn⟩ := (S.centralizerIntegral_iff {e}).mp hI i hi
  exact ⟨n,(S.fpdim_iso u).trans hn⟩

theorem integral_of_odd_invertible {e a : C} (E : TensorInverse e)
    (he : e ⊗ e ≅ 𝟙_ C) (A : TensorInverse a)
    (ha : (doubleBraiding e a).hom = (-1 : ℂ) • 𝟙 (e ⊗ a))
    (hI : S.CentralizerIntegral {e}) : S.Integral := by
  letI := A.simple S
  have hχa : TensorAutomorphism.scalar E.monodromyCharacter a = -1 := by
    letI := E.simple_tensor S a
    apply smul_left_injective ℂ (CategoryTheory.id_nonzero (e ⊗ a))
    exact (E.doubleBraiding_scalar a).symm.trans ha
  intro X hX
  letI := hX
  rcases tensorCharacter_scalar_sign E.monodromyCharacter
    (E.monodromy_involutive_of_square he) X with hpos | hneg
  · apply fpdim_integer_of_centralizes S hI
    change (doubleBraiding e X).hom = 𝟙 (e ⊗ X)
    rw [E.doubleBraiding_scalar, hpos, one_smul]
  · letI := A.simple_tensor S X
    have hodd : TensorAutomorphism.scalar E.monodromyCharacter (a ⊗ X) = 1 := by
      rw [tensorCharacter_scalar_tensor, hχa, hneg]
      norm_num
    have hc : Centralizes e (a ⊗ X) := by
      change (doubleBraiding e (a ⊗ X)).hom = 𝟙 (e ⊗ (a ⊗ X))
      rw [E.doubleBraiding_scalar, hodd, one_smul]
    obtain ⟨n,hn⟩ := fpdim_integer_of_centralizes S hI hc
    refine ⟨n,?_⟩
    rw [S.fpdim_tensor, S.fpdim_eq_one_of_tensorInvertible ⟨A⟩, one_mul] at hn
    exact hn

end Paper18.Category

import Paper18.Category.DrinfeldPivotalFactorization
import Paper18.Category.DeligneProductMapReverse
import Paper18.Category.DeligneProductEmbedding

/-! # Actual pivotal preservation by actual Deligne product functors -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped TensorProduct
universe v u v' u' v₁ u₁ v₂ u₂
namespace Paper18.Category.DeligneProduct
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [bC : BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [bD : BraidedCategory D]
  {E : Type u₁} [Category.{v₁} E] [Preadditive E] [Linear ℂ E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalLinear ℂ E]
  [RightRigidCategory E] [bE : BraidedCategory E]
  {H : Type u₂} [Category.{v₂} H] [Preadditive H] [Linear ℂ H]
  [MonoidalCategory H] [MonoidalPreadditive H] [MonoidalLinear ℂ H]
  [RightRigidCategory H] [bH : BraidedCategory H]
  (F : C ⥤ E) [F.Additive] [F.Linear ℂ] [F.Braided]
  (G : D ⥤ H) [G.Additive] [G.Linear ℂ] [G.Braided]
  (J : PivotalStructure C) (K : PivotalStructure D)
  (L : PivotalStructure E) (M : PivotalStructure H)

/-- Actual pivotal preservation in both factors gives actual pivotal
preservation of the actual additive Deligne product functor. -/
theorem map_preservesPivotal (hF : PreservesPivotal F J L) (hG : PreservesPivotal G K M) :
    PreservesPivotal (map F G) (pivotal J K) (pivotal L M) := by
  let Q := LinearTensor.map F G ⋙ Mat_.embedding (LinearTensor E H)
  have hraw (Z : LinearTensor C D) : Q.map ((LinearTensor.productTwist J K).hom.app Z) =
      ((pivotal L M).twistIso (Q.obj Z)).hom := by
    funext i k
    cases i
    cases k
    change (LinearTensor.map F G).map ((LinearTensor.productTwist J K).hom.app Z) =
      ((pivotal L M).twistIso ((Mat_.embedding (LinearTensor E H)).obj
        (⟨F.obj Z.left, G.obj Z.right⟩ : LinearTensor E H))).hom PUnit.unit PUnit.unit
    rw [pivotal_twist_pair]
    change F.map (J.twistIso Z.left).hom ⊗ₜ[ℂ] G.map (K.twistIso Z.right).hom = _
    rw [hF.twist, hG.twist]
  apply preservesPivotal_of_twist
  intro X
  change (map F G).map ((pivotal J K).twistNatIso.hom.app X) = _
  rw [pivotal_twist]
  exact Drinfeld.linearMatLift_twist Q (LinearTensor.productTwist J K)
    (pivotal L M) hraw X

/-- Prescribed actual product pivotal structure with explicitly reversed
second braiding, also valid when the two factor types coincide. -/
def reverseRightProductPivotal : PivotalStructure (DeligneProduct C D) :=
  @pivotal C _ _ _ _ _ _ _ bC D _ _ _ _ _ _ _ (@reverseBraiding D _ _ bD) J K

/-- Actual pivotal preservation for the explicit reverse-second product
structures, with the original strong tensor maps. -/
theorem mapReverseSecond_preservesPivotal
    (hF : PreservesPivotal F J L) (hG : PreservesPivotal G K M) :
    PreservesPivotal (map F G) (reverseRightProductPivotal J K)
      (reverseRightProductPivotal L M) := by
  exact @map_preservesPivotal C _ _ _ _ _ _ _ bC
    D _ _ _ _ _ _ _ (@reverseBraiding D _ _ bD)
    E _ _ _ _ _ _ _ bE H _ _ _ _ _ _ _ (@reverseBraiding H _ _ bH)
    F _ _ inferInstance G _ _ (braidedFunctorReverse G) J K L M hF hG

/-- The actual left unit-factor embedding preserves the actual prescribed
product pivotal structure. -/
theorem left_preservesPivotal :
    PreservesPivotal (left (C := C) (D := D)) J (pivotal J K) := by
  apply preservesPivotal_of_twist
  intro X
  funext i k
  cases i
  cases k
  change (J.twistIso X).hom ⊗ₜ[ℂ] 𝟙 (𝟙_ D) =
    ((pivotal J K).twistIso ((Mat_.embedding (LinearTensor C D)).obj
      (⟨X, 𝟙_ D⟩ : LinearTensor C D))).hom PUnit.unit PUnit.unit
  rw [pivotal_twist_pair]
  rw [K.twist_unit]

/-- The actual left embedding also preserves the prescribed pivotal
structure with reversed second braiding. -/
theorem leftReverseSecond_preservesPivotal :
    PreservesPivotal (left (C := C) (D := D)) J (reverseRightProductPivotal J K) := by
  exact @left_preservesPivotal C _ _ _ _ _ _ _ bC
    D _ _ _ _ _ _ _ (@reverseBraiding D _ _ bD) J K

section Spherical
variable [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type*} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type*} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)

include S T in
/-- Reversing a braiding does not affect the actual sphericality of the
prescribed product pivotal structure. -/
theorem reverseRightProductPivotal_spherical (hJ : J.Spherical) (hK : K.Spherical) :
    (reverseRightProductPivotal J K).Spherical := by
  exact @pivotal_spherical C _ _ _ _ _ _ _ bC
    D _ _ _ _ _ _ _ (@reverseBraiding D _ _ bD) J K
    _ _ _ _ _ _ _ _ ι _ S κ _ T hJ hK
end Spherical
end Paper18.Category.DeligneProduct

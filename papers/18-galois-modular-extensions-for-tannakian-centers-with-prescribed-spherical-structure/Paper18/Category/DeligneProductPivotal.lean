import Paper18.Category.DeligneProductPivotalRaw
import Paper18.Category.DeligneProductPivotalMatrix
import Paper18.Category.FactorizationEssentialSurjectiveProduct
import Paper18.Category.LocalModulesPivotalRibbon

/-! # Actual prescribed spherical structures on Deligne products

The twist is the actual componentwise twist, extended by finite diagonal
matrices. Its balancing and dual compatibility are proved in the actual
category, and reconstruct its actual coherent pivotal structure.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped TensorProduct
universe v u w v' u' w'
namespace Paper18.Category.DeligneProduct
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [BraidedCategory D]
  (J : PivotalStructure C) (K : PivotalStructure D)

/-- The actual componentwise pivotal structure on the existing actual
Deligne monoidal category. -/
def pivotal : PivotalStructure (DeligneProduct C D) :=
  LinearMat.matrixPivotal (LinearTensor.productTwist J K)
    (LinearTensor.productTwist_unit J K) (LinearTensor.productTwist_tensor J K)

@[simp] lemma pivotal_twist : (pivotal J K).twistNatIso =
    LinearMat.matrixTwist (LinearTensor.productTwist J K) :=
  LinearMat.matrixPivotal_twist _ _ _

/-- On an actual external tensor pair the twist is the pure tensor of
the actual twists of its two factors. -/
lemma pivotal_twist_pair (X : C) (Y : D) :
    ((pivotal J K).twistIso ((Mat_.embedding (LinearTensor C D)).obj
      (⟨X,Y⟩ : LinearTensor C D))).hom PUnit.unit PUnit.unit =
        (J.twistIso X).hom ⊗ₜ[ℂ] (K.twistIso Y).hom := by
  have h := congrArg (fun θ : 𝟭 (DeligneProduct C D) ≅ 𝟭 (DeligneProduct C D) =>
    θ.hom.app ((Mat_.embedding (LinearTensor C D)).obj (⟨X,Y⟩ : LinearTensor C D))
      PUnit.unit PUnit.unit) (pivotal_twist J K)
  apply h.trans
  exact LinearMat.indexEquivHom_apply (Equiv.refl _)
    (fun i => (LinearTensor.productTwist J K).hom.app
      (((Mat_.embedding (LinearTensor C D)).obj (⟨X,Y⟩ : LinearTensor C D)).X i)) PUnit.unit

variable [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)

include S T in
/-- The prescribed actual spherical structures give an actual spherical
structure on the Deligne product, on every actual endomorphism. -/
theorem pivotal_spherical (hJ : J.Spherical) (hK : K.Spherical) :
    (pivotal J K).Spherical := by
  letI := hasKernels S T
  letI := simpleUnit S T
  apply (pivotal J K).spherical_of_twistSelfDual (skeleton S T)
  intro X
  change (pivotal J K).twistNatIso.hom.app (dual (DeligneProduct C D) X) =
    dualMap (DeligneProduct C D) ((pivotal J K).twistNatIso.hom.app X)
  rw [pivotal_twist]
  exact LinearMat.matrixTwist_dual (LinearTensor.productTwist J K)
    (LinearTensor.productTwist_dual J K (J.twistSelfDual_of_spherical S hJ)
      (K.twistSelfDual_of_spherical T hK)) X

end Paper18.Category.DeligneProduct

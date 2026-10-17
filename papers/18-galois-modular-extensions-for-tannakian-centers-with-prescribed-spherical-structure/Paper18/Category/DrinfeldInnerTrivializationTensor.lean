import Paper18.Category.DrinfeldInnerTrivialization
import Paper18.Category.MonoidalNatIsoUnit

/-! # Tensor coherence suffices for the actual inner center trivialization -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.Monoidal
universe v u w
namespace Paper18.Category.DrinfeldInner
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (F : C ⥤ C) [F.Monoidal] [F.IsEquivalence] (L : C)
  (γ : tensorLeft L ≅ F ⋙ tensorRight L)

/-- Invertibility derives the unit equation from the actual tensor square. -/
def underlyingOfIntertwinerMonoidalOfTensor (E : TensorInverse L)
    (hγtensor : ∀ X Y, γ.hom.app (X ⊗ Y) =
      (conjugatingTensorIso F L γ X Y).hom ≫ μ F X Y ▷ L) :
    NatTrans.IsMonoidal (underlyingOfIntertwiner F L γ E).hom := by
  apply monoidalNatIso_isMonoidal_of_tensor
  intro Z W
  simpa using monoidal_tensor_of_intertwining F L γ
    (underlyingOfIntertwiner F L γ E) E hγtensor
    (underlyingOfIntertwiner_intertwines F L γ E) Z W

section Fusion
variable [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [CategoryTheory.Limits.HasKernels C] [CategoryTheory.Limits.HasFiniteBiproducts C]
  [Simple (𝟙_ C)] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

/-- The constructed actual monoidal center trivialization, using only the
actual tensor square of the conjugating intertwiner. -/
def trivializationOfIntertwinerOfTensor (E : TensorInverse L)
    (hγtensor : ∀ X Y, γ.hom.app (X ⊗ Y) =
      (conjugatingTensorIso F L γ X Y).hom ≫ μ F X Y ▷ L) :
    DrinfeldEquivalence.map F ≅ 𝟭 (Center C) := by
  letI := underlyingOfIntertwinerMonoidalOfTensor F L γ E hγtensor
  exact liftOverForget F (underlyingOfIntertwiner F L γ E) S J

instance trivializationOfIntertwinerOfTensor_monoidal (E : TensorInverse L)
    (hγtensor : ∀ X Y, γ.hom.app (X ⊗ Y) =
      (conjugatingTensorIso F L γ X Y).hom ≫ μ F X Y ▷ L) :
    NatTrans.IsMonoidal (trivializationOfIntertwinerOfTensor F L γ S J E hγtensor).hom := by
  letI := underlyingOfIntertwinerMonoidalOfTensor F L γ E hγtensor
  exact inferInstanceAs (NatTrans.IsMonoidal
    (liftOverForget F (underlyingOfIntertwiner F L γ E) S J).hom)

@[simp] lemma trivializationOfIntertwinerOfTensor_hom_app_f (E : TensorInverse L)
    (hγtensor : ∀ X Y, γ.hom.app (X ⊗ Y) =
      (conjugatingTensorIso F L γ X Y).hom ≫ μ F X Y ▷ L) (Z : Center C) :
    ((trivializationOfIntertwinerOfTensor F L γ S J E hγtensor).hom.app Z).f =
      (underlyingOfIntertwiner F L γ E).hom.app Z := rfl

end Fusion
end Paper18.Category.DrinfeldInner

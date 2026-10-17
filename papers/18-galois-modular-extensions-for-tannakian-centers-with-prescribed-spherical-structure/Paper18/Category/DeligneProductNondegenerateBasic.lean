import Paper18.Category.LinearTensorBraided
import Paper18.Category.LinearMatMonoidalBraided
import Paper18.Category.LinearTensorSemisimple
import Paper18.Category.NondegenerateBasic
import Paper18.Category.CentralizerSimples

/-! # Actual component monodromy in the Deligne product -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped TensorProduct
universe v u w v' u' w' z z'
namespace Paper18.Category.DeligneProduct

section VectorSpace
variable {M : Type z} [AddCommGroup M] [Module ℂ M]
  {N : Type z'} [AddCommGroup N] [Module ℂ N]

/-- Tensoring a vector with a fixed nonzero vector is injective. The proof
uses an actual linear left inverse of the corresponding scalar line. -/
lemma tmul_right_injective (n : N) (hn : n ≠ 0) :
    Function.Injective (fun m : M => m ⊗ₜ[ℂ] n) := by
  let f := LinearMap.toSpanSingleton ℂ N n
  obtain ⟨l, hl⟩ := f.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (smul_left_injective ℂ hn))
  have hln : l n = 1 := by
    simpa [f] using LinearMap.congr_fun hl 1
  intro x y h
  have hh := congrArg (fun t => (TensorProduct.rid ℂ M)
    (TensorProduct.map (LinearMap.id : M →ₗ[ℂ] M) l t)) h
  simpa [hln] using hh

lemma tmul_left_injective (m : M) (hm : m ≠ 0) :
    Function.Injective (fun n : N => m ⊗ₜ[ℂ] n) := by
  intro x y h
  apply tmul_right_injective m hm
  simpa using congrArg (TensorProduct.comm ℂ M N) h
end VectorSpace

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] [BraidedCategory D]

lemma raw_doubleBraiding (X Y : LinearTensor C D) :
    (doubleBraiding X Y).hom =
      (doubleBraiding X.left Y.left).hom ⊗ₜ[ℂ]
        (doubleBraiding X.right Y.right).hom := by
  change (((β_ X.left Y.left).hom ≫ (β_ Y.left X.left).hom) ⊗ₜ[ℂ]
    ((β_ X.right Y.right).hom ≫ (β_ Y.right X.right).hom)) = _
  rfl

/-- The actual raw pair monodromy is trivial if both factor monodromies are. -/
lemma raw_centralizes {X Y : LinearTensor C D}
    (hC : Centralizes X.left Y.left) (hD : Centralizes X.right Y.right) :
    Centralizes X Y := by
  change (doubleBraiding X Y).hom = _
  rw [raw_doubleBraiding, hC, hD]
  rfl

/-- Testing against `(Z,1)` detects the first factor of monodromy. -/
lemma centralizes_left_test {X : LinearTensor C D} [Simple X.right] (Z : C)
    (h : Centralizes X (⟨Z, 𝟙_ D⟩ : LinearTensor C D)) : Centralizes X.left Z := by
  letI : Simple (X.right ⊗ 𝟙_ D) := Simple.of_iso (ρ_ X.right)
  apply tmul_right_injective (𝟙 (X.right ⊗ 𝟙_ D)) (CategoryTheory.id_nonzero _)
  change (doubleBraiding X (⟨Z, 𝟙_ D⟩ : LinearTensor C D)).hom = _ at h
  rw [raw_doubleBraiding, centralizes_unit_right] at h
  exact h

/-- Testing against `(1,Z)` detects the second factor of monodromy. -/
lemma centralizes_right_test {X : LinearTensor C D} [Simple X.left] (Z : D)
    (h : Centralizes X (⟨𝟙_ C, Z⟩ : LinearTensor C D)) : Centralizes X.right Z := by
  letI : Simple (X.left ⊗ 𝟙_ C) := Simple.of_iso (ρ_ X.left)
  apply tmul_left_injective (𝟙 (X.left ⊗ 𝟙_ C)) (CategoryTheory.id_nonzero _)
  change (doubleBraiding X (⟨𝟙_ C, Z⟩ : LinearTensor C D)).hom = _ at h
  rw [raw_doubleBraiding, centralizes_unit_right] at h
  exact h

variable [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)

/-- The actual simple pair of the two unit labels is the actual tensor unit. -/
def unitPairIso [HasKernels C] [HasKernels D]
    [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
    [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
    [Simple (𝟙_ C)] [Simple (𝟙_ D)] :
    pairObject S T S.unitLabel T.unitLabel ≅ 𝟙_ (DeligneProduct C D) :=
  (Mat_.embedding (LinearTensor C D)).mapIso
    (LinearTensor.isoOfPair S.unitIso T.unitIso)

end Paper18.Category.DeligneProduct

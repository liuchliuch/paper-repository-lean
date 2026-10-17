import Paper18.Category.FactorizationFullyFaithfulRotation
import Paper18.Category.FactorizationFullyFaithfulCriterion
import Paper18.Category.FactorizationDeligne
import Paper18.Category.LinearTensorSemisimple

/-!
# Actual full faithfulness of nondegenerate Deligne factorization

The actual canonical Deligne functor is fully faithful. This is derived
from the actual rigid Hom rotation, Müger nondegeneracy, Schur's lemma and
the constructed finite semisimple source; image simplicity is not assumed.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped TensorProduct
universe v u w
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- The actual image of a single pair under the additive-envelope lift is
canonically its actual factored center object. -/
def deligneFactorizationPairIso (X Y : C) :
    (deligneFactorization C).obj ((Mat_.embedding (LinearTensor C C)).obj ⟨X,Y⟩) ≅
      (positive C).obj X ⊗ (negative C).obj Y := by
  change (⨁ fun _ : PUnit => (positive C).obj X ⊗ (negative C).obj Y) ≅ _
  refine
    { hom := biproduct.π (fun _ : PUnit => (positive C).obj X ⊗ (negative C).obj Y) PUnit.unit
      inv := biproduct.ι (fun _ : PUnit => (positive C).obj X ⊗ (negative C).obj Y) PUnit.unit
      hom_inv_id := ?_
      inv_hom_id := by simp }
  apply biproduct.hom_ext
  intro j
  cases j
  simp



/-- The singleton-envelope comparison intertwines the actual linear and
additive factorization maps. -/
@[reassoc]
lemma deligneFactorizationPairIso_naturality {X X' Y Y' : C}
    (t : (X ⟶ X') ⊗[ℂ] (Y ⟶ Y')) :
    (deligneFactorization C).map ((Mat_.embedding (LinearTensor C C)).map
      (show (⟨X,Y⟩ : LinearTensor C C) ⟶ ⟨X',Y'⟩ from t)) ≫
        (deligneFactorizationPairIso X' Y').hom =
      (deligneFactorizationPairIso X Y).hom ≫
        (linearFactorization C).map
          (show (⟨X,Y⟩ : LinearTensor C C) ⟶ ⟨X',Y'⟩ from t) := by
  change (biproduct.matrix (fun _ _ : PUnit => (linearFactorization C).map
      (show (⟨X,Y⟩ : LinearTensor C C) ⟶ ⟨X',Y'⟩ from t))) ≫
        biproduct.π _ PUnit.unit = biproduct.π _ PUnit.unit ≫ _
  apply biproduct.hom_ext'
  intro i
  cases i
  simp


include S in
/-- The actual source simple pairs have the proved orthogonal image Hom
law under the actual Deligne factorization functor. -/
lemma finrank_deligneFactorization_simpleHom (hC : IsNondegenerate (C := C)) (p q : ι × ι) :
    Module.finrank ℂ
      ((deligneFactorization C).obj ((DeligneProduct.skeleton S S).simpleObject p) ⟶
        (deligneFactorization C).obj ((DeligneProduct.skeleton S S).simpleObject q)) =
      if p = q then 1 else 0 := by
  dsimp only [DeligneProduct.skeleton, DeligneProduct.pairObject]
  rw [finrank_hom_iso (deligneFactorizationPairIso (S.simpleObject p.1) (S.simpleObject p.2))
    (deligneFactorizationPairIso (S.simpleObject q.1) (S.simpleObject q.2))]
  rw [finrank_factorization_simpleHom S hC]
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  by_cases hi : i = k <;> by_cases hj : j = l <;> simp [hi, hj]

include S in
/-- Actual full faithfulness is a theorem of the constructed Deligne
factorization functor under actual Müger nondegeneracy. -/
def deligneFactorizationFullyFaithful (hC : IsNondegenerate (C := C)) :
    (deligneFactorization C).FullyFaithful := by
  letI := DeligneProduct.hasKernels S S
  exact (DeligneProduct.skeleton S S).fullyFaithfulOfSimpleHomDimensions
    (deligneFactorization C) (fun p q => by
      by_cases h : p = q
      · simpa only [if_pos h] using finrank_deligneFactorization_simpleHom S hC p q
      · simpa only [if_neg h] using finrank_deligneFactorization_simpleHom S hC p q)

include S in
/-- The actual canonical comparison identifies the tensor product of the
factor Hom spaces with the center Hom between their factored objects. -/
def factorizationHomTensorLinearEquiv (hC : IsNondegenerate (C := C))
    (X X' Y Y' : C) :
    ((X ⟶ X') ⊗[ℂ] (Y ⟶ Y')) ≃ₗ[ℂ]
      ((positive C).obj X ⊗ (negative C).obj Y ⟶
        (positive C).obj X' ⊗ (negative C).obj Y') := by
  letI := (deligneFactorizationFullyFaithful S hC).full
  letI := (deligneFactorizationFullyFaithful S hC).faithful
  exact (fullyFaithfulHomLinearEquiv (Mat_.embedding (LinearTensor C C))
      (⟨X,Y⟩ : LinearTensor C C) ⟨X',Y'⟩).trans
    ((fullyFaithfulHomLinearEquiv (deligneFactorization C) _ _).trans
      (CategoryTheory.Linear.homCongr ℂ (deligneFactorizationPairIso X Y)
        (deligneFactorizationPairIso X' Y')))



/-- The proved Hom equivalence is the actual linear factorization map. -/
lemma factorizationHomTensorLinearEquiv_apply (hC : IsNondegenerate (C := C))
    {X X' Y Y' : C} (t : (X ⟶ X') ⊗[ℂ] (Y ⟶ Y')) :
    factorizationHomTensorLinearEquiv S hC X X' Y Y' t =
      (linearFactorization C).map
        (show (⟨X,Y⟩ : LinearTensor C C) ⟶ ⟨X',Y'⟩ from t) := by
  change ((deligneFactorizationPairIso X Y).inv ≫
    (deligneFactorization C).map
      ((Mat_.embedding (LinearTensor C C)).map
        (show (⟨X,Y⟩ : LinearTensor C C) ⟶ ⟨X',Y'⟩ from t))) ≫
          (deligneFactorizationPairIso X' Y').hom = _
  rw [assoc, deligneFactorizationPairIso_naturality, Iso.inv_hom_id_assoc]

@[simp]
lemma factorizationHomTensorLinearEquiv_tmul (hC : IsNondegenerate (C := C))
    {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    factorizationHomTensorLinearEquiv S hC X X' Y Y' (f ⊗ₜ[ℂ] g) =
      (positive C).map f ⊗ₘ (negative C).map g := by
  rw [factorizationHomTensorLinearEquiv_apply, linearFactorization_map_tmul]

include S in
/-- The actual linear tensor lift is fully faithful as well. -/
def linearFactorizationFullyFaithful (hC : IsNondegenerate (C := C)) :
    (linearFactorization C).FullyFaithful where
  preimage {X Y} h :=
    (factorizationHomTensorLinearEquiv S hC X.left Y.left X.right Y.right).symm h
  map_preimage {X Y} h := by
    rw [← factorizationHomTensorLinearEquiv_apply S hC]
    exact (factorizationHomTensorLinearEquiv S hC X.left Y.left X.right Y.right).apply_symm_apply h
  preimage_map {X Y} h := by
    rw [← factorizationHomTensorLinearEquiv_apply S hC]
    exact (factorizationHomTensorLinearEquiv S hC X.left Y.left X.right Y.right).symm_apply_apply h

end Paper18.Category.Drinfeld

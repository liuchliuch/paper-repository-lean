import Paper18.Category.LinearTensorDecomposition
import Paper18.Category.Multiplicity
import Mathlib.Algebra.Category.FGModuleCat.Limits
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Finite orthogonal presentations of the actual linear tensor product -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Limits
open scoped BigOperators TensorProduct
universe v u w v' u' w'
namespace Paper18.Category.DeligneProduct
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)

/-- The finite list of pairs of actual simple summands of a matrix object. -/
abbrev PresentationIndex (M : DeligneProduct C D) :=
  Σ m : M.ι, Fin (S.length (M.X m).left) × Fin (T.length (M.X m).right)

/-- Label of an actual simple pair in the flattened decomposition. -/
def presentationLabel (M : DeligneProduct C D) (a : PresentationIndex S T M) : ι × κ :=
  (S.label (M.X a.1).left a.2.1, T.label (M.X a.1).right a.2.2)

/-- Every actual object is a finite biproduct of actual embedded simple pairs. -/
def presentationIso (M : DeligneProduct C D) :
    M ≅ ⨁ fun a : PresentationIndex S T M =>
      pairObject S T (presentationLabel S T M a).1 (presentationLabel S T M a).2 :=
  Mat_.isoBiproductEmbedding M ≪≫
    biproduct.mapIso (fun m => pairDecompositionIso S T (M.X m).left (M.X m).right ≪≫
      Mat_.isoBiproductEmbedding (pairDecompositionObject S T (M.X m).left (M.X m).right)) ≪≫
    biproductBiproductIso
      (fun m : M.ι => Fin (S.length (M.X m).left) × Fin (T.length (M.X m).right))
      (fun m a => pairObject S T (S.label (M.X m).left a.1) (T.label (M.X m).right a.2))

/-- A finite-ordinal presentation, in the format used by the semisimple skeleton. -/
def finitePresentationIso (M : DeligneProduct C D) :
    M ≅ ⨁ fun a : Fin (Fintype.card (PresentationIndex S T M)) =>
      pairObject S T
        (presentationLabel S T M ((Fintype.equivFin (PresentationIndex S T M)).symm a)).1
        (presentationLabel S T M ((Fintype.equivFin (PresentationIndex S T M)).symm a)).2 :=
  presentationIso S T M ≪≫
    (biproduct.reindex (Fintype.equivFin (PresentationIndex S T M)).symm
      (fun a : PresentationIndex S T M =>
        pairObject S T (presentationLabel S T M a).1 (presentationLabel S T M a).2)).symm

/-- Embedded pair Hom spaces are the actual tensor products of factor Hom spaces. -/
def pairHomLinearEquiv (i k : ι) (j l : κ) :
    (pairObject S T i j ⟶ pairObject S T k l) ≃ₗ[ℂ]
      ((S.simpleObject i ⟶ S.simpleObject k) ⊗[ℂ]
        (T.simpleObject j ⟶ T.simpleObject l)) where
  toFun f := f PUnit.unit PUnit.unit
  invFun f _ _ := f
  left_inv f := by ext ⟨⟩ ⟨⟩; rfl
  right_inv f := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Schur's lemma in the factors gives orthogonality of actual pair Hom spaces. -/
theorem finrank_pair_hom (p q : ι × κ) :
    Module.finrank ℂ (pairObject S T p.1 p.2 ⟶ pairObject S T q.1 q.2) =
      if p = q then 1 else 0 := by
  rw [(pairHomLinearEquiv S T p.1 q.1 p.2 q.2).finrank_eq,
    Module.finrank_tensorProduct, S.finrank_simple_hom_simple, T.finrank_simple_hom_simple]
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  by_cases hi : i = k <;> by_cases hj : j = l <;> simp [hi, hj]

/-- The actual identity of a simple pair is nonzero. -/
theorem pair_id_ne_zero (p : ι × κ) : (𝟙 (pairObject S T p.1 p.2)) ≠ 0 := by
  have hr : Module.finrank ℂ
      (pairObject S T p.1 p.2 ⟶ pairObject S T p.1 p.2) = 1 := by
    simp [finrank_pair_hom]
  intro h
  obtain ⟨a, ha⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (show 0 < Module.finrank ℂ
    (pairObject S T p.1 p.2 ⟶ pairObject S T p.1 p.2) by omega)
  exact ha (by rw [← Category.id_comp a, h, zero_comp])

/-- Every endomorphism of a simple pair is a scalar multiple of its identity. -/
theorem pair_end_eq_smul (p : ι × κ)
    (f : pairObject S T p.1 p.2 ⟶ pairObject S T p.1 p.2) :
    ∃ c : ℂ, c • 𝟙 (pairObject S T p.1 p.2) = f :=
  exists_smul_eq_of_finrank_eq_one (by simp [finrank_pair_hom]) (pair_id_ne_zero S T p) f

/-- Morphisms between differently labeled pairs vanish. -/
theorem pair_hom_eq_zero {p q : ι × κ} (hpq : p ≠ q)
    (f : pairObject S T p.1 p.2 ⟶ pairObject S T q.1 q.2) : f = 0 := by
  have hr : Module.finrank ℂ
      (pairObject S T p.1 p.2 ⟶ pairObject S T q.1 q.2) = 0 := by
    simp [finrank_pair_hom, hpq]
  exact (Module.finrank_zero_iff.mp hr).elim f 0

end Paper18.Category.DeligneProduct

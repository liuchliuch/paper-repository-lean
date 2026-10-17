import Paper18.Category.DiagonalCondensationEmbedding

/-! # Actual mixed Hom coordinates for diagonal condensation -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators TensorProduct MonObj
universe v u v' u' vE uE w wC wD
namespace Paper18.Category.DiagonalCondensation
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [BraidedCategory D] [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {E : Type uE} [Category.{vE} E] [Preadditive E] [Linear ℂ E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalLinear ℂ E]
  [RightRigidCategory E] [HasKernels E] [HasFiniteBiproducts E]
  [∀ X Y : E, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ E)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton E ι)
  (F : E ⥤ C) [F.Monoidal] [F.Full] [F.Faithful] [F.Additive] [F.Linear ℂ]
  (G : E ⥤ D) [G.Monoidal] [G.Full] [G.Faithful] [G.Additive] [G.Linear ℂ]

/-- Actual rigid adjunction removes the dual factor from a mixed diagonal
coordinate. The pairing is transported by the actual tensor functor. -/
def mixedRightHomLinearEquiv (i : ι) (V : D) :
    (𝟙_ D ⟶ G.obj (dual E (S.simpleObject i)) ⊗ V) ≃ₗ[ℂ]
      (G.obj (S.simpleObject i) ⟶ V) := by
  letI := mapExactPairing G (S.simpleObject i) (dual E (S.simpleObject i))
  exact (CategoryTheory.Linear.homCongr ℂ (Iso.refl _)
    (β_ (G.obj (dual E (S.simpleObject i))) V)).trans
      ((tensorRightHomLinearEquiv (𝟙_ D) (G.obj (S.simpleObject i))
        (G.obj (dual E (S.simpleObject i))) V).symm.trans
          (CategoryTheory.Linear.homCongr ℂ (λ_ _) (Iso.refl _)))

variable {A : DeligneProduct C D} [MonObj A]
  (e : A ≅ ⨁ fun i => pair (F.obj (S.simpleObject i))
    (G.obj (dual E (S.simpleObject i))))

/-- The actual mixed free-module Hom space is the finite family of
actual matching Hom tensor products through the shared category. -/
def freeMixedHomLinearEquiv (X : C) (V : D) :
    ((leftFreeFunctor (A := A)).obj X ⟶ (rightFreeFunctor (A := A)).obj V) ≃ₗ[ℂ]
      (∀ i, (X ⟶ F.obj (S.simpleObject i)) ⊗[ℂ] (G.obj (S.simpleObject i) ⟶ V)) :=
  (freePairHomLinearEquiv _ _ e X (𝟙_ C) (𝟙_ D) V).trans
    (LinearEquiv.piCongrRight fun i => TensorProduct.congr
      (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) (ρ_ _))
      (mixedRightHomLinearEquiv S G i V))

include e in
/-- The actual mixed Hom rank follows from its proved linear universal
property and ordinary finite tensor-product dimensions. -/
lemma finrank_freeMixedHom_normalized (X : C) (V : D) :
    Module.finrank ℂ ((leftFreeFunctor (A := A)).obj X ⟶
      (rightFreeFunctor (A := A)).obj V) =
      ∑ i, Module.finrank ℂ (X ⟶ F.obj (S.simpleObject i)) *
        Module.finrank ℂ (G.obj (S.simpleObject i) ⟶ V) := by
  rw [(freeMixedHomLinearEquiv S F G e X V).finrank_eq, Module.finrank_pi_fintype]
  simp only [Module.finrank_tensorProduct]

end Paper18.Category.DiagonalCondensation

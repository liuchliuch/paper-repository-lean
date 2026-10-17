import Paper18.Category.DiagonalAlgebraSemisimplePairing

/-! # Actual perfect multiplication pairings on right-adjoint unit algebras -/
noncomputable section
set_option maxHeartbeats 1000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w v' u' w'
namespace Paper18.Category.DiagonalAlgebra

section FiniteIso
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

include S

/-- A split inclusion with equal finite endomorphism dimensions is an
actual isomorphism. -/
lemma isIso_of_mono_end_finrank_eq {X Y : C} (f : X ⟶ Y) [Mono f]
    (h : Module.finrank ℂ (X ⟶ X) = Module.finrank ℂ (Y ⟶ Y)) : IsIso f := by
  let s := S.splitMono f
  let P : (Y ⟶ Y) →ₗ[ℂ] (X ⟶ X) :=
    (CategoryTheory.Linear.rightComp ℂ X s.retraction).comp
      (CategoryTheory.Linear.leftComp ℂ Y f)
  have hs : Function.Surjective P := by
    intro a
    refine ⟨s.retraction ≫ a ≫ f, ?_⟩
    change (f ≫ (s.retraction ≫ a ≫ f)) ≫ s.retraction = a
    calc
      _ = (f ≫ s.retraction) ≫ a ≫ (f ≫ s.retraction) := by simp only [assoc]
      _ = a := by simp only [s.id, id_comp, comp_id]
  have hi : Function.Injective P :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h.symm (f := P)).mpr hs
  have hr : s.retraction ≫ f = 𝟙 Y := by
    apply hi
    change (f ≫ (s.retraction ≫ f)) ≫ s.retraction = (f ≫ 𝟙 Y) ≫ s.retraction
    simp only [← assoc, s.id, id_comp, comp_id]
  exact ⟨⟨s.retraction, s.id, hr⟩⟩
end FiniteIso

section Transpose
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
attribute [local instance 2000] RightRigidCategory.rightDual

/-- The actual transpose of a cap in its first factor. -/
def capTranspose (A : C) (b : A ⊗ A ⟶ 𝟙_ C) : A ⟶ Aᘁ :=
  tensorRightHomLinearEquiv A A Aᘁ (𝟙_ C) b ≫ (λ_ Aᘁ).hom

lemma capTranspose_evaluation (A : C) (b : A ⊗ A ⟶ 𝟙_ C) :
    capTranspose A b ▷ A ≫ ε_ A Aᘁ = b := by
  calc
    _ = (tensorRightHomEquiv A A Aᘁ (𝟙_ C) b) ▷ A ≫
        (α_ (𝟙_ C) Aᘁ A).hom ≫ (𝟙_ C ◁ ε_ A Aᘁ) ≫ (ρ_ (𝟙_ C)).hom := by
      dsimp only [capTranspose, tensorRightHomLinearEquiv]
      monoidal
    _ = b := (tensorRightHomEquiv A A Aᘁ (𝟙_ C)).symm_apply_apply b

end Transpose

section Adjoint
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [MonoidalCategory C] [RightRigidCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D] [MonoidalCategory D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [Simple (𝟙_ D)]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Monoidal]

include T

/-- The actual multiplication cap has an invertible actual transpose. -/
def adjointPairingTransposeIso : semisimpleAdjointAlgebra S F ≅ (semisimpleAdjointAlgebra S F)ᘁ := by
  let A := semisimpleAdjointAlgebra S F
  let b := μ[A] ≫ adjointFrobeniusCounit S F
  let φ := capTranspose A b
  letI : Mono φ := Preadditive.mono_of_cancel_zero φ (fun {Y} g hg => by
    apply adjointAlgebra_pairing_nondegenerate S T F Y g
    change g ▷ A ≫ b = 0
    rw [← capTranspose_evaluation A b, ← comp_whiskerRight_assoc]
    change (g ≫ φ) ▷ A ≫ ε_ A Aᘁ = 0
    rw [hg]
    simp)
  letI : IsIso φ := isIso_of_mono_end_finrank_eq S φ (finrank_rightDual_hom A A).symm
  exact asIso φ

/-- The actual perfect multiplication pairing is derived, including both
snake identities; no Frobenius or nondegeneracy laws are inputs. -/
def adjointMultiplicationPairing : ModuleBalancing.MultiplicationPairing (semisimpleAdjointAlgebra S F) where
  counit := adjointFrobeniusCounit S F
  pairing := exactPairingCongrRight (adjointPairingTransposeIso S T F)
  evaluation := capTranspose_evaluation _ _

end Adjoint
end Paper18.Category.DiagonalAlgebra

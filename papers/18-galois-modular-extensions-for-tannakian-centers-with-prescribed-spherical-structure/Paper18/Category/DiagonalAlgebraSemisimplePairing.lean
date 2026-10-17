import Paper18.Category.DiagonalAlgebraSemisimpleUnit
import Paper18.Category.DiagonalAlgebraPairingCounit
import Paper18.Category.PivotalFunctor

/-! # Zero radical of actual right-adjoint unit multiplication

Actual cap functionals lift through the proved right adjunction. Rigid
contraction then detects every possible radical morphism. All arguments
work for finite semisimple tensor functors without nondegeneracy inputs.
-/
noncomputable section
set_option maxHeartbeats 1000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w v' u' w'
namespace Paper18.Category.DiagonalAlgebra
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

/-- The actual normalized counit of the connected right-adjoint algebra. -/
def adjointFrobeniusCounit : semisimpleAdjointAlgebra S F ⟶ 𝟙_ C :=
  connectedCounit S _ (semisimpleAdjointAlgebra_connected S F)

/-- Lift the cap-dual of an actual underlying unit vector. -/
def adjointPairingLift (Y : C) (q : 𝟙_ D ⟶ F.obj Y) :
    Yᘁ ⟶ semisimpleAdjointAlgebra S F := by
  letI := mapExactPairing F Y Yᘁ
  exact (semisimpleRightAdjunction S F).homEquiv (Yᘁ) (𝟙_ D)
    (capFunctional (F.obj Y) (F.obj Yᘁ) q)

lemma adjointPairingLift_counit (Y : C) (q : 𝟙_ D ⟶ F.obj Y) :
    letI := mapExactPairing F Y Yᘁ
    F.map (adjointPairingLift S F Y q) ≫ semisimpleAdjointAlgebraCounit S F =
      capFunctional (F.obj Y) (F.obj Yᘁ) q := by
  letI := mapExactPairing F Y Yᘁ
  simpa only [Adjunction.homEquiv_counit] using
    ((semisimpleRightAdjunction S F).homEquiv (Yᘁ) (𝟙_ D)).symm_apply_apply
      (capFunctional (F.obj Y) (F.obj Yᘁ) q)

include T

/-- The actual multiplication pairing of a right-adjoint unit has zero
left radical, proved by actual adjunction and rigid triangle identities. -/
lemma adjointAlgebra_pairing_nondegenerate (Y : C) (g : Y ⟶ semisimpleAdjointAlgebra S F)
    (h : g ▷ semisimpleAdjointAlgebra S F ≫ μ[semisimpleAdjointAlgebra S F] ≫
      adjointFrobeniusCounit S F = 0) : g = 0 := by
  have hcomp (q : 𝟙_ D ⟶ F.obj Y) : q ≫ (F.map g ≫ semisimpleAdjointAlgebraCounit S F) = 0 := by
    letI := mapExactPairing F Y Yᘁ
    let t := adjointPairingLift S F Y q
    let k : 𝟙_ C ⟶ semisimpleAdjointAlgebra S F :=
      η_ Y Yᘁ ≫ (g ⊗ₘ t) ≫ μ[semisimpleAdjointAlgebra S F]
    have hkcap : k ≫ adjointFrobeniusCounit S F = 0 := by
      dsimp only [k]
      simp only [assoc]
      rw [MonoidalCategory.tensorHom_def']
      simp only [assoc]
      rw [h, comp_zero, comp_zero]
    have hk : k = 0 := connectedCounit_detects_zero S _
      (semisimpleAdjointAlgebra_connected S F) k hkcap
    have hkf : Functor.LaxMonoidal.ε F ≫ F.map k ≫ semisimpleAdjointAlgebraCounit S F = 0 := by
      rw [hk, Functor.map_zero, zero_comp, comp_zero]
    have hx : Functor.LaxMonoidal.ε F ≫ F.map k ≫ semisimpleAdjointAlgebraCounit S F =
        η_ (F.obj Y) (F.obj Yᘁ) ≫
          ((F.map g ≫ semisimpleAdjointAlgebraCounit S F) ⊗ₘ
            capFunctional (F.obj Y) (F.obj Yᘁ) q) ≫ (λ_ (𝟙_ D)).hom := by
      dsimp only [k]
      simp only [Functor.map_comp, assoc]
      rw [semisimpleAdjointAlgebra_mul_counit]
      rw [← Functor.OplaxMonoidal.δ_natural_assoc]
      rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
      rw [show F.map t ≫ semisimpleAdjointAlgebraCounit S F =
        capFunctional (F.obj Y) (F.obj Yᘁ) q from adjointPairingLift_counit S F Y q]
      have hc : η_ (F.obj Y) (F.obj Yᘁ) = Functor.LaxMonoidal.ε F ≫
          F.map (η_ Y Yᘁ) ≫ Functor.OplaxMonoidal.δ F Y Yᘁ := rfl
      rw [hc]
      simp only [assoc]
    rw [hx, cup_capFunctional] at hkf
    exact hkf
  have hg : F.map g ≫ semisimpleAdjointAlgebraCounit S F = 0 := by
    apply T.hom_ext_simples
    intro i a
    have hu : Module.finrank ℂ (T.simpleObject i ⟶ 𝟙_ D) = if i = T.unitLabel then 1 else 0 := by
      rw [← finrank_hom_iso (Iso.refl (T.simpleObject i)) T.unitIso]
      exact T.finrank_simple_hom_simple i T.unitLabel
    by_cases hi : i = T.unitLabel
    · subst i
      apply (cancel_epi T.unitIso.inv).mp
      simpa only [assoc, comp_zero] using hcomp (T.unitIso.inv ≫ a)
    · have hz : Module.finrank ℂ (T.simpleObject i ⟶ 𝟙_ D) = 0 := by rw [hu, if_neg hi]
      exact (Module.finrank_zero_iff.mp hz).elim _ _
  apply ((semisimpleRightAdjunction S F).homEquiv Y (𝟙_ D)).symm.injective
  change F.map g ≫ semisimpleAdjointAlgebraCounit S F =
    F.map (0 : Y ⟶ semisimpleAdjointAlgebra S F) ≫ _
  simpa using hg

end Paper18.Category.DiagonalAlgebra

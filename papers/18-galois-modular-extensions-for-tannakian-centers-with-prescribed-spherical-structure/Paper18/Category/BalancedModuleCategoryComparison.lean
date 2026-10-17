import Paper18.Category.BalancedModuleCategoryTransformation
import Paper18.Category.BalancedModuleCategoryPairGenerators

/-! # Unique actual descent of all balanced natural comparison maps -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u vE uE
namespace Paper18.Category.BalancedModuleCategory
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  {A B : D} [MonObj A] [MonObj B]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {E : Type uE} [Category.{vE} E]
  {F G : BimoduleRelativeTensor.Native A B ⥤ E}
  (τ : external (A := A) (B := B) ⋙ F ⟶ external ⋙ G)

omit [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] in
theorem balancedNatural_inv (hτ : IsBalancedNatural τ)
    (M : Mod_ D A) (X : D) (N : RightModules B) :
    F.map (balancingIso M X N).inv ≫ τ.app (RelativeTensor.ambientTensor M X, N) =
      τ.app (M, rightAmbientTensor N X) ≫ G.map (balancingIso M X N).inv := by
  apply (cancel_epi (F.map (balancingIso M X N).hom)).mp
  rw [← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, id_comp]
  rw [reassoc_of% hτ M X N, ← G.map_comp, Iso.hom_inv_id, G.map_id, comp_id]

variable (SA : SeparableAlgebra A) (SB : SeparableAlgebra B)

omit [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] in
theorem pairGeneratorSection_naturality (hτ : IsBalancedNatural τ)
    (M : Mod_ D A) (N : RightModules B) :
    F.map (pairGeneratorRetract SA SB M N).i ≫
        τ.app (InternalModule.free A (M.X ⊗ rightUnderlying N), Mod_.regular (mop B)) =
      τ.app (M, N) ≫ G.map (pairGeneratorRetract SA SB M N).i := by
  have hM := τ.naturality (CategoryTheory.Prod.mkHom
    (leftFreeRetract SA (RelativeTensor.ambientTensor M (rightUnderlying N))).i
      (𝟙 (Mod_.regular (mop B))))
  have hN := τ.naturality (CategoryTheory.Prod.mkHom (𝟙 M) (rightFreeRetract SB N).i)
  simp only [Functor.comp_map, Mod_.regular] at hM hN
  rw [pairGeneratorRetract_i]
  simp only [Functor.map_comp, assoc]
  have hs := compose_square (compose_square hN
    (balancedNatural_inv τ hτ M (rightUnderlying N) (Mod_.regular (mop B)))) hM
  simpa only [assoc] using hs

/-- The actual comparison extension agrees with the given balanced map
on every external pair, not only on free generators. -/
theorem extendBalancedNatTrans_external (hτ : IsBalancedNatural τ)
    (M : Mod_ D A) (N : RightModules B) :
    (extendBalancedNatTrans SA SB τ hτ).app (externalObj M N) = τ.app (M, N) := by
  let σ := extendBalancedNatTrans SA SB τ hτ
  let R := pairGeneratorRetract SA SB M N
  calc
    σ.app (externalObj M N) = F.map R.i ≫ σ.app _ ≫ G.map R.r := by
      rw [σ.naturality_assoc, ← G.map_comp, R.retract, G.map_id, comp_id]
    _ = F.map R.i ≫ τ.app (InternalModule.free A (M.X ⊗ rightUnderlying N), Mod_.regular (mop B)) ≫
        G.map R.r := by rw [extendBalancedNatTrans_free]
    _ = τ.app (M, N) := by
      rw [reassoc_of% pairGeneratorSection_naturality τ SA SB hτ M N,
        ← G.map_comp, R.retract, G.map_id (externalObj M N)]
      exact comp_id _

include SA SB in
/-- The map part of the balanced-product universal property is proved
from free-coordinate factorization and the two actual separable sections.
No universal-property or full-faithfulness certificate is a hypothesis. -/
theorem exists_unique_balanced_extension (hτ : IsBalancedNatural τ) :
    ∃! σ : F ⟶ G, ∀ (M : Mod_ D A) (N : RightModules B),
      σ.app (externalObj M N) = τ.app (M, N) := by
  refine ⟨extendBalancedNatTrans SA SB τ hτ,
    extendBalancedNatTrans_external τ SA SB hτ, ?_⟩
  intro σ hσ
  apply natTrans_ext SA SB
  intro M N
  exact (hσ M N).trans (extendBalancedNatTrans_external τ SA SB hτ M N).symm

end Paper18.Category.BalancedModuleCategory

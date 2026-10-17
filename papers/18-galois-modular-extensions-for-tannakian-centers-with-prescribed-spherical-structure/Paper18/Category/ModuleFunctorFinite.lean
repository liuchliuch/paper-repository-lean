import Paper18.Category.ModuleFunctorFiniteBasic
import Paper18.Category.EquivariantInduction

/-! # Finite-dimensional Hom spaces of actual module functors

Evaluation on actual chosen simple representatives is proved injective
using the genuine biproduct decomposition and naturality. Module natural
transformations are then a genuine subspace of this finite vector space.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u v' u' v'' u'' w
namespace Paper18.Category.ModuleFunctor

section NaturalTransformations
variable {M : Type u'} [Category.{v'} M] [Preadditive M] [HasFiniteBiproducts M]
  {N : Type u''} [Category.{v''} N] [Preadditive N] [Linear ℂ N]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton M ι)
  (F G : M ⥤ N) [F.Additive]

/-- Actual natural transformations are determined by their components on
the actual finite family of simple representatives. -/
theorem natTrans_ext_simples (τ σ : F ⟶ G)
    (h : ∀ i, τ.app (S.simpleObject i) = σ.app (S.simpleObject i)) : τ = σ := by
  ext X
  let f := fun a : Fin (S.length X) => S.simpleObject (S.label X a)
  have hb : τ.app (⨁ f) = σ.app (⨁ f) := by
    apply Paper18.Category.map_biproduct_hom_ext F f
    intro a
    rw [τ.naturality, σ.naturality, h (S.label X a)]
  apply (cancel_epi (F.map (S.decomposition X).inv)).mp
  rw [τ.naturality, σ.naturality, hb]

/-- Evaluation on actual simples, as a genuine complex-linear map. -/
def simpleEvaluationLinearMap : (F ⟶ G) →ₗ[ℂ]
    (∀ i : ι, F.obj (S.simpleObject i) ⟶ G.obj (S.simpleObject i)) where
  toFun τ i := τ.app (S.simpleObject i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem simpleEvaluationLinearMap_injective :
    Function.Injective (simpleEvaluationLinearMap S F G) := by
  intro τ σ h
  exact natTrans_ext_simples S F G τ σ (fun i => congrFun h i)

variable [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]

/-- Finite-dimensionality follows from actual finite simple evaluation. -/
def finiteDimensionalNatTrans : FiniteDimensional ℂ (F ⟶ G) :=
  FiniteDimensional.of_injective (simpleEvaluationLinearMap S F G)
    (simpleEvaluationLinearMap_injective S F G)

theorem finrank_natTrans_le : Module.finrank ℂ (F ⟶ G) ≤
    ∑ i : ι, Module.finrank ℂ (F.obj (S.simpleObject i) ⟶ G.obj (S.simpleObject i)) := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (simpleEvaluationLinearMap_injective S F G)
  simpa only [Module.finrank_pi_fintype] using h

end NaturalTransformations

section ModuleFunctors
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type u'} [Category.{v'} M] [Preadditive M] [Linear ℂ M]
  [HasFiniteBiproducts M] [MonoidalLeftAction C M]
  {N : Type u''} [Category.{v''} N] [Preadditive N] [Linear ℂ N]
  [MonoidalLeftAction C N]
  [∀ X : C, (MonoidalLeftAction.actionLeft N X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft N X).Linear ℂ]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton M ι)

/-- The Hom spaces of the actual bundled strong module-functor category
are finite-dimensional; no representative or classification is assumed. -/
def finiteDimensionalHom (F G : Bundled C M N) : FiniteDimensional ℂ (F ⟶ G) := by
  letI := finiteDimensionalNatTrans S F.toFunctor G.toFunctor
  change FiniteDimensional ℂ (homSubmodule F G)
  infer_instance

end ModuleFunctors
end Paper18.Category.ModuleFunctor

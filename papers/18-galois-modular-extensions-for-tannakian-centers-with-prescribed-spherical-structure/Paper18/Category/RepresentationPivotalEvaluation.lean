import Paper18.Category.RepresentationPivotal

/-! # The canonical representation pivotal map is functional evaluation -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe u
namespace Paper18.Category.Representation
attribute [local instance 2000] RightRigidCategory.rightDual
variable {G : Type} [Group G]

/-- The native representation evaluation is ordinary vector contraction;
this also unfolds the exact pairing transported through the action/functor
category equivalence. -/
lemma evaluation_underlying (V : FDRep ℂ G) :
    (ε_ V (dual (FDRep ℂ G) V)).hom = ε_ V.V (dual (FGModuleCat ℂ) V.V) := by
  let F := Action.FunctorCategoryEquivalence.functor (V := FGModuleCat ℂ) (G := G)
  change (F.map (F.preimage _)).app PUnit.unit = _
  rw [F.map_preimage]
  simp [ExactPairing.evaluation, exactPairingCongrRight, Adjunction.toEquivalence,
    Action.functorCategoryEquivalence, Action.FunctorCategoryEquivalence.counitIso]
  apply FGModuleCat.hom_ext
  ext t
  rfl

/-- The actual equivariant pivotal map sends a vector to functional
evaluation on its dual, as in the ordinary finite-dimensional model. -/
lemma pivotalStructure_apply (V : FDRep ℂ G) (v : V) (φ : Module.Dual ℂ V) :
    (show Module.Dual ℂ (Module.Dual ℂ V) from
      ((pivotalStructure (G := G)).j.hom.app V).hom.hom v) φ = φ v := by
  have h := congrArg (fun q : V ⊗ dual (FDRep ℂ G) V ⟶ 𝟙_ (FDRep ℂ G) =>
    q.hom.hom (v ⊗ₜ[ℂ] φ)) (drinfeldIso_evaluation V)
  simp only [Action.comp_hom, evaluation_underlying] at h
  exact h

end Paper18.Category.Representation

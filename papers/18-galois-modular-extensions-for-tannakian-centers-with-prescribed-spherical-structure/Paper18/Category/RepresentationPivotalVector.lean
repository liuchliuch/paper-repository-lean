import Paper18.Category.RepresentationPivotalBasic
import Paper18.Category.SphericalizationFunctor
import Mathlib.LinearAlgebra.Trace

/-! # The canonical pivotal maps and actual traces on finite vector spaces -/
noncomputable section
open Classical Module
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u v' u'
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual

section Functor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [SymmetricCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  [RightRigidCategory D] [SymmetricCategory D]
  (F : C ⥤ D) [F.Braided]

/-- Braided tensor functors preserve the actual canonical symmetric
pivotal comparison, by the canonical dual comparison theorem. -/
lemma symmetricPivotal_preserves : PreservesPivotal F symmetricPivotal symmetricPivotal := by
  intro X
  exact doubleDualComparison_drinfeld F X
end Functor

namespace Representation

/-- The native categorical double-dual comparison is actual vector
functional evaluation. This identifies the abstract rigid construction
with the usual finite-dimensional evaluation map. -/
lemma vectorPivotal_apply (V : FGModuleCat ℂ) (v : V) (φ : Module.Dual ℂ V) :
    (show Module.Dual ℂ (Module.Dual ℂ V) from (symmetricPivotal.j.hom.app V).hom v) φ = φ v := by
  have h := congrArg (fun q : V ⊗ dual (FGModuleCat ℂ) V ⟶ 𝟙_ (FGModuleCat ℂ) =>
    q.hom (v ⊗ₜ[ℂ] φ)) (drinfeldIso_evaluation V)
  change (show Module.Dual ℂ (Module.Dual ℂ V) from (symmetricPivotal.j.hom.app V).hom v) φ = φ v at h
  exact h

/-- The actual canonical pivotal trace of a finite vector space is its
ordinary dimension, derived from its native coevaluation basis sum and
the actual flip/evaluation morphisms. -/
lemma vectorPivotal_rightDimension (V : FGModuleCat ℂ) :
    symmetricPivotal.rightDimension V =
      (Module.finrank ℂ V : ℂ) • 𝟙 (𝟙_ (FGModuleCat ℂ)) := by
  simp only [PivotalStructure.rightDimension, PivotalStructure.rightTrace,
    id_whiskerRight, id_comp, symmetricPivotal_leftEvaluation]
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change ℂ at c
  change contractLeft ℂ V ((TensorProduct.comm ℂ V (Module.Dual ℂ V))
    (coevaluation ℂ V c)) = (Module.finrank ℂ V : ℂ) * c
  have hc : coevaluation ℂ V c = c • coevaluation ℂ V 1 := by
    simpa only [smul_eq_mul, mul_one] using (coevaluation ℂ V).map_smul c (1 : ℂ)
  rw [hc, map_smul, map_smul, coevaluation_apply_one, map_sum, map_sum]
  simp only [TensorProduct.comm_tmul, contractLeft_apply, Basis.coord_apply, Basis.repr_self_apply, ite_true]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
  rw [← Module.finrank_eq_card_basis (Basis.ofVectorSpace ℂ V)]
  ring

variable {G : Type} [Group G]

/-- The actual forgetful tensor functor preserves the constructed pivotal
structure; this is proved from braided rigid comparisons, not assumed as
a trace-preservation field. -/
lemma forget_preservesPivotal : PreservesPivotal
    (Action.forget (FGModuleCat ℂ) G) pivotalStructure symmetricPivotal :=
  symmetricPivotal_preserves _

end Representation
end Paper18.Category

import Paper18.Category.ModuleFunctorAdjointLax
import Paper18.Category.ModuleFunctorAdjointAction
import Paper18.Category.FixedBoundaryModuleStrong
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Rigidity makes the actual right-adjoint lineator invertible -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u v' u' v'' u''
namespace Paper18.Category.ModuleFunctor
open MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type u'} [Category.{v'} M] [MonoidalLeftAction C M]
  {N : Type u''} [Category.{v''} N] [MonoidalLeftAction C N]
  (F : M ⥤ N) [F.LeftLinear C]

/-- The strong module lineator, regarded as an actual natural isomorphism
between the two composites with an action functor. -/
def adjointActionLineatorIso (c : C) : F ⋙ actionLeft N c ≅ actionLeft M c ⋙ F :=
  NatIso.ofComponents (fun m => Functor.LeftLinear.μₗIso F c m)
    (fun f => Functor.LaxLeftLinear.μₗ_naturality_right F c f)

variable {G : N ⥤ M}

section Pairing
variable (c d : C) [ExactPairing c d]

/-- Strong module functors intertwine actual action caps. This is derived
from the actual lineator associativity, naturality and unit coherence. -/
lemma lineator_actionEvaluation (m : M) :
    (d ⊴ₗ Functor.LaxLeftLinear.μₗ F c m) ≫
      Functor.LaxLeftLinear.μₗ F d (c ⊙ₗ m) ≫
        F.map ((actionEvaluation M c d).app m) =
      (actionEvaluation N c d).app (F.obj m) := by
  simp only [actionEvaluation_app, F.map_comp]
  rw [Functor.LaxLeftLinear.μₗ_associativity_inv_assoc,
    ← Functor.LaxLeftLinear.μₗ_naturality_left_assoc,
    ← Functor.LaxLeftLinear.μₗ_unitality]

/-- An equivalent cap identity, with the inverse of the first lineator. -/
lemma lineator_actionEvaluation_oplax (m : M) :
    Functor.LaxLeftLinear.μₗ F d (c ⊙ₗ m) ≫
      F.map ((actionEvaluation M c d).app m) =
    (d ⊴ₗ Functor.OplaxLeftLinear.δₗ F c m) ≫
      (actionEvaluation N c d).app (F.obj m) := by
  apply (cancel_epi (d ⊴ₗ Functor.LaxLeftLinear.μₗ F c m)).mp
  rw [lineator_actionEvaluation]
  simp only [← assoc, ← actionHomRight_comp,
    Functor.LeftLinear.μₗ_comp_δₗ, actionHomRight_id, id_comp]

variable (adj : F ⊣ G)

/-- The actual comparison of right adjoints, obtained by conjugating the
strong lineator on the dual action through actual composite adjunctions. -/
def rigidRightAdjointComparison :
    G ⋙ actionLeft M c ≅ actionLeft N c ⋙ G :=
  (conjugateIsoEquiv ((actionAdjunction M c d).comp adj)
    (adj.comp (actionAdjunction N c d))) (adjointActionLineatorIso F d)

lemma rigidRightAdjointComparison_counit (n : N) :
    d ⊴ₗ (F.map ((rigidRightAdjointComparison F c d adj).hom.app n) ≫
      adj.counit.app (c ⊙ₗ n)) ≫ (actionEvaluation N c d).app n =
      Functor.LaxLeftLinear.μₗ F d (c ⊙ₗ G.obj n) ≫
        F.map ((actionEvaluation M c d).app (G.obj n)) ≫ adj.counit.app n := by
  have h := conjugateEquiv_counit ((actionAdjunction M c d).comp adj)
    (adj.comp (actionAdjunction N c d)) (adjointActionLineatorIso F d).hom n
  simpa only [rigidRightAdjointComparison, conjugateIsoEquiv_apply_hom,
    Adjunction.comp_counit_app, actionAdjunction_counit,
    Functor.comp_map, actionLeft_map, NatIso.ofComponents_hom_app,
    adjointActionLineatorIso, Functor.LeftLinear.μₗIso, assoc, actionHomRight_comp] using h

/-- The canonical mate lineator is precisely the actual isomorphism of
right adjoints. Strongness is therefore proved, rather than supplied. -/
lemma rigidRightAdjointComparison_hom_app (n : N) :
    (rigidRightAdjointComparison F c d adj).hom.app n =
      rightAdjointLineator adj c n := by
  apply (adj.homEquiv _ _).symm.injective
  change F.map ((rigidRightAdjointComparison F c d adj).hom.app n) ≫
    adj.counit.app (c ⊙ₗ n) =
      F.map (rightAdjointLineator adj c n) ≫ adj.counit.app (c ⊙ₗ n)
  rw [rightAdjointLineator_counit]
  apply ((actionAdjunction N c d).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  change d ⊴ₗ (F.map ((rigidRightAdjointComparison F c d adj).hom.app n) ≫
      adj.counit.app (c ⊙ₗ n)) ≫ (actionEvaluation N c d).app n =
    d ⊴ₗ (Functor.OplaxLeftLinear.δₗ F c (G.obj n) ≫ c ⊴ₗ adj.counit.app n) ≫
      (actionEvaluation N c d).app n
  have hn := (actionEvaluation N c d).naturality (adj.counit.app n)
  change d ⊴ₗ c ⊴ₗ adj.counit.app n ≫ (actionEvaluation N c d).app n =
    (actionEvaluation N c d).app (F.obj (G.obj n)) ≫ adj.counit.app n at hn
  rw [rigidRightAdjointComparison_counit, actionHomRight_comp, assoc, hn]
  simpa only [assoc] using congrArg (fun f => f ≫ adj.counit.app n)
    (lineator_actionEvaluation_oplax F c d (G.obj n))

end Pairing

section Rigid
variable [RightRigidCategory C] (adj : F ⊣ G)
attribute [local instance 2000] RightRigidCategory.rightDual

/-- Every actual mate lineator of the ordinary right adjoint is invertible
when the acting category has actual right duals. -/
lemma rightAdjointLineator_isIso (c : C) (n : N) :
    IsIso (rightAdjointLineator adj c n) := by
  rw [← rigidRightAdjointComparison_hom_app F c cᘁ adj n]
  infer_instance

/-- The actual strong module structure on an ordinary right adjoint. -/
def rightAdjointLeftLinear : G.LeftLinear C := by
  letI := rightAdjointLaxLeftLinear (C := C) adj
  letI (c : C) (n : N) : IsIso (Functor.LaxLeftLinear.μₗ G c n) :=
    rightAdjointLineator_isIso F adj c n
  exact leftLinearOfLax G

end Rigid
end Paper18.Category.ModuleFunctor

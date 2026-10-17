import Paper18.Category.ModuleFunctorFiniteHomogeneous
import Paper18.Category.FixedBoundaryOddConnected

/-! # Actual one-object density of homogeneous module functors

Neutral tensor connectivity provides actual retracts from the action on a
single homogeneous simple. Thus module natural transformations are detected
on that actual object; this is proved for all transformations, including
noninvertible ones.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u v' u' v'' u'' w
namespace Paper18.Category.ModuleFunctor

section Action
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type u'} [Category.{v'} M] [MonoidalLeftAction C M]
  {N : Type u''} [Category.{v''} N] [MonoidalLeftAction C N]
  {F G : M ⥤ N} [F.LeftLinear C] [G.LeftLinear C]

theorem moduleNatTrans_app_action_eq (τ σ : F ⟶ G)
    [IsModuleNatural C τ] [IsModuleNatural C σ]
    (X : C) (Y : M) (h : τ.app Y = σ.app Y) :
    τ.app (X ⊙ₗ Y) = σ.app (X ⊙ₗ Y) := by
  apply (cancel_epi (Functor.LaxLeftLinear.μₗ F X Y)).mp
  rw [IsModuleNatural.lineator, IsModuleNatural.lineator, h]

end Action

section Retract
variable {M : Type u'} [Category.{v'} M] {N : Type u''} [Category.{v''} N]
  {F G : M ⥤ N}

theorem natTrans_app_eq_of_retract (τ σ : F ⟶ G) {X Y : M}
    (R : Retract X Y) (h : τ.app Y = σ.app Y) : τ.app X = σ.app X := by
  have he := congrArg (fun k => F.map R.i ≫ k ≫ G.map R.r) h
  simpa only [τ.naturality_assoc, σ.naturality_assoc, ← G.map_comp,
    R.retract, G.map_id, Category.comp_id] using he

end Retract
end Paper18.Category.ModuleFunctor

namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom] (d : ZMod 2)
  {N : Type u''} [Category.{v''} N] [Preadditive N] [Linear ℂ N]
  [MonoidalLeftAction (SignKernel.Positive χ) N]

section Transformations
variable
  (F G : HomogeneousCategory χ d ⥤ N)
  [F.LeftLinear (SignKernel.Positive χ)] [G.LeftLinear (SignKernel.Positive χ)] [F.Additive]

/-- Actual module natural transformations on a homogeneous component are
determined by a single actual homogeneous simple, using actual neutral
tensor connectivity and actual retracts. -/
theorem homogeneousModuleNatTrans_ext (τ σ : F ⟶ G)
    [ModuleFunctor.IsModuleNatural (SignKernel.Positive χ) τ]
    [ModuleFunctor.IsModuleNatural (SignKernel.Positive χ) σ]
    (j : ι) (hj : Homogeneous χ d (S.simpleObject j))
    (h : τ.app ⟨S.simpleObject j, hj⟩ = σ.app ⟨S.simpleObject j, hj⟩) : τ = σ := by
  apply ModuleFunctor.natTrans_ext_simples (homogeneousSkeleton χ d S) F G τ σ
  intro i
  obtain ⟨k, hk, hn⟩ := neutral_tensor_connects S χ j i.val hj i.property
  let X : SignKernel.Positive χ := ⟨S.simpleObject k, by
    rw [SignKernel.mem_positive]
    simpa only [Homogeneous, paritySign_zero, one_smul] using hk⟩
  let Y : HomogeneousCategory χ d := ⟨S.simpleObject j, hj⟩
  let r := S.retractOfMultiplicityPos (S.simpleObject k ⊗ S.simpleObject j) i.val hn
  let R : Retract ((homogeneousSkeleton χ d S).simpleObject i) (X ⊙ₗ Y) :=
    ⟨r.i, r.r, r.retract⟩
  exact ModuleFunctor.natTrans_app_eq_of_retract τ σ R
    (ModuleFunctor.moduleNatTrans_app_action_eq τ σ X Y h)

end Transformations

section Evaluations
variable [∀ X : SignKernel.Positive χ, (MonoidalLeftAction.actionLeft N X).Additive]
  [∀ X : SignKernel.Positive χ, (MonoidalLeftAction.actionLeft N X).Linear ℂ]

/-- Genuine evaluation on one actual homogeneous simple, on actual module
natural transformations as a complex-linear map. -/
def homogeneousEvaluationLinearMap
    (F G : ModuleFunctor.Bundled (SignKernel.Positive χ) (HomogeneousCategory χ d) N)
    (j : ι) (hj : Homogeneous χ d (S.simpleObject j)) :
    (F ⟶ G) →ₗ[ℂ]
      (F.toFunctor.obj ⟨S.simpleObject j, hj⟩ ⟶ G.toFunctor.obj ⟨S.simpleObject j, hj⟩) where
  toFun τ := τ.val.app ⟨S.simpleObject j, hj⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem homogeneousEvaluationLinearMap_injective
    (F G : ModuleFunctor.Bundled (SignKernel.Positive χ) (HomogeneousCategory χ d) N)
    (j : ι) (hj : Homogeneous χ d (S.simpleObject j)) :
    Function.Injective (homogeneousEvaluationLinearMap S χ d F G j hj) := by
  intro τ σ h
  apply ModuleFunctor.bundled_hom_ext
  exact homogeneousModuleNatTrans_ext S χ d F.toFunctor G.toFunctor τ.val σ.val j hj h

variable [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]

/-- The actual module Hom dimension is bounded by a single actual finite
Hom space, because actual neutral tensor connectivity detects every map. -/
theorem homogeneousModuleHom_finrank_le
    (F G : ModuleFunctor.Bundled (SignKernel.Positive χ) (HomogeneousCategory χ d) N)
    (j : ι) (hj : Homogeneous χ d (S.simpleObject j)) :
    Module.finrank ℂ (F ⟶ G) ≤ Module.finrank ℂ
      (F.toFunctor.obj ⟨S.simpleObject j, hj⟩ ⟶ G.toFunctor.obj ⟨S.simpleObject j, hj⟩) :=
  LinearMap.finrank_le_finrank_of_injective
    (homogeneousEvaluationLinearMap_injective S χ d F G j hj)

end Evaluations

end Paper18.Category.FixedBoundary

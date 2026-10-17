import Paper18.Category.BalancedModuleCategoryFreeNaturality

/-! # Actual descent of balanced comparison maps using separable sections -/
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
variable (SA : SeparableAlgebra A) (SB : SeparableAlgebra B)
  {E : Type uE} [Category.{vE} E]
  {F G : BimoduleRelativeTensor.Native A B ⥤ E}
  (τ : external (A := A) (B := B) ⋙ F ⟶ external ⋙ G)

/-- The comparison component on an arbitrary native bimodule is an
explicit composite through its actual separable free retraction. -/
def extendApp (P : BimoduleRelativeTensor.Native A B) : F.obj P ⟶ G.obj P :=
  let R := externalFreeRetract SA SB P
  F.map R.i ≫ τ.app (InternalModule.free A P.X.X, Mod_.regular (mop B)) ≫ G.map R.r

theorem extendApp_naturality (hτ : IsBalancedNatural τ)
    {P Q : BimoduleRelativeTensor.Native A B} (f : P ⟶ Q) :
    F.map f ≫ extendApp SA SB τ Q = extendApp SA SB τ P ≫ G.map f := by
  let R := externalFreeRetract SA SB P
  let S := externalFreeRetract SA SB Q
  have h := free_naturality τ hτ (R.r ≫ f ≫ S.i)
  have hh := congrArg (fun k => F.map R.i ≫ k ≫ G.map S.r) h
  simp only [Functor.map_comp, assoc] at hh
  rw [← F.map_comp_assoc, R.retract, F.map_id, id_comp] at hh
  rw [← G.map_comp, S.retract, G.map_id, comp_id] at hh
  simpa only [extendApp, assoc] using hh

/-- A balanced comparison of restricted functors descends to an actual
natural transformation on all native bimodules. -/
def extendBalancedNatTrans (hτ : IsBalancedNatural τ) : F ⟶ G where
  app := extendApp SA SB τ
  naturality _ _ f := extendApp_naturality SA SB τ hτ f

/-- The constructed extension has the prescribed values on every actual
external free generator. -/
lemma extendBalancedNatTrans_free (hτ : IsBalancedNatural τ) (X : D) :
    (extendBalancedNatTrans SA SB τ hτ).app
      (externalObj (InternalModule.free A X) (Mod_.regular (mop B))) =
        τ.app (InternalModule.free A X, Mod_.regular (mop B)) := by
  let P := externalObj (InternalModule.free A X) (Mod_.regular (mop B))
  let R := externalFreeRetract SA SB P
  have h := free_naturality τ hτ (X := X) (Y := P.X.X) R.i
  change F.map R.i ≫ τ.app (InternalModule.free A P.X.X, Mod_.regular (mop B)) ≫ G.map R.r = _
  rw [reassoc_of% h, ← G.map_comp, R.retract, G.map_id P]
  exact comp_id _

omit [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] in
include SA SB in
/-- Actual free generators detect arbitrary native-functor comparison
maps; no essential-surjectivity certificate is used. -/
theorem natTrans_ext_free {α β : F ⟶ G}
    (h : ∀ X : D, α.app (externalObj (InternalModule.free A X) (Mod_.regular (mop B))) =
      β.app (externalObj (InternalModule.free A X) (Mod_.regular (mop B)))) : α = β := by
  apply NatTrans.ext
  funext P
  let R := externalFreeRetract SA SB P
  calc
    α.app P = F.map R.i ≫ α.app _ ≫ G.map R.r := by
      rw [α.naturality_assoc, ← G.map_comp, R.retract, G.map_id, comp_id]
    _ = F.map R.i ≫ β.app _ ≫ G.map R.r := by rw [h P.X.X]
    _ = β.app P := by
      rw [β.naturality_assoc, ← G.map_comp, R.retract, G.map_id, comp_id]

theorem extendBalancedNatTrans_unique (hτ : IsBalancedNatural τ) (α : F ⟶ G)
    (hα : ∀ X : D, α.app (externalObj (InternalModule.free A X) (Mod_.regular (mop B))) =
      τ.app (InternalModule.free A X, Mod_.regular (mop B))) :
    α = extendBalancedNatTrans SA SB τ hτ := by
  apply natTrans_ext_free SA SB
  intro X
  exact (hα X).trans (extendBalancedNatTrans_free SA SB τ hτ X).symm

end Paper18.Category.BalancedModuleCategory

import Paper18.Category.FixedBoundaryTensoratorBasic
import Paper18.Category.FixedBoundaryOrdinaryExtraction

/-! # The mixed defect vanishes by actual module naturality

The input is an actual ordinary comparison with the specified neutral
component, and actual native module naturality on the odd component.
No tensorator-defect equation is supplied.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts C]

section General
variable (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]
  (F : C ⥤ C) [F.Monoidal] [F.IsEquivalence] [F.Additive] [F.Linear ℂ]
  (a : SignKernel.inclusion χ ⋙ F ≅ SignKernel.inclusion χ)
  [NatTrans.IsMonoidal a.hom]
  (hF : ∀ X : C, Homogeneous χ 1 X → Homogeneous χ 1 (F.obj X))
  (e : F ≅ 𝟭 C)

/-- Restrict the actual ordinary comparison to the actual odd component. -/
def comparisonRestriction : homogeneousBoundaryFunctor χ F a 1 hF ≅ 𝟭 (HomogeneousCategory χ 1) :=
  NatIso.ofComponents (fun X => ObjectProperty.isoMk _ (e.app X.obj))
    (fun f => e.hom.naturality (show _ ⟶ _ from f))

@[simp] theorem comparisonRestriction_hom_app (X : HomogeneousCategory χ 1) :
    (comparisonRestriction χ F a hF e).hom.app X = e.hom.app X.obj := rfl

variable (he : ∀ X : SignKernel.Positive χ, e.hom.app X.obj = a.hom.app X)
  [hmodule : ModuleFunctor.IsModuleNatural (SignKernel.Positive χ) (comparisonRestriction χ F a hF e).hom]

include he in
lemma tensoratorDefect_zero_zero {X Y : C}
    (hX : Homogeneous χ 0 X) (hY : Homogeneous χ 0 Y) :
    tensoratorDefect F e X Y = 𝟙 _ := by
  let p : SignKernel.Positive χ := ⟨X, hX⟩
  let q : SignKernel.Positive χ := ⟨Y, hY⟩
  apply tensoratorDefect_eq_id_of_tensor
  change Functor.LaxMonoidal.μ F p.obj q.obj ≫ e.hom.app (p ⊗ q).obj =
    e.hom.app p.obj ⊗ₘ e.hom.app q.obj
  rw [he p, he q, he (p ⊗ q)]
  have hh := NatTrans.IsMonoidal.tensor (τ := a.hom) p q
  change (Functor.LaxMonoidal.μ F p.obj q.obj ≫ F.map (𝟙 _)) ≫ a.hom.app (p ⊗ q) =
    (a.hom.app p ⊗ₘ a.hom.app q) ≫ 𝟙 _ at hh
  simpa only [F.map_id, Category.comp_id] using hh

include he hmodule in
lemma tensoratorDefect_zero_one {X Y : C}
    (hX : Homogeneous χ 0 X) (hY : Homogeneous χ 1 Y) :
    tensoratorDefect F e X Y = 𝟙 _ := by
  let p : SignKernel.Positive χ := ⟨X, hX⟩
  let q : HomogeneousCategory χ 1 := ⟨Y, hY⟩
  have hh := ModuleFunctor.IsModuleNatural.lineator
    (C := SignKernel.Positive χ) (τ := (comparisonRestriction χ F a hF e).hom) p q
  change (a.inv.app p ▷ F.obj Y ≫ Functor.LaxMonoidal.μ F X Y) ≫
      e.hom.app (X ⊗ Y) = X ◁ e.hom.app Y ≫ 𝟙 _ at hh
  apply tensoratorDefect_eq_id_of_tensor
  apply (cancel_epi (a.inv.app p ▷ F.obj Y)).mp
  simp only [Category.assoc, Category.comp_id] at hh ⊢
  rw [hh]
  change X ◁ e.hom.app Y = (a.inv.app p ▷ F.obj Y) ≫
    (e.hom.app p.obj ⊗ₘ e.hom.app Y)
  rw [he p, MonoidalCategory.tensorHom_def, ← Category.assoc, ← comp_whiskerRight,
    Iso.inv_hom_id_app, id_whiskerRight, Category.id_comp]
  rfl

include he hmodule in
lemma tensoratorDefect_zero_left {g : ZMod 2} {X Y : C}
    (hX : Homogeneous χ 0 X) (hY : Homogeneous χ g Y) :
    tensoratorDefect F e X Y = 𝟙 _ := by
  rcases Paper18.ZMod.two_eq_zero_or_one g with rfl | rfl
  · exact tensoratorDefect_zero_zero χ F a e he hX hY
  · exact tensoratorDefect_zero_one χ F a hF e he hX hY



section Glued
variable [HasKernels C]
  (hχ : ∀ X : C, χ.hom.app X ≫ χ.hom.app X = 𝟙 X)
  (b : homogeneousBoundaryFunctor χ F a 1 hF ≅ 𝟭 (HomogeneousCategory χ 1))

/-- The actual glued ordinary comparison retains its given odd isomorphism. -/
theorem comparisonRestriction_ordinaryComparisonFromOdd :
    comparisonRestriction χ F a hF (ordinaryComparisonFromOdd χ hχ F a hF b) = b := by
  ext X
  exact ordinaryComparisonFromOdd_odd χ hχ F a hF b X

instance ordinaryComparisonFromOdd_moduleNatural [ModuleFunctor.IsModuleNatural (SignKernel.Positive χ) b.hom] :
    ModuleFunctor.IsModuleNatural (SignKernel.Positive χ)
      (comparisonRestriction χ F a hF (ordinaryComparisonFromOdd χ hχ F a hF b)).hom := by
  rw [comparisonRestriction_ordinaryComparisonFromOdd]
  infer_instance
end Glued
end General

section Braided
variable [BraidedCategory C]
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]
  (F : C ⥤ C) [F.Braided] [F.IsEquivalence] [F.Additive] [F.Linear ℂ]
  (a : SignKernel.inclusion χ ⋙ F ≅ SignKernel.inclusion χ)
  [NatTrans.IsMonoidal a.hom]
  (hF : ∀ X : C, Homogeneous χ 1 X → Homogeneous χ 1 (F.obj X))
  (e : F ≅ 𝟭 C)
  (he : ∀ X : SignKernel.Positive χ, e.hom.app X.obj = a.hom.app X)
  [hmodule : ModuleFunctor.IsModuleNatural (SignKernel.Positive χ) (comparisonRestriction χ F a hF e).hom]

include he hmodule in
lemma tensoratorDefect_zero_right {g : ZMod 2} {X Y : C}
    (hX : Homogeneous χ g X) (hY : Homogeneous χ 0 Y) :
    tensoratorDefect F e X Y = 𝟙 _ := by
  apply (cancel_epi (β_ Y X).hom).mp
  rw [← tensoratorDefect_braiding F e Y X,
    tensoratorDefect_zero_left χ F a hF e he hY hX]
  simp

end Braided

end Paper18.Category.FixedBoundary

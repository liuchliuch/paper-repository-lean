import Paper18.Category.FixedBoundaryTensoratorCorrection

/-! # H² gauge correction retains actual action comparisons

A complex-linear action preserving the actual character preserves its
actual gauge polynomial.  In particular H² correction does not change
the actual scalar defect of a regular-action comparison.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  (χ : 𝟭 C ≅ 𝟭 C) (T : C ⥤ C) [T.Additive] [T.Linear ℂ]
  (hT : ∀ X : C, T.map (χ.hom.app X) = χ.hom.app (T.obj X))

include hT in
/-- An actual character-preserving complex-linear functor preserves every
gauge component, as an equality of actual morphisms. -/
lemma map_gaugeComponent (z : ℂ) (X : C) :
    T.map (gaugeComponent χ z X) = gaugeComponent χ z (T.obj X) := by
  simp only [gaugeComponent, Functor.map_add, Functor.map_smul, T.map_id, hT]

variable (hχ : ∀ X : C, χ.hom.app X ≫ χ.hom.app X=𝟙 X)

include hT in
@[simp] lemma map_gaugeNatIso_hom (z : ℂˣ) (X : C) :
    T.map ((gaugeNatIso χ hχ z).hom.app X) = (gaugeNatIso χ hχ z).hom.app (T.obj X) :=
  map_gaugeComponent χ T hT (z : ℂ) X

section Correction
variable [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  (F : C ⥤ C) [F.Monoidal] (e : F ≅ 𝟭 C)
  (κ : T ⋙ F ≅ F ⋙ T) (μ : ZMod 2 → ℂˣ)

include hT in
/-- Correction retains the actual scalar action defect, so its vanishing
can be established from the true crossed equation after monoidal correction. -/
lemma correctedIso_action_defect (r : ℂ) (X : C)
    (hκ : κ.hom.app X ≫ T.map (e.hom.app X) = r • e.hom.app (T.obj X)) :
    κ.hom.app X ≫ T.map ((correctedIso F e χ hχ μ).hom.app X) =
      r • (correctedIso F e χ hχ μ).hom.app (T.obj X) := by
  dsimp only [correctedIso, Iso.trans_hom, NatTrans.comp_app]
  rw [Functor.map_comp, ← Category.assoc, hκ, map_gaugeNatIso_hom χ T hT]
  rw [Linear.smul_comp]

include hT in
/-- In particular an actual equivariant ordinary comparison remains
actually equivariant after the H² gauge correction. -/
lemma correctedIso_action_compatible (X : C)
    (hκ : κ.hom.app X ≫ T.map (e.hom.app X) = e.hom.app (T.obj X)) :
    κ.hom.app X ≫ T.map ((correctedIso F e χ hχ μ).hom.app X) =
      (correctedIso F e χ hχ μ).hom.app (T.obj X) := by
  simpa only [one_smul] using correctedIso_action_defect χ T hT hχ F e κ μ 1 X
    (by simpa only [one_smul] using hκ)

end Correction
end Paper18.Category.FixedBoundary

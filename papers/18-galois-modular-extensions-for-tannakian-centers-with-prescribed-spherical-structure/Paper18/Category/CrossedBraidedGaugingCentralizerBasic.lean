import Paper18.Category.CrossedBraidedGaugingTransparentUnderlying

/-! # The actual centralizer of neutral equivariant objects -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.CrossedBraidedGauging
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C] [HasKernels C]
  (P : Grading G C) (A : WeakAction G C)

/-- The actual neutral objects in the equivariant category. -/
def neutralEquivariantObjects : Set A.Equivariant :=
  {E | P.Homogeneous 1 E.obj}

namespace CrossedBraiding
variable {P A}
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  [∀ g : G, (A.ρ g).Additive]
  {Q : GradedAction P A} (B : CrossedBraiding P A Q)

/-- Centralizing the actual neutral equivariant category already kills
every nonneutral degree, by its actual regular representation of the unit. -/
theorem centralizer_homogeneous (E : A.Equivariant) :
    letI := B.equivariantBraidedCategory
    E ∈ centralizer (neutralEquivariantObjects P A) → P.Homogeneous 1 E.obj := by
  letI := B.equivariantBraidedCategory
  intro hE
  apply B.homogeneous_of_regularUnit_monodromy E
  have hc := hE (regularUnit (A := A)) Q.regularUnit_homogeneous
  change (B.equivariantBraiding E (regularUnit (A := A))).hom ≫
    (B.equivariantBraiding (regularUnit (A := A)) E).hom = 𝟙 _ at hc
  simpa only [WeakAction.Equivariant.comp_hom, equivariantBraiding_hom,
    WeakAction.Equivariant.id_hom] using congrArg WeakAction.Equivariant.Hom.hom hc

/-- Genuine induction dominance detects neutral transparency from
centralization only against actual neutral equivariant objects. -/
theorem centralizer_neutral (E : A.Equivariant) :
    letI := B.equivariantBraidedCategory
    ∀ hE : E ∈ centralizer (neutralEquivariantObjects P A),
      letI := B.neutralBraidedCategory
      (⟨E.obj, B.centralizer_homogeneous E hE⟩ : Neutral P) ∈ mugerCenter := by
  letI := B.equivariantBraidedCategory
  intro hE
  let hX := B.centralizer_homogeneous E hE
  letI := B.neutralBraidedCategory
  intro Y _
  change (B.neutralIso E.obj hX Y.obj).hom ≫
    (B.neutralIso Y.obj Y.property E.obj).hom = 𝟙 (E.obj ⊗ Y.obj)
  apply B.neutral_monodromy_of_retract E.obj Y.obj (A.induction Y.obj).obj
    hX Y.property (Q.induction_homogeneous Y.property) (A.inductionRetract Y.obj)
  have hc := hE (A.induction Y.obj) (Q.induction_homogeneous Y.property)
  change (B.equivariantBraiding E (A.induction Y.obj)).hom ≫
    (B.equivariantBraiding (A.induction Y.obj) E).hom = 𝟙 _ at hc
  have hu := congrArg WeakAction.Equivariant.Hom.hom hc
  simp only [WeakAction.Equivariant.comp_hom, equivariantBraiding_hom,
    WeakAction.Equivariant.id_hom] at hu
  rwa [B.halfSwapIso_homogeneous 1 E.obj hX,
    B.halfSwapIso_homogeneous 1 (A.induction Y.obj).obj (Q.induction_homogeneous Y.property),
    ← B.neutralIso_eq_block, ← B.neutralIso_eq_block] at hu

/-- With a genuinely nondegenerate neutral component, this relative
centralizer has actual unit-sum underlying objects. -/
theorem centralizer_underlying_unitSum
    (hN : letI := B.neutralBraidedCategory; IsNondegenerate (C := Neutral P))
    (E : A.Equivariant) :
    letI := B.equivariantBraidedCategory
    E ∈ centralizer (neutralEquivariantObjects P A) → IsUnitSum E.obj := by
  letI := B.equivariantBraidedCategory
  intro hE
  letI := B.neutralBraidedCategory
  exact RelativeTensor.unitSum_map (neutralInclusion P)
    (hN _ (B.centralizer_neutral E hE))

end CrossedBraiding
end Paper18.Category.CrossedBraidedGauging

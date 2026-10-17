import Paper18.Category.CrossedBraidedGaugingTransparentDegree
import Paper18.Category.RelativeTensorCentralImage

/-! # A transparent gauged object is an actual underlying unit sum -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.CrossedBraidedGauging.CrossedBraiding
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C] [HasKernels C]
  {P : Grading G C} {A : WeakAction G C}
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  [∀ g : G, (A.ρ g).Additive]
  {Q : GradedAction P A} (B : CrossedBraiding P A Q)

/-- Actual neutral monodromy descends along actual retracts. -/
theorem neutral_monodromy_of_retract (X Y Z : C)
    (hX : P.Homogeneous 1 X) (hY : P.Homogeneous 1 Y) (hZ : P.Homogeneous 1 Z)
    (r : Retract Y Z)
    (hc : (B.neutralIso X hX Z).hom ≫ (B.neutralIso Z hZ X).hom = 𝟙 (X ⊗ Z)) :
    (B.neutralIso X hX Y).hom ≫ (B.neutralIso Y hY X).hom = 𝟙 (X ⊗ Y) := by
  let sm : SplitMono (X ◁ r.i) :=
    ⟨X ◁ r.r, by rw [← whiskerLeft_comp, r.retract, whiskerLeft_id]⟩
  letI : Mono (X ◁ r.i) := sm.mono
  apply (cancel_mono (X ◁ r.i)).mp
  simp only [Category.assoc, Category.id_comp]
  rw [← B.neutralIso_naturality_left hY hZ r.i X,
    ← Category.assoc, ← B.neutralIso_naturality_right X hX r.i,
    Category.assoc, hc, Category.comp_id]

/-- Transparency in the genuine gauging implies actual transparency of
the underlying object in the actual braided neutral full category. -/
theorem transparent_neutral (E : A.Equivariant) :
    letI := B.equivariantBraidedCategory
    ∀ hE : E ∈ mugerCenter,
      letI := B.neutralBraidedCategory
      (⟨E.obj, B.transparent_homogeneous E hE⟩ : Neutral P) ∈ mugerCenter := by
  letI := B.equivariantBraidedCategory
  intro hE
  let hX := B.transparent_homogeneous E hE
  letI := B.neutralBraidedCategory
  intro Y _
  change (B.neutralIso E.obj hX Y.obj).hom ≫
    (B.neutralIso Y.obj Y.property E.obj).hom = 𝟙 (E.obj ⊗ Y.obj)
  apply B.neutral_monodromy_of_retract E.obj Y.obj (A.induction Y.obj).obj
    hX Y.property (Q.induction_homogeneous Y.property) (A.inductionRetract Y.obj)
  have hc := hE (A.induction Y.obj) (Set.mem_univ _)
  change (B.equivariantBraiding E (A.induction Y.obj)).hom ≫
    (B.equivariantBraiding (A.induction Y.obj) E).hom = 𝟙 _ at hc
  have hu := congrArg WeakAction.Equivariant.Hom.hom hc
  simp only [WeakAction.Equivariant.comp_hom, equivariantBraiding_hom,
    WeakAction.Equivariant.id_hom] at hu
  rwa [B.halfSwapIso_homogeneous 1 E.obj hX,
    B.halfSwapIso_homogeneous 1 (A.induction Y.obj).obj (Q.induction_homogeneous Y.property),
    ← B.neutralIso_eq_block, ← B.neutralIso_eq_block] at hu

/-- Nondegeneracy is assumed only of the actual neutral category and
forces the actual underlying unit-sum decomposition. -/
theorem transparent_underlying_unitSum
    (hN : letI := B.neutralBraidedCategory; IsNondegenerate (C := Neutral P))
    (E : A.Equivariant) :
    letI := B.equivariantBraidedCategory
    E ∈ mugerCenter → IsUnitSum E.obj := by
  letI := B.equivariantBraidedCategory
  intro hE
  letI := B.neutralBraidedCategory
  exact RelativeTensor.unitSum_map (neutralInclusion P)
    (hN _ (B.transparent_neutral E hE))

end Paper18.Category.CrossedBraidedGauging.CrossedBraiding

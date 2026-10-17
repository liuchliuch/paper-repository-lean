import Paper18.Category.CrossedBraidedGaugingCentralizerBasic

/-! # Relative neutral centralizer detection by actual induced test objects -/
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

/-- A source containing the actual regular representation of the unit
detects the neutral support of every object in its actual centralizer. -/
theorem centralizer_homogeneous_of_regularUnit_mem (T : Set A.Equivariant)
    (hregular : regularUnit (A := A) ∈ T) (E : A.Equivariant) :
    letI := B.equivariantBraidedCategory
    E ∈ centralizer T → P.Homogeneous 1 E.obj := by
  letI := B.equivariantBraidedCategory
  intro hE
  apply B.homogeneous_of_regularUnit_monodromy E
  have hc := hE (regularUnit (A := A)) hregular
  change (B.equivariantBraiding E (regularUnit (A := A))).hom ≫
    (B.equivariantBraiding (regularUnit (A := A)) E).hom = 𝟙 _ at hc
  simpa only [WeakAction.Equivariant.comp_hom, equivariantBraiding_hom,
    WeakAction.Equivariant.id_hom] using congrArg WeakAction.Equivariant.Hom.hom hc

/-- Actual induced neutral tests in a source detect the corresponding
actual centralizer inside the neutral category. This permits a proper
neutral tensor factor, as needed in inverse-obstruction constructions. -/
theorem centralizer_neutral_of_induced_tests (T : Set A.Equivariant)
    (hregular : regularUnit (A := A) ∈ T) (U : Set (Neutral P))
    (hinduced : ∀ Y ∈ U, A.induction Y.obj ∈ T) (E : A.Equivariant) :
    letI := B.equivariantBraidedCategory
    ∀ hE : E ∈ centralizer T,
      letI := B.neutralBraidedCategory
      (⟨E.obj, B.centralizer_homogeneous_of_regularUnit_mem T hregular E hE⟩ :
        Neutral P) ∈ centralizer U := by
  letI := B.equivariantBraidedCategory
  intro hE
  let hX := B.centralizer_homogeneous_of_regularUnit_mem T hregular E hE
  letI := B.neutralBraidedCategory
  intro Y hY
  change (B.neutralIso E.obj hX Y.obj).hom ≫
    (B.neutralIso Y.obj Y.property E.obj).hom = 𝟙 (E.obj ⊗ Y.obj)
  apply B.neutral_monodromy_of_retract E.obj Y.obj (A.induction Y.obj).obj
    hX Y.property (Q.induction_homogeneous Y.property) (A.inductionRetract Y.obj)
  have hc := hE (A.induction Y.obj) (hinduced Y hY)
  change (B.equivariantBraiding E (A.induction Y.obj)).hom ≫
    (B.equivariantBraiding (A.induction Y.obj) E).hom = 𝟙 _ at hc
  have hu := congrArg WeakAction.Equivariant.Hom.hom hc
  simp only [WeakAction.Equivariant.comp_hom, equivariantBraiding_hom,
    WeakAction.Equivariant.id_hom] at hu
  rwa [B.halfSwapIso_homogeneous 1 E.obj hX,
    B.halfSwapIso_homogeneous 1 (A.induction Y.obj).obj (Q.induction_homogeneous Y.property),
    ← B.neutralIso_eq_block, ← B.neutralIso_eq_block] at hu

end Paper18.Category.CrossedBraidedGauging.CrossedBraiding

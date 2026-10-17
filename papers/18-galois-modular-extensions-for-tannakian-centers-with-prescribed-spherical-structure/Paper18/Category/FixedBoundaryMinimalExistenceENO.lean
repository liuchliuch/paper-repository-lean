import Paper18.External.ENOExtensionTheory

/-! # Original A.1 and prescribed spherical output relative to ENO

Only the precise external obstruction-realization theorem is an input.
The C₂ primitive, original-source reconstruction, gauging, exact minimal
dimension, every specified-boundary trivialization, and spherical enhancement
are the project's actual proofs.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open Paper18.External.ENOExtensionTheory
open Paper18.Category.CrossedBraidedGauging
universe v u w v' u' w'
namespace Paper18.Category.FixedBoundary.MinimalExistence
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (T : TannakianCenter C C2)

/-- ENO's external existence input applied to the actual specified
Tannakian de-equivariant action. Coequalizers, fusion structures, and neutral
nondegeneracy are supplied by the actual source construction. -/
def TannakianObstructionInput : Prop := by
  letI := S.hasCoequalizers
  letI := T.deequivariantRightRigid
  letI := T.deequivariantSimpleUnit S
  letI := T.deequivariantBraided
  letI := T.deequivariantActionBraided
  exact ObstructionRealization.{_,_,_,v',u',w'} T.deequivariantAction
    (T.deequivariantSkeleton S) (T.deequivariant_isNondegenerate S)

/-- The existence half of the original categorical Lemma A.1, relative
only to the explicitly registered external ENO realization input. -/
theorem minimalExtension_exists
    (hENO : TannakianObstructionInput.{v,u,w,v',u',w'} S T) :
    Nonempty (MinimalBraidedExtension.{v,u,w,v',max u' v',w'} S) := by
  letI := S.hasCoequalizers
  letI := T.deequivariantRightRigid
  letI := T.deequivariantSimpleUnit S
  letI := T.deequivariantBraided
  letI := T.deequivariantActionBraided
  obtain ⟨R⟩ := faithfulCrossedRealization_exists T.deequivariantAction
    (T.deequivariantSkeleton S) (T.deequivariant_isNondegenerate S) hENO
  exact ⟨tannakianMinimalExtensionOfCrossedData S T R.skeleton R.crossing R.neutral
    R.homogeneous R.covers R.faithful R.braided⟩

/-- The complete exact Lemma A.1 contract follows from the registered
external existence input and the internally proved universal specified-
boundary classification. No classification premise is supplied externally. -/
theorem lemmaA1_relative_to_ENO
    (hENO : ∀ T : TannakianCenter C C2,
      TannakianObstructionInput.{v,u,w,v',u',w'} S T) :
    LemmaA1Statement.{v,u,w,v',max u' v',w'} S := by
  rintro ⟨T⟩
  exact ⟨minimalExtension_exists S T (hENO T),
    fun E P => FixedBoundary.minimalBoundary_trivializable S T E P⟩

/-- A single fixed actual Tannakian identification and its ENO input
already prove the exact original A.1 proposition. -/
theorem lemmaA1_relative_to_ENO_at_center
    (hENO : TannakianObstructionInput.{v,u,w,v',u',w'} S T) :
    LemmaA1Statement.{v,u,w,v',max u' v',w'} S := by
  intro _
  exact ⟨minimalExtension_exists S T hENO,
    fun E P => FixedBoundary.minimalBoundary_trivializable S T E P⟩

/-- Every prescribed spherical structure with negative C₂ generator
admits an actual minimal modular extension, relative only to external ENO
realization. The spherical structure is constructed by the own-paper proof. -/
theorem modularExtension_exists
    (hENO : TannakianObstructionInput.{v,u,w,v',u',w'} S T)
    (J : PivotalStructure C) (hJ : J.Spherical) (hd : J.rightDim T.c2Generator = -1) :
    Nonempty (ModularExtension.{v,u,v',max u' v',w'} J) := by
  letI := S.hasCoequalizers
  letI := T.deequivariantRightRigid
  letI := T.deequivariantSimpleUnit S
  letI := T.deequivariantBraided
  letI := T.deequivariantActionBraided
  obtain ⟨R⟩ := faithfulCrossedRealization_exists T.deequivariantAction
    (T.deequivariantSkeleton S) (T.deequivariant_isNondegenerate S) hENO
  exact ⟨tannakianModularExtensionOfCrossedData S T R.skeleton R.crossing R.neutral
    R.homogeneous R.covers R.faithful R.braided J hJ hd⟩

/-- The exact two assertions of Proposition 2.2: an actual minimal
extension with the prescribed spherical structure exists, and every actual
minimal nondegenerate extension supports such a structure. Only the first
assertion uses the explicitly registered ENO existence input. -/
theorem proposition2_2_relative_to_ENO
    (hENO : TannakianObstructionInput.{v,u,w,v',u',w'} S T)
    (J : PivotalStructure C) (hJ : J.Spherical) (hd : J.rightDim T.c2Generator = -1) :
    (∃ E : MinimalBraidedExtension.{v,u,w,v',max u' v',w'} S,
      ∃ K : PivotalStructure E.ambient,
        K.Spherical ∧ PreservesPivotal E.inclusion J K) ∧
      ∀ E : MinimalBraidedExtension.{v,u,w,v',max u' v',w'} S,
        ∃ K : PivotalStructure E.ambient,
          K.Spherical ∧ PreservesPivotal E.inclusion J K := by
  constructor
  · obtain ⟨E⟩ := minimalExtension_exists S T hENO
    exact ⟨E, spherical_extension_of_c2_minimal S T J hJ hd E⟩
  · intro E
    exact spherical_extension_of_c2_minimal S T J hJ hd E

end Paper18.Category.FixedBoundary.MinimalExistence

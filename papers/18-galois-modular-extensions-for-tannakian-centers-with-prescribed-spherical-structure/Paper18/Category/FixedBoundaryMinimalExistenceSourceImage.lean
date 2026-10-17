import Paper18.Category.FixedBoundaryMinimalExistenceAssembly
import Paper18.Category.FactorizationEssentialSurjectiveBasic
import Paper18.Category.CentralizerDimensionBasic

/-! # The actual source image is exactly the neutral equivariant sector

The essential image is derived from actual full tensor functors and the
actual index-two dimension formula. It is not a realization premise.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Functor.LaxMonoidal
open Paper18.Category.CrossedBraidedGauging
universe v₀ u₀ w₀ v₁ u₁ w₁ v₂ u₂ w₂
namespace Paper18.Category.FixedBoundary.MinimalExistence
variable {C : Type u₀} [Category.{v₀} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w₀} [Fintype ι] (SC : FiniteSemisimpleSkeleton C ι)
  {D : Type u₁} [Category.{v₁} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)]
  {κ : Type w₁} [Fintype κ] (SD : FiniteSemisimpleSkeleton D κ)
  {A : WeakAction C2 C} {H : WeakAction C2 D}
  [∀ g : C2, (A.ρ g).Monoidal] [A.IsMonoidal] [A.IsBraided]
  [∀ g : C2, (H.ρ g).Monoidal] [H.IsMonoidal]
  [∀ g : C2, (A.ρ g).Additive] [∀ g : C2, (A.ρ g).Linear ℂ]
  [∀ g : C2, (H.ρ g).Additive] [∀ g : C2, (H.ρ g).Linear ℂ]
  {P : Grading C2 D} {Q : GradedAction P H} (B : CrossedBraiding P H Q)
  (F : A.Intertwiner H) [F.functor.Monoidal] [F.IsMonoidal]
  [F.functor.Additive] [F.functor.Linear ℂ] [F.functor.Full] [F.functor.Faithful]
  (hdeg : ∀ X : C, P.Homogeneous 1 (F.functor.obj X))
  (hcover : ∀ Y : D, P.Homogeneous 1 Y → ∃ X : C, Nonempty (F.functor.obj X ≅ Y))

variable {R : Type u₂} [Category.{v₂} R] [Preadditive R] [Linear ℂ R]
  [HasKernels R] [HasFiniteBiproducts R]
  [∀ X Y : R, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory R] [BraidedCategory R] [MonoidalPreadditive R] [MonoidalLinear ℂ R]
  [RightRigidCategory R] [Simple (𝟙_ R)]
  {ν : Type w₂} [Fintype ν] (SR : FiniteSemisimpleSkeleton R ν)
  (E : R ⥤ A.Equivariant) [E.IsEquivalence] [E.Additive] [E.Linear ℂ] [E.Braided]

include hdeg in
/-- The genuine source embedding is supported in the actual neutral degree. -/
theorem sourceEmbedding_homogeneous (X : R) :
    (equivariantGrading Q).Homogeneous 1 ((sourceEmbedding F E).obj X) :=
  (equivariantGrading_homogeneous Q 1 _).mpr (hdeg (E.obj X).obj)

include SC SD SR hdeg hcover E Q in
/-- Equal actual dimensions make the neutral lift of the genuine source
embedding essentially surjective. This uses actual simple decompositions,
not an equivariant essential-image premise. -/
def sourceNeutralLiftEssSurj (hf : P.Faithful) :
    (neutralLift (sourceEmbedding F E) (sourceEmbedding_homogeneous (Q := Q) F hdeg E)).EssSurj := by
  let T := H.equivariantSkeleton SD
  let PN := neutralProperty (equivariantGrading Q)
  letI : ∀ X Y : PN.FullSubcategory, FiniteDimensional ℂ (X ⟶ Y) :=
    fun X Y => inferInstanceAs (FiniteDimensional ℂ (X.obj ⟶ Y.obj))
  letI := T.fullSubcategoryHasKernels PN
  letI := T.fullSubcategoryRightRigid PN
  letI := T.fullSubcategorySimpleUnit PN
  let SN := T.fullSubcategorySkeleton PN
  let K := neutralLift (sourceEmbedding F E) (sourceEmbedding_homogeneous (Q := Q) F hdeg E)
  have ht : SN.fusionBasis.totalFPdim = SD.fusionBasis.totalFPdim := by
    rw [T.fullSubcategory_totalFPdim_eq PN]
    exact gauging_neutral_support_eq_total SD Q hf
  exact SR.essSurjOfTotalFPdimEq SN K
    ((source_total_eq_graded SC SD F hdeg hcover SR E hf).trans ht.symm)

include SC SD SR hdeg hcover E Q in
/-- Every genuine neutral equivariant object comes from the original source. -/
theorem sourceEmbedding_covers_neutral (hf : P.Faithful)
    (Y : H.Equivariant) (hY : P.Homogeneous 1 Y.obj) :
    ∃ X : R, Nonempty ((sourceEmbedding F E).obj X ≅ Y) := by
  let PN := neutralProperty (equivariantGrading Q)
  let K := neutralLift (sourceEmbedding F E) (sourceEmbedding_homogeneous (Q := Q) F hdeg E)
  letI : K.EssSurj := sourceNeutralLiftEssSurj (Q := Q) SC SD F hdeg hcover SR E hf
  let YN : PN.FullSubcategory := ⟨Y, (equivariantGrading_homogeneous Q 1 Y).mpr hY⟩
  refine ⟨K.objPreimage YN, ⟨?_⟩⟩
  exact PN.ι.mapIso (K.objObjPreimageIso YN)

include SC SD SR hdeg hcover E Q in
/-- The essential image of the actual original-source embedding is exactly
the actual neutral equivariant objects. -/
theorem sourceEmbedding_essImage (hf : P.Faithful) :
    (sourceEmbedding F E).essImage = neutralProperty (equivariantGrading Q) := by
  ext Y
  constructor
  · intro hY
    exact (equivariantGrading Q).homogeneous_iso hY.getIso.symm
      (sourceEmbedding_homogeneous (Q := Q) F hdeg E hY.witness)
  · intro hY
    exact sourceEmbedding_covers_neutral (Q := Q) SC SD F hdeg hcover SR E hf Y
      ((equivariantGrading_homogeneous Q 1 Y).mp hY)

end Paper18.Category.FixedBoundary.MinimalExistence

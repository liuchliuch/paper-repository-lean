import Paper18.Category.CrossedBraidedGaugingCentralizerRelative
import Paper18.Category.CrossedBraidedGaugingCentralizerIntegral

/-! # Integral relative centralizers pass to actual crossed gauging -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w t
namespace Paper18.Category.CrossedBraidedGauging.CrossedBraiding
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {P : Grading G C} {A : WeakAction G C}
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  [∀ g : G, (A.ρ g).Additive] [∀ g : G, (A.ρ g).Linear ℂ]
  {Q : GradedAction P A} (B : CrossedBraiding P A Q)
  {ι : Type t} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- An integral actual relative centralizer in the neutral category gives
integral dimensions in the gauging. The induced-test and regular-unit
conditions concern actual objects of the embedded source. -/
theorem centralizerIntegral_of_induced_tests (T : Set A.Equivariant)
    (hregular : regularUnit (A := A) ∈ T) (U : Set (Neutral P))
    (hinduced : ∀ Y ∈ U, A.induction Y.obj ∈ T)
    (hIntegral :
      letI := B.neutralBraidedCategory
      letI := S.fullSubcategoryHasKernels (neutralProperty P)
      letI := S.fullSubcategoryRightRigid (neutralProperty P)
      letI := S.fullSubcategorySimpleUnit (neutralProperty P)
      (S.fullSubcategorySkeleton (neutralProperty P)).CentralizerIntegral U) :
    letI := B.equivariantBraidedCategory
    (gaugingSkeleton S).CentralizerIntegral T := by
  letI := B.equivariantBraidedCategory
  letI := B.neutralBraidedCategory
  letI := S.fullSubcategoryHasKernels (neutralProperty P)
  letI := S.fullSubcategoryRightRigid (neutralProperty P)
  letI := S.fullSubcategorySimpleUnit (neutralProperty P)
  let SN := S.fullSubcategorySkeleton (neutralProperty P)
  apply (gaugingSkeleton S).centralizerIntegral_iff T |>.mpr
  intro i hi
  let E := (gaugingSkeleton S).simpleObject i
  let hX := B.centralizer_homogeneous_of_regularUnit_mem T hregular E hi
  let Y : Neutral P := ⟨E.obj, hX⟩
  have hY : Y ∈ centralizer U :=
    B.centralizer_neutral_of_induced_tests T hregular U hinduced E hi
  have hn : ∃ n : ℤ, SN.fpdim Y = n := by
    let CP := centralizerProperty U
    letI := SN.fullSubcategoryHasKernels CP
    letI := SN.fullSubcategoryRightRigid CP
    letI := SN.fullSubcategorySimpleUnit CP
    let ST := SN.fullSubcategorySkeleton CP
    have hST : ST.Integral := hIntegral
    obtain ⟨n, hn⟩ := ST.fpdim_integer hST (⟨Y, hY⟩ : CP.FullSubcategory)
    refine ⟨n, ?_⟩
    exact (SN.fullSubcategoryFPdim_eq CP (⟨Y, hY⟩ : CP.FullSubcategory)).symm.trans hn
  obtain ⟨n, hn⟩ := hn
  refine ⟨n, ?_⟩
  calc
    (gaugingSkeleton S).fpdim E = S.fpdim E.obj :=
      ((gaugingSkeleton S).fpdim_map S A.forget E).symm
    _ = SN.fpdim Y := SN.fpdim_map S (neutralInclusion P) Y
    _ = n := hn

end Paper18.Category.CrossedBraidedGauging.CrossedBraiding

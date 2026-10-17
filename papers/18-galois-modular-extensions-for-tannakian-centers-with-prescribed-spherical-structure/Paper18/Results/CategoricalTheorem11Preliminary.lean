import Paper18.Results.CategoricalTheorem11Cases
import Paper18.Results.CategoricalPreliminaryCentralizer
import Paper18.Results.CategoricalPreliminaryCentralizerDimension
import Paper18.Category.SphericalizationC2Negative
import Paper18.Category.FixedBoundaryMinimalSpherical

/-! # The actual preliminary construction in Theorem 1.1

Starting with the actual nonspherical Johnson--Freyd extension, a genuine
minimal extension of its sphericalization is enhanced by the own-paper
Proposition 2.2. Its actual negative object and integral even centralizer
then feed the two proved sign-character branches. No spherical extension
or preliminary case package is an external input.
-/
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe vB uB wB v0 u0 w0 vN uN wN
namespace Paper18.Category.CategoricalTheorem11
attribute [local instance 2000] RightRigidCategory.rightDual
variable {B : Type uB} [Category.{vB} B] [Preadditive B] [Linear ℂ B]
  [MonoidalCategory B] [BraidedCategory B] [MonoidalPreadditive B] [MonoidalLinear ℂ B]
  [HasKernels B] [HasFiniteBiproducts B] [RightRigidCategory B] [Simple (𝟙_ B)]
  [∀ X Y : B, FiniteDimensional ℂ (X ⟶ Y)]
  {ιB : Type wB} [Fintype ιB] (SB : FiniteSemisimpleSkeleton B ιB)
  (JB : PivotalStructure B) (hJB : JB.Spherical)
  {Γ : Type} [Group Γ] (TB : TannakianCenter B Γ)
  (E0 : GaloisBraidedExtension.{vB,uB,v0,u0,w0} B)
  (E : MinimalBraidedExtension.{v0,max u0 v0,w0,vN,uN,wN}
    (Sphericalized.skeleton E0.skeleton))

/-- The actual prescribed spherical enhancement is constructed by
Proposition 2.2 applied to the negative canonical sphericalization generator. -/
def minimalSphericalPivotal : PivotalStructure E.ambient :=
  Classical.choose (spherical_extension_of_c2_minimal (Sphericalized.skeleton E0.skeleton)
    (Sphericalized.tannakianCenter E0.nondegenerate) Sphericalized.pivotalStructure
    Sphericalized.pivotalStructure_spherical
    (Sphericalized.tannakianCenter_c2Generator_rightDim E0.skeleton E0.nondegenerate) E)

omit [MonoidalPreadditive B] [MonoidalLinear ℂ B] [HasKernels B]
  [HasFiniteBiproducts B] [RightRigidCategory B] [Simple (𝟙_ B)]
  [∀ X Y : B, FiniteDimensional ℂ (X ⟶ Y)] in
/-- The constructed enhancement is actually spherical and has the
canonical actual pivotal comparison on the given minimal inclusion. -/
theorem minimalSphericalPivotal_spec :
    (minimalSphericalPivotal E0 E).Spherical ∧
      PreservesPivotal E.inclusion Sphericalized.pivotalStructure (minimalSphericalPivotal E0 E) :=
  Classical.choose_spec (spherical_extension_of_c2_minimal (Sphericalized.skeleton E0.skeleton)
    (Sphericalized.tannakianCenter E0.nondegenerate) Sphericalized.pivotalStructure
    Sphericalized.pivotalStructure_spherical
    (Sphericalized.tannakianCenter_c2Generator_rightDim E0.skeleton E0.nondegenerate) E)

/-- The original source's specified spherical structure is retained by
the actual composite through sphericalization and the actual minimal extension. -/
def preliminaryEmbedding : BraidedSphericalEmbedding JB (minimalSphericalPivotal E0 E) where
  functor := Sphericalized.embedding SB JB hJB E0.inclusion ⋙ E.inclusion
  pivotal := (Sphericalized.embedding_preservesPivotal SB JB hJB E0.inclusion).comp
    (minimalSphericalPivotal_spec E0 E).2

/-- Formula (3.3) is an actual consequence of the genuine minimal
extension and the own-paper spherical enhancement. -/
theorem preliminaryCentralizerFPdim :
    E.skeleton.centralizerFPdim
      (PreliminaryCentralizer.preliminaryAmbientObjects SB JB hJB E0.inclusion E.inclusion) =
      4 * E0.skeleton.centralizerFPdim (Set.range E0.inclusion.obj) :=
  PreliminaryCentralizer.negativeCentralizerFPdim_eq_four E0.skeleton SB JB hJB E0.inclusion
    E.skeleton E.inclusion (minimalSphericalPivotal E0 E) E.nondegenerate E.minimal

/-- The actual preliminary construction supplies every input needed by
both own-paper branches. Only the sign-kernel use of JF Proposition 2.3
and the actual initial minimal extension remain explicit inputs here. -/
def fromInitialMinimal
    (EBound : MinimalBraidedExtension.{v0,max u0 v0,w0,vN,max 1 (max uN vN),wN}
      (Sphericalized.skeleton E0.skeleton))
    (jf : Paper18.External.JohnsonFreyd23At.{vN,max 1 (max uN vN),wN,vN,max 1 (max uN vN),wN}) :
    Nonempty (ModularExtension.{vB,uB,vN,max 1 (max uN vN),wN} JB) := by
  let JN := minimalSphericalPivotal E0 EBound
  have hJN := (minimalSphericalPivotal_spec E0 EBound).1
  have hp := (minimalSphericalPivotal_spec E0 EBound).2
  let H := preliminaryEmbedding SB JB hJB E0 EBound
  have hpre := PreliminaryCentralizer.sphericalized_preliminary E0.skeleton SB JB hJB
    E0.inclusion EBound.skeleton EBound.inclusion JN hJN hp EBound.nondegenerate EBound.minimal
    E0.integralCentralizer
  have hcases := fromAmbientCasesAt SB JB TB EBound.skeleton JN H jf ⟨hJN, EBound.nondegenerate⟩
  have hset : PreliminaryCentralizer.preliminaryAmbientObjects SB JB hJB E0.inclusion EBound.inclusion =
      Set.range H.functor.obj :=
    PreliminaryCentralizer.preliminaryAmbientObjects_eq_range SB JB hJB E0.inclusion EBound.inclusion
  rw [← hset] at hcases
  letI := EBound.skeleton.fullSubcategoryHasKernels
    (centralizerProperty (PreliminaryCentralizer.preliminaryAmbientObjects SB JB hJB E0.inclusion EBound.inclusion))
  letI := EBound.skeleton.fullSubcategoryRightRigid
    (centralizerProperty (PreliminaryCentralizer.preliminaryAmbientObjects SB JB hJB E0.inclusion EBound.inclusion))
  letI := EBound.skeleton.fullSubcategorySimpleUnit
    (centralizerProperty (PreliminaryCentralizer.preliminaryAmbientObjects SB JB hJB E0.inclusion EBound.inclusion))
  have hout := hcases (PreliminaryCentralizer.negativeCentralObject SB JB hJB E0.inclusion EBound.inclusion)
    (PreliminaryCentralizer.negativeCentralTensorInverse SB JB hJB E0.inclusion EBound.inclusion)
    (PreliminaryCentralizer.negativeCentralSquareIso SB JB hJB E0.inclusion EBound.inclusion)
    hpre.2.2.1 hpre.2.1
  exact hout.elim id id

end Paper18.Category.CategoricalTheorem11

import Paper18.Results.CategoricalPreliminaryCentralizerBasic
import Paper18.Category.SphericalizationCentralizerIntegral
import Paper18.Category.SphericalizationNegative

/-! # Preliminary weak integrality after actual sphericalization

The original ambient category has no chosen pivotal structure. Its actual
sphericalization supplies the negative transparent object and the lift of
the prescribed spherical embedding. All centralizer conclusions below are
derived from the actual minimal extension of that sphericalization.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u' w' v'' u'' w''
namespace Paper18.Category.PreliminaryCentralizer
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {B : Type u'} [Category.{v'} B] [MonoidalCategory B] [BraidedCategory B]
  [RightRigidCategory B] [Preadditive B] [Linear ℂ B]
  [MonoidalPreadditive B] [MonoidalLinear ℂ B] [HasKernels B] [HasFiniteBiproducts B]
  [∀ X Y : B, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ B)]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton B κ)
  (JB : PivotalStructure B) (hJB : JB.Spherical)
  (F : B ⥤ C) [F.Braided] [F.Additive] [F.Linear ℂ] [F.Full] [F.Faithful]
  {N : Type u''} [Category.{v''} N] [MonoidalCategory N] [BraidedCategory N]
  [RightRigidCategory N] [Preadditive N] [Linear ℂ N]
  [MonoidalPreadditive N] [MonoidalLinear ℂ N] [HasKernels N] [HasFiniteBiproducts N]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ N)]
  {ν : Type w''} [Fintype ν] (U : FiniteSemisimpleSkeleton N ν)
  (H : Sphericalized C ⥤ N) [H.Braided] [H.Additive] [H.Linear ℂ] [H.Full] [H.Faithful]

/-- The actual prescribed spherical lift, as a set of objects. -/
abbrev prescribedSourceObjects : Set (Sphericalized C) :=
  Set.range (Sphericalized.embedding T JB hJB F).obj

/-- The actual object set whose centralizer is the preliminary category. -/
abbrev preliminaryAmbientObjects : Set N :=
  H.obj '' prescribedSourceObjects T JB hJB F

/-- This is the object range of the actual composite embedding. -/
lemma preliminaryAmbientObjects_eq_range : preliminaryAmbientObjects T JB hJB F H =
    Set.range (Sphericalized.embedding T JB hJB F ⋙ H).obj := by
  ext Y
  constructor
  · rintro ⟨X, ⟨Z, rfl⟩, rfl⟩
    exact ⟨Z, rfl⟩
  · rintro ⟨Z, rfl⟩
    exact ⟨_, ⟨Z, rfl⟩, rfl⟩

/-- Actual transparency of the canonical negative sphericalization object. -/
lemma negativeGenerator_mem_mugerCenter :
    Sphericalized.negativeGenerator (C := C) ∈ mugerCenter (C := Sphericalized C) :=
  fun Y _ => Sphericalized.negativeGenerator_centralizes Y

/-- The actual negative object in the preliminary ambient centralizer. -/
def negativeCentralObject : CentralizerCategory (preliminaryAmbientObjects T JB hJB F H) :=
  minimalCentralObject H (prescribedSourceObjects T JB hJB F)
    (negativeGenerator_mem_mugerCenter (C := C))

@[simp] lemma negativeCentralObject_obj :
    (negativeCentralObject T JB hJB F H).obj =
      H.obj (Sphericalized.negativeGenerator (C := C)) := rfl

/-- Its tensor square is constructed by transporting the actual negative square. -/
def negativeCentralSquareIso :
    negativeCentralObject T JB hJB F H ⊗ negativeCentralObject T JB hJB F H ≅
      𝟙_ (CentralizerCategory (preliminaryAmbientObjects T JB hJB F H)) :=
  minimalCentralSquareIso H (prescribedSourceObjects T JB hJB F)
    (negativeGenerator_mem_mugerCenter (C := C)) Sphericalized.negativeGeneratorSquareIso

/-- Actual two-sided tensor inverse in the preliminary category. -/
def negativeCentralTensorInverse : TensorInverse (negativeCentralObject T JB hJB F H) :=
  minimalCentralTensorInverse H (prescribedSourceObjects T JB hJB F)
    (negativeGenerator_mem_mugerCenter (C := C)) Sphericalized.negativeGeneratorSquareIso

/-- The actual negative object remains bosonic in the preliminary category. -/
lemma negativeCentralObject_selfBraiding :
    (β_ (negativeCentralObject T JB hJB F H) (negativeCentralObject T JB hJB F H)).hom =
      𝟙 (negativeCentralObject T JB hJB F H ⊗ negativeCentralObject T JB hJB F H) :=
  minimalCentralObject_selfBraiding H (prescribedSourceObjects T JB hJB F)
    (negativeGenerator_mem_mugerCenter (C := C)) Sphericalized.negativeGenerator_selfBraiding

include S in
/-- The actual negative object is distinct from the preliminary tensor unit. -/
lemma negativeCentralObject_not_iso_unit :
    ¬ Nonempty (negativeCentralObject T JB hJB F H ≅
      𝟙_ (CentralizerCategory (preliminaryAmbientObjects T JB hJB F H))) :=
  minimalCentralObject_not_iso_unit H (prescribedSourceObjects T JB hJB F)
    (negativeGenerator_mem_mugerCenter (C := C))
    (Sphericalized.negativeGenerator_not_iso_unit S)

/-- The actual even centralizer is integral. The original ambient category
requires no pivotal structure. -/
theorem negativeCentralizer_evenIntegral (JN : PivotalStructure N)
    (hN : IsNondegenerate (C := N))
    (hminimal : U.fusionBasis.totalFPdim =
      2 * (Sphericalized.skeleton S).fusionBasis.totalFPdim)
    (hI : S.CentralizerIntegral (Set.range F.obj)) :
    letI := U.fullSubcategoryHasKernels
      (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
    letI := U.fullSubcategoryRightRigid
      (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
    letI := U.fullSubcategorySimpleUnit
      (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
    (U.centralizerSkeleton (preliminaryAmbientObjects T JB hJB F H)).CentralizerIntegral
      {negativeCentralObject T JB hJB F H} :=
  minimalCentralizer_evenIntegral H (prescribedSourceObjects T JB hJB F)
    (negativeGenerator_mem_mugerCenter (C := C)) (Sphericalized.skeleton S) U
    JN hN hminimal Sphericalized.negativeGeneratorTensorInverse
    (Sphericalized.negativeGenerator_not_iso_unit S)
    (Sphericalized.embedding_centralizerIntegral S T JB hJB F hI)

/-- The actual preliminary centralizer is weakly integral, before any
positive pivotal structure is chosen on it. -/
theorem negativeCentralizer_weaklyIntegral (JN : PivotalStructure N)
    (hN : IsNondegenerate (C := N))
    (hminimal : U.fusionBasis.totalFPdim =
      2 * (Sphericalized.skeleton S).fusionBasis.totalFPdim)
    (hI : S.CentralizerIntegral (Set.range F.obj)) :
    letI := U.fullSubcategoryHasKernels
      (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
    letI := U.fullSubcategoryRightRigid
      (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
    letI := U.fullSubcategorySimpleUnit
      (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
    (U.centralizerSkeleton (preliminaryAmbientObjects T JB hJB F H)).fusionBasis.WeaklyIntegral :=
  minimalCentralizer_weaklyIntegral H (prescribedSourceObjects T JB hJB F)
    (negativeGenerator_mem_mugerCenter (C := C)) (Sphericalized.skeleton S) U
    JN hN hminimal Sphericalized.negativeGeneratorTensorInverse
    Sphericalized.negativeGeneratorSquareIso (Sphericalized.negativeGenerator_not_iso_unit S)
    (Sphericalized.embedding_centralizerIntegral S T JB hJB F hI)

include S in
/-- The actual prescribed pivotal extension makes epsilon's inherited
pivotal dimension exactly minus one. -/
lemma negativeCentralObject_rightDim (JN : PivotalStructure N)
    (hp : PreservesPivotal H (Sphericalized.pivotalStructure (C := C)) JN) :
    letI := U.fullSubcategoryHasKernels
      (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
    letI := U.fullSubcategoryRightRigid
      (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
    letI := U.fullSubcategorySimpleUnit
      (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
    (U.centralizerPivotal (preliminaryAmbientObjects T JB hJB F H) JN).rightDim
      (negativeCentralObject T JB hJB F H) = -1 := by
  exact (minimalCentralObject_rightDim H (prescribedSourceObjects T JB hJB F)
    (negativeGenerator_mem_mugerCenter (C := C)) U
    Sphericalized.pivotalStructure JN hp).trans (Sphericalized.negativeGenerator_rightDim S)

end Paper18.Category.PreliminaryCentralizer

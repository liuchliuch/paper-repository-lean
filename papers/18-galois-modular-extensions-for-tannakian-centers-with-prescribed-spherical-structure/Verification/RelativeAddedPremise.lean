import Paper18.AllSources
import Paper18.Results.CategoricalTheorem11
import Paper18.Results.CategoricalLacabanne
import Paper18.Category.PointedTannakian
import Paper18.Category.EquivariantIntegrality
import Paper18.Category.Integrality
import Paper18.Category.PositiveGaloisExtensionRefinement
import Paper18.Category.TannakianBasic
import Paper18.Results.CategoricalJohnsonFreydPositive
import Paper18.Category.FixedBoundaryMinimalExistenceENO

/-! Solutions relative to explicit published external inputs.
This file never imports a challenge. -/

noncomputable section
open Classical CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Paper18.Category
open Paper18.Category.FixedBoundary.MinimalExistence
namespace P18Relative
universe v u w
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [BraidedCategory C]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

include S in
/-- Original A.1 relative only to the registered ENO obstruction-realization
input. The universal specified-boundary conclusion is not an external input. -/
theorem lemmaA_1 (T : TannakianCenter C (Multiplicative (ZMod 2)))
    (hENO : TannakianObstructionInput.{v,u,w,max u v,max u (v+1),max (max u v) w} S T) :
    Nonempty (MinimalBraidedExtension.{v,u,w,max u v,max u (v+1),max (max u v) w} S) ∧
      ∀ E : MinimalBraidedExtension.{v,u,w,max u v,max u (v+1),max (max u v) w} S,
        ∀ P : BoundaryAutoequivalence E.inclusion,
          Nonempty (BoundaryIso E.inclusion P (BoundaryAutoequivalence.identity E.inclusion)) :=
by
  exact ⟨minimalExtension_exists S T hENO,
    fun E P => FixedBoundary.minimalBoundary_trivializable S T E P⟩

include S in
/-- Original Proposition 2.2 relative to the same published existence input.
The negative-generator spherical extension is proved internally for every E. -/
theorem proposition2_2 (J : PivotalStructure C) (hJ : J.Spherical)
    (T : TannakianCenter C (Multiplicative (ZMod 2)))
    (hd : J.rightDim T.c2Generator = -1)
    (hENO : TannakianObstructionInput.{v,u,w,max u v,max u (v+1),max (max u v) w} S T) :
    Nonempty (MinimalBraidedExtension.{v,u,w,max u v,max u (v+1),max (max u v) w} S) ∧
      ∀ E : MinimalBraidedExtension.{v,u,w,max u v,max u (v+1),max (max u v) w} S,
        ∃ K : PivotalStructure E.ambient, K.Spherical ∧ PreservesPivotal E.inclusion J K :=
by
  exact ⟨minimalExtension_exists S T hENO,
    fun E => spherical_extension_of_c2_minimal S T J hJ hd E⟩


include S in
/-- The positive refinement is derived from the nonspherical JF input and
internally proved positivity of the actual ambient category. -/
theorem positive_extension {G : Type} [Group G]
    (extra_premise : True)
    (hJF : Paper18.External.JohnsonFreyd23.{v,u,w})
    (J : PivotalStructure C) (hJ : J.Positive) (T : TannakianCenter C G) :
    Nonempty (PositiveGaloisExtension.{v,u,max u v,max u (v+1),max (max u v) w} J) :=
by
  exact positive_extension_of_johnsonFreyd23 S hJF J hJ T


include S in
/-- The original actual-category main theorem relative only to the two
registered published external existence results. Its output bounds and
prescribed spherical conclusion are unchanged. -/
theorem theorem1_1 {G : Type} [Group G]
    (J : PivotalStructure C) (hJ : J.Spherical) (T : TannakianCenter C G)
    (jf : Paper18.External.JohnsonFreyd23.{v,u,w})
    (jfKernel : Paper18.External.JohnsonFreyd23At.{
      max u v,max u (v+1),max (max u v) w,
      max u v,max u (v+1),max (max u v) w})
    (hENO : CategoricalTheorem11.InitialObstructionInput S T jf) :
    Nonempty (ModularExtension.{v,u,max u v,max u (v+1),max (max u v) w} J) :=
by
  exact CategoricalTheorem11.exists_modularExtension S T J hJ jf jfKernel hENO

end P18Relative

section

/-! Original categorical solutions. This module never imports the challenge.
Only completed original targets are exported here. -/
open Classical CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Paper18.Category
namespace P18Original
universe v u w
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [BraidedCategory C]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

include S in
theorem lemma2_1 (J : PivotalStructure C) (hC : IsNondegenerate (C := C)) :
    ∃ t : C, ∃ A : TensorInverse t,
      (∀ X : C, Simple X →
        (doubleBraiding t X).hom =
          (J.rightDim X / J.rightDim (dual C X)) • 𝟙 (t ⊗ X)) ∧
      (J.twistIso A.inverse).hom = 𝟙 A.inverse ∧
      (∀ u : C, TensorInverse u →
        (∀ X : C, Simple X →
          (doubleBraiding u X).hom =
            (J.rightDim X / J.rightDim (dual C X)) • 𝟙 (u ⊗ X)) →
        Nonempty (t ≅ u)) :=
  Paper18.Category.lemma2_1 S J hC

end P18Original

namespace P18Original
open Paper18.Category.AppendixBPointed

theorem appendixB :
    ∃ _T : TannakianCenter B (Multiplicative (ZMod 2)),
      IsModular canonicalPivotal ∧
      canonicalPivotal.twistNatIso = twist ∧
      prescribedPivotal.Spherical ∧
      centerPrescribedPivotal = centerCanonicalPivotal ∧
      PreservesPivotal BInclusion prescribedPivotal nonsphericalPivotalExtension ∧
      ¬ nonsphericalPivotalExtension.Spherical ∧
      (∀ J : PivotalStructure Vec, J.Spherical →
        ¬ PreservesPivotal BInclusion prescribedPivotal J) ∧
      (PointedVec.skeleton Paper18.PointedA).fusionBasis.totalFPdim =
        bSkeleton.fusionBasis.totalFPdim * bCenterSkeleton.fusionBasis.totalFPdim := by
  obtain ⟨T, _, h⟩ := appendixB_actual_counterexample
  exact ⟨T,h⟩

end P18Original
end

section

/-! Actual-category solutions; does not import the challenge. -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Paper18.Category
namespace P18Category
universe v u w v' u' w'
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (F : C ⥤ D) [F.Additive] [F.Monoidal]

theorem dominant (hF : FiniteSemisimpleSkeleton.Dominant F)
    (hS : S.Integral) : T.Integral :=
  S.lemma3_1_dominant T F hF hS

theorem preserves_fpdim (X : C) : T.fpdim (F.obj X) = S.fpdim X :=
  S.fpdim_map T F X

include F in
theorem reflects_integrality (hT : T.Integral) : S.Integral :=
  S.integral_of_integral_target T F hT

end P18Category

namespace P18Category
section Equivariant
universe vg ug wg sg
variable {G : Type wg} [Group G] [Fintype G]
  {C : Type ug} [Category.{vg} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  (A : WeakAction G C)
  [∀ g : G, (A.ρ g).Additive] [∀ g : G, (A.ρ g).Linear ℂ]
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  {ι : Type sg} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

theorem equivariant : (A.equivariantSkeleton S).Integral ↔ S.Integral :=
  A.lemma3_1_equivariant S

end Equivariant
end P18Category
end

section

/-! Independent completed Johnson--Freyd solutions. This module never imports the challenge. -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Paper18.Category
universe v u w
namespace P18JohnsonFreyd
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [BraidedCategory C]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {G : Type} [Group G]

section LiteralProposition24
universe v' u' w'
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)] [BraidedCategory D]
  {κ : Type w'} [Fintype κ] (U : FiniteSemisimpleSkeleton D κ)

include S in
/-- Literal JF Proposition 2.4: source and actual centralizer positivity
imply positivity of the fixed actual nondegenerate ambient category.
No ambient pivotal structure is a premise. -/
theorem proposition2_4 (J : PivotalStructure C) (hJ : J.Positive)
    (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Braided] [F.Full] [F.Faithful]
    (hD : IsNondegenerate (C := D))
    (hcentralizer :
      letI := U.fullSubcategoryHasKernels (centralizerProperty (Set.range F.obj))
      letI := U.fullSubcategoryRightRigid (centralizerProperty (Set.range F.obj))
      letI := U.fullSubcategorySimpleUnit (centralizerProperty (Set.range F.obj))
      ∃ K : PivotalStructure (CentralizerCategory (Set.range F.obj)), K.Positive) :
    ∃ K : PivotalStructure D, K.Positive := by
  letI := U.fullSubcategoryHasKernels (centralizerProperty (Set.range F.obj))
  letI := U.fullSubcategoryRightRigid (centralizerProperty (Set.range F.obj))
  letI := U.fullSubcategorySimpleUnit (centralizerProperty (Set.range F.obj))
  obtain ⟨K, hK⟩ := hcentralizer
  exact U.exists_positive_of_positive_source_centralizer S J hJ F hD K hK

end LiteralProposition24

end P18JohnsonFreyd
end

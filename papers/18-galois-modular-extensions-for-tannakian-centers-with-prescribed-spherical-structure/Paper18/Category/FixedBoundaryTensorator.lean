import Paper18.Category.FixedBoundaryTensoratorRigid
import Paper18.Category.FixedBoundaryScalarTrivialization

/-! # Actual scalar cocycle exhaustivity and boundary-retaining correction

The scalar coordinates are derived from actual native module naturality,
rigidity, and the actual tensorator equations. The existing normalized H²
calculation then supplies an actual specified-boundary isomorphism.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w vA uA
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]
  (F : C ⥤ C) [F.Braided] [F.IsEquivalence] [F.Additive] [F.Linear ℂ]
  (a : SignKernel.inclusion χ ⋙ F ≅ SignKernel.inclusion χ)
  [NatTrans.IsMonoidal a.hom]
  (hF : ∀ X : C, Homogeneous χ 1 X → Homogeneous χ 1 (F.obj X))
  (e : F ≅ 𝟭 C)
  (he : ∀ X : SignKernel.Positive χ, e.hom.app X.obj = a.hom.app X)
  [hmodule : ModuleFunctor.IsModuleNatural (SignKernel.Positive χ) (comparisonRestriction χ F a hF e).hom]
  (j : ι) (hj : Homogeneous χ 1 (S.simpleObject j))

include S he hmodule hj in
/-- Actual tensorator exhaustivity: an ordinary comparison with actual
native odd module naturality has a genuine normalized C₂ cocycle as its
entire tensorator defect. No scalar-cocycle certificate is an input. -/
theorem exists_tensorator_cocycle :
    ∃ lam : Paper18.Z2Cocycle, ∀ (g h : ZMod 2) (X Y : C),
      Homogeneous χ g X → Homogeneous χ h Y →
        tensoratorDefect F e X Y = (lam.toFun g h : ℂ) • 𝟙 (X ⊗ Y) := by
  exact exists_tensorator_cocycle_of_mixed F e χ
    (fun hX hY => tensoratorDefect_zero_left χ F a hF e he hX hY)
    (fun hX hY => tensoratorDefect_zero_right χ F a hF e he hX hY) S j hj

end Paper18.Category.FixedBoundary

namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {A : Type uA} [Category.{vA} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A]
  (i : A ⥤ C) [i.Monoidal] (P : BoundaryAutoequivalence i)
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]
  (hχ : ∀ X : C, χ.hom.app X ≫ χ.hom.app X=𝟙 X)
  (a : SignKernel.inclusion χ ⋙ P.functor ≅ SignKernel.inclusion χ)
  [NatTrans.IsMonoidal a.hom]
  (hF : ∀ X : C, FixedBoundary.Homogeneous χ 1 X → FixedBoundary.Homogeneous χ 1 (P.functor.obj X))
  (e : P.functor ≅ 𝟭 C)
  (he : ∀ X : SignKernel.Positive χ, e.hom.app X.obj=a.hom.app X)
  [hmodule : ModuleFunctor.IsModuleNatural (SignKernel.Positive χ)
    (FixedBoundary.comparisonRestriction χ P.functor a hF e).hom]
  (hBoundary : ∀ X : A, e.hom.app (i.obj X)=P.boundary.hom.app X)
  (hi : ∀ X : A, FixedBoundary.Homogeneous χ 0 (i.obj X))
  (j : ι) (hj : FixedBoundary.Homogeneous χ 1 (S.simpleObject j))

include S hχ he hmodule hBoundary hi hj in
/-- Actual native module comparison implies an actual specified-boundary
monoidal trivialization. Scalar coordinates and the normalized cocycle
are derived internally, and H² correction preserves the chosen boundary. -/
theorem BoundaryAutoequivalence.trivializable_of_native_comparison : P.Trivializable := by
  obtain ⟨lam, hd⟩ := FixedBoundary.exists_tensorator_cocycle S χ P.functor a hF e he j hj
  exact P.trivializable_of_scalar_tensorator_defect S i χ hχ e hBoundary hi lam hd

/-- The actual monoidal natural isomorphism, including its prescribed
boundary equality, selected from the proved construction. -/
def BoundaryAutoequivalence.boundaryIsoOfNativeComparison :
    BoundaryIso i P (BoundaryAutoequivalence.identity i) :=
  Classical.choice (P.trivializable_of_native_comparison S i χ hχ a hF e he hBoundary hi j hj)

end Paper18.Category

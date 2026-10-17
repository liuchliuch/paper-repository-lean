import Paper18.Category.ModuleFunctorFiniteRepresentable
import Paper18.Category.ModuleAlphaInductionRightTensor

/-! # The genuine crossed square gives right module naturality

The crossing is an actual morphism in the actual homogeneous category.
Its genuine naturality, hexagon and preservation square force the
representing isomorphism to respect the ordinary right tensor lineator.
Epimorphic cancellation follows from actual semisimple splitting.
No transparency conclusion is an input.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u w
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom] (d : ZMod 2)
  [BraidedCategory (SignKernel.Positive χ)]

local notation "M" => HomogeneousCategory χ d
local notation "Alpha" => ModuleAlphaInduction.negative (SignKernel.Positive χ) M

/-- The ordinary right tensor lineator for left tensoring by Z. -/
def canonicalRightLineator (Z B : SignKernel.Positive χ) (n : M) :
    ((Alpha).obj Z).toFunctor.obj ((homogeneousRightTensor χ d B).obj n) ⟶
      (homogeneousRightTensor χ d B).obj (((Alpha).obj Z).toFunctor.obj n) := by
  change Z.obj ⊗ (n.obj ⊗ B.obj) ⟶ (Z.obj ⊗ n.obj) ⊗ B.obj
  exact (α_ Z.obj n.obj B.obj).inv

include S in
/-- The true crossed square forces actual right module naturality of a
true representing isomorphism. The supplied equations are precisely the
crossing's naturality, its actual hexagon, and its functorial preservation. -/
theorem right_lineator_of_crossed_square
    (G : ModuleAlphaInduction.End (SignKernel.Positive χ) M)
    (Z X B : SignKernel.Positive χ) (b : (Alpha).obj Z ≅ G) (n : M)
    (c : X ⊙ₗ n ⟶ (homogeneousRightTensor χ d B).obj n) [Epi c]
    (cZ : X ⊙ₗ (((Alpha).obj Z).toFunctor.obj n) ⟶
      (homogeneousRightTensor χ d B).obj (((Alpha).obj Z).toFunctor.obj n))
    (cG : X ⊙ₗ G.toFunctor.obj n ⟶ (homogeneousRightTensor χ d B).obj (G.toFunctor.obj n))
    (r : (homogeneousRightTensor χ d B).obj (G.toFunctor.obj n) ⟶
      G.toFunctor.obj ((homogeneousRightTensor χ d B).obj n))
    (hnat : (X ⊴ₗ b.hom.val.app n) ≫ cG =
      cZ ≫ (homogeneousRightTensor χ d B).map (b.hom.val.app n))
    (hhex : cZ = Functor.LaxLeftLinear.μₗ ((Alpha).obj Z).toFunctor X n ≫
      ((Alpha).obj Z).toFunctor.map c ≫ canonicalRightLineator χ d Z B n)
    (hG : Functor.LaxLeftLinear.μₗ G.toFunctor X n ≫ G.toFunctor.map c = cG ≫ r) :
    b.hom.val.app ((homogeneousRightTensor χ d B).obj n) =
      canonicalRightLineator χ d Z B n ≫
        (homogeneousRightTensor χ d B).map (b.hom.val.app n) ≫ r := by
  letI : HasKernels M := homogeneousHasKernels χ d S
  let split := (homogeneousSkeleton χ d S).splitEpi c
  letI : IsSplitEpi c := ⟨⟨split⟩⟩
  haveI : Epi (((Alpha).obj Z).toFunctor.map c) := inferInstance
  apply (cancel_epi (Functor.LaxLeftLinear.μₗ ((Alpha).obj Z).toFunctor X n ≫
    ((Alpha).obj Z).toFunctor.map c)).mp
  calc
    _ = Functor.LaxLeftLinear.μₗ ((Alpha).obj Z).toFunctor X n ≫
        b.hom.val.app (X ⊙ₗ n) ≫ G.toFunctor.map c := by
      rw [Category.assoc, b.hom.val.naturality]
    _ = (X ⊴ₗ b.hom.val.app n) ≫
        Functor.LaxLeftLinear.μₗ G.toFunctor X n ≫ G.toFunctor.map c := by
      rw [← ModuleFunctor.IsModuleNatural.lineator_assoc]
    _ = (X ⊴ₗ b.hom.val.app n) ≫ cG ≫ r := by rw [hG]
    _ = cZ ≫ (homogeneousRightTensor χ d B).map (b.hom.val.app n) ≫ r := by
      rw [← Category.assoc, hnat, Category.assoc]
    _ = _ := by rw [hhex]; simp only [Category.assoc]

end Paper18.Category.FixedBoundary

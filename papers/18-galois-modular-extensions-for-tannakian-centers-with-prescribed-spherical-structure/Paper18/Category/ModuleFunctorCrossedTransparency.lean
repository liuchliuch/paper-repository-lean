import Paper18.Category.ModuleFunctorCrossedTransparencyBasic

/-! # A genuine crossed square forces the alpha representative to centralize

The positive crossed hexagon fixes the ordinary right lineator. The
negative actual central crossing gives another calculation of that same
lineator. Actual half-braiding coherence and normalized rigid contraction
then give genuine neutral monodromy equal to the identity.
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
  (L : SignKernel.Positive χ ⥤ Center C)
  (e : SignKernel.inclusion χ ≅ L ⋙ Center.forget C)
local notation "M" => HomogeneousCategory χ d
local notation "Alpha" => ModuleAlphaInduction.negative (SignKernel.Positive χ) M
local notation "K" => ModuleFunctor.strictCenterFunctor L (SignKernel.inclusion χ) e

/-- The actual neutral half-braiding against an actual homogeneous object. -/
def neutralHalfCross (B : SignKernel.Positive χ) (n : M) :
    B ⊙ₗ n ≅ (homogeneousRightTensor χ d B).obj n :=
  ObjectProperty.isoMk _ (((K).obj B).2.β n.obj)

/-- Half-braiding naturality holds for the actual representing components. -/
lemma neutralHalfCross_naturality (B : SignKernel.Positive χ) {n m : M} (f : n ⟶ m) :
    (B ⊴ₗ f) ≫ (neutralHalfCross χ d L e B m).hom =
      (neutralHalfCross χ d L e B n).hom ≫ (homogeneousRightTensor χ d B).map f :=
  ((K).obj B).2.naturality (show n.obj ⟶ m.obj from f)

/-- The actual negative-crossing square compares the left and the fixed
ordinary right lineators on the actual representative. -/
theorem representative_halfCross_equation
    (G : ModuleAlphaInduction.End (SignKernel.Positive χ) M)
    (Z B : SignKernel.Positive χ) (b : (Alpha).obj Z ≅ G) (n : M)
    (r : (homogeneousRightTensor χ d B).obj (G.toFunctor.obj n) ⟶
      G.toFunctor.obj ((homogeneousRightTensor χ d B).obj n)) [IsIso r]
    (hRight : b.hom.val.app ((homogeneousRightTensor χ d B).obj n) =
      canonicalRightLineator χ d Z B n ≫
        (homogeneousRightTensor χ d B).map (b.hom.val.app n) ≫ r)
    (hG : Functor.LaxLeftLinear.μₗ G.toFunctor B n ≫
        G.toFunctor.map (neutralHalfCross χ d L e B n).hom =
      (neutralHalfCross χ d L e B (G.toFunctor.obj n)).hom ≫ r) :
    Functor.LaxLeftLinear.μₗ ((Alpha).obj Z).toFunctor B n ≫
        ((Alpha).obj Z).toFunctor.map (neutralHalfCross χ d L e B n).hom ≫
          canonicalRightLineator χ d Z B n =
      (neutralHalfCross χ d L e B (((Alpha).obj Z).toFunctor.obj n)).hom := by
  letI : IsIso (b.hom.val.app n) :=
    ((ModuleFunctor.forget.mapIso b).app n).isIso_hom
  apply (cancel_mono ((homogeneousRightTensor χ d B).map (b.hom.val.app n) ≫ r)).mp
  calc
    _ = Functor.LaxLeftLinear.μₗ ((Alpha).obj Z).toFunctor B n ≫
        ((Alpha).obj Z).toFunctor.map (neutralHalfCross χ d L e B n).hom ≫
          b.hom.val.app ((homogeneousRightTensor χ d B).obj n) := by
      simp only [Category.assoc, ← hRight]
    _ = Functor.LaxLeftLinear.μₗ ((Alpha).obj Z).toFunctor B n ≫
        b.hom.val.app (B ⊙ₗ n) ≫ G.toFunctor.map (neutralHalfCross χ d L e B n).hom := by
      rw [b.hom.val.naturality]
    _ = (B ⊴ₗ b.hom.val.app n) ≫ Functor.LaxLeftLinear.μₗ G.toFunctor B n ≫
        G.toFunctor.map (neutralHalfCross χ d L e B n).hom := by
      rw [← ModuleFunctor.IsModuleNatural.lineator_assoc]
    _ = (B ⊴ₗ b.hom.val.app n) ≫
        (neutralHalfCross χ d L e B (G.toFunctor.obj n)).hom ≫ r := by rw [hG]
    _ = _ := by rw [← Category.assoc, neutralHalfCross_naturality, Category.assoc]

variable [RightRigidCategory C] [Simple (𝟙_ C)]
attribute [local instance 2000] RightRigidCategory.rightDual

include S in
/-- The actual representative centralizes B once both genuine crossed
calculations fix its right lineator. Rigidity removes the actual odd
simple tensor factor; no scalar monodromy hypothesis is supplied. -/
theorem representative_centralizes_of_right_lineator
    (hL : NegativeCentralCompatibility χ L e)
    (G : ModuleAlphaInduction.End (SignKernel.Positive χ) M)
    (Z B : SignKernel.Positive χ) (b : (Alpha).obj Z ≅ G) (n : M) [Simple n.obj]
    (r : (homogeneousRightTensor χ d B).obj (G.toFunctor.obj n) ⟶
      G.toFunctor.obj ((homogeneousRightTensor χ d B).obj n)) [IsIso r]
    (hRight : b.hom.val.app ((homogeneousRightTensor χ d B).obj n) =
      canonicalRightLineator χ d Z B n ≫
        (homogeneousRightTensor χ d B).map (b.hom.val.app n) ≫ r)
    (hG : Functor.LaxLeftLinear.μₗ G.toFunctor B n ≫
        G.toFunctor.map (neutralHalfCross χ d L e B n).hom =
      (neutralHalfCross χ d L e B (G.toFunctor.obj n)).hom ≫ r) :
    Centralizes Z B := by
  have h := representative_halfCross_equation χ d L e G Z B b n r hRight hG
  rw [ModuleAlphaInduction.negative_μ] at h
  simp only [Category.assoc] at h
  change (α_ B.obj Z.obj n.obj).inv ≫
    (show B.obj ⊗ Z.obj ⟶ Z.obj ⊗ B.obj from (β_ B Z).hom) ▷ n.obj ≫
      (α_ Z.obj B.obj n.obj).hom ≫
      Z.obj ◁ (((K).obj B).2.β n.obj).hom ≫ (α_ Z.obj n.obj B.obj).inv =
    (((K).obj B).2.β (Z.obj ⊗ n.obj)).hom at h
  rw [HalfBraiding.monoidal] at h
  have ht : (show B.obj ⊗ Z.obj ⟶ Z.obj ⊗ B.obj from (β_ B Z).hom) ▷ n.obj =
      (((K).obj B).2.β Z.obj).hom ▷ n.obj := by
    let tail := (α_ Z.obj B.obj n.obj).hom ≫
      Z.obj ◁ (((K).obj B).2.β n.obj).hom ≫ (α_ Z.obj n.obj B.obj).inv
    apply (cancel_mono tail).mp
    apply (cancel_epi (α_ B.obj Z.obj n.obj).inv).mp
    simpa only [Category.assoc] using h
  have hb : (show B.obj ⊗ Z.obj ⟶ Z.obj ⊗ B.obj from (β_ B Z).hom) =
      (((K).obj B).2.β Z.obj).hom := by
    have hh := congrArg (ModuleFunctor.simpleContraction S n.obj) ht
    simpa only [ModuleFunctor.simpleContraction_whiskerRight] using hh
  change (show Z.obj ⊗ B.obj ⟶ B.obj ⊗ Z.obj from (β_ Z B).hom) ≫
    (show B.obj ⊗ Z.obj ⟶ Z.obj ⊗ B.obj from (β_ B Z).hom) = 𝟙 _
  rw [hb, hL B Z]
  exact (β_ Z B).hom_inv_id

include S in
/-- Both actual crossings together force actual centralization. The
positive square determines the right lineator and the negative square
then removes the actual odd simple tensor factor by rigidity. -/
theorem representative_centralizes_of_crossed_square
    (hL : NegativeCentralCompatibility χ L e)
    (G : ModuleAlphaInduction.End (SignKernel.Positive χ) M)
    (Z X B : SignKernel.Positive χ) (b : (Alpha).obj Z ≅ G) (n : M) [Simple n.obj]
    (c : X ⊙ₗ n ⟶ (homogeneousRightTensor χ d B).obj n) [Epi c]
    (cZ : X ⊙ₗ (((Alpha).obj Z).toFunctor.obj n) ⟶
      (homogeneousRightTensor χ d B).obj (((Alpha).obj Z).toFunctor.obj n))
    (cG : X ⊙ₗ G.toFunctor.obj n ⟶ (homogeneousRightTensor χ d B).obj (G.toFunctor.obj n))
    (r : (homogeneousRightTensor χ d B).obj (G.toFunctor.obj n) ⟶
      G.toFunctor.obj ((homogeneousRightTensor χ d B).obj n)) [IsIso r]
    (hnat : (X ⊴ₗ b.hom.val.app n) ≫ cG =
      cZ ≫ (homogeneousRightTensor χ d B).map (b.hom.val.app n))
    (hhex : cZ = Functor.LaxLeftLinear.μₗ ((Alpha).obj Z).toFunctor X n ≫
      ((Alpha).obj Z).toFunctor.map c ≫ canonicalRightLineator χ d Z B n)
    (hG : Functor.LaxLeftLinear.μₗ G.toFunctor X n ≫ G.toFunctor.map c = cG ≫ r)
    (hGneg : Functor.LaxLeftLinear.μₗ G.toFunctor B n ≫
        G.toFunctor.map (neutralHalfCross χ d L e B n).hom =
      (neutralHalfCross χ d L e B (G.toFunctor.obj n)).hom ≫ r) :
    Centralizes Z B :=
  representative_centralizes_of_right_lineator S χ d L e hL G Z B b n r
    (right_lineator_of_crossed_square S χ d G Z X B b n c cZ cG r hnat hhex hG) hGneg

/-- Testing the actual translated neutral image suffices for the entire
actual Müger center, since the algebra translation is an actual
essentially surjective functor. -/
theorem representative_mem_mugerCenter_of_translated_tests
    (Z : SignKernel.Positive χ) (sigma : SignKernel.Positive χ ⥤ SignKernel.Positive χ)
    [sigma.EssSurj] (h : ∀ X, Centralizes Z (sigma.obj X)) : Z ∈ mugerCenter := by
  intro B _
  obtain ⟨X, ⟨q⟩⟩ := Functor.EssSurj.mem_essImage (F := sigma) B
  exact (centralizes_iso_right q).mp (h X)

end Paper18.Category.FixedBoundary

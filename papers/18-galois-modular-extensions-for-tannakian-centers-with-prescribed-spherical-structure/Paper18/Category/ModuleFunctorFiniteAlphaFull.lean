import Paper18.Category.ModuleFunctorFiniteAlphaFaithful
import Paper18.Category.ModuleFunctorFiniteDensity
import Paper18.Category.ModuleFunctorFiniteCenterLift
import Paper18.Category.ModuleAlphaInductionDensityDiagram
import Paper18.Category.TensorCharacters

/-! # Actual fullness of homogeneous alpha induction from a true central lift

The true central lift supplies crossings only for neutral objects. The
matrix-action identity is derived from actual module naturality and actual
evaluation naturality. Normalized rigid contraction gives an actual
preimage morphism, and actual one-simple density recovers the entire map.
No fullness or representing-object conclusion is an input.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u w
namespace Paper18.Category.FixedBoundary
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]

/-- The actual tensor product of a simple and its actual right dual is
neutral for every actual monoidal identity automorphism. -/
lemma simple_tensor_dual_positive (j : ι) :
    SignKernel.positiveProperty χ (S.simpleObject j ⊗ dual C (S.simpleObject j)) := by
  letI : Simple (dual C (S.simpleObject j)) := S.simple_rightDual (S.simpleObject j)
  rw [SignKernel.mem_positive, TensorAutomorphism.tensor_component_simple]
  have hd : TensorAutomorphism.scalar χ (dual C (S.simpleObject j)) =
      (TensorAutomorphism.scalar χ (S.simpleObject j))⁻¹ :=
    (TensorAutomorphism.scalar_iso χ (S.dualIso j)).symm.trans
      (TensorAutomorphism.scalar_dualLabel χ S j)
  rw [hd, mul_inv_cancel₀ (TensorAutomorphism.scalar_ne_zero χ (S.simpleObject j)), one_smul]

variable (d : ZMod 2) [BraidedCategory (SignKernel.Positive χ)]
  (L : SignKernel.Positive χ ⥤ Center C)
  (e : SignKernel.inclusion χ ≅ L ⋙ Center.forget C)

local notation "K" => ModuleFunctor.strictCenterFunctor L (SignKernel.inclusion χ) e
local notation "Alpha" => ModuleAlphaInduction.negative (SignKernel.Positive χ) (HomogeneousCategory χ d)

/-- Compatibility of the actual neutral central lift with the negative
braiding convention. It concerns genuine half-braidings, not a desired
fullness or dimension conclusion. -/
def NegativeCentralCompatibility : Prop := ∀ X Y : SignKernel.Positive χ,
  (((K).obj X).2.β Y.obj).hom =
    (show X.obj ⊗ Y.obj ⟶ Y.obj ⊗ X.obj from (β_ Y X).inv)

variable (hL : NegativeCentralCompatibility χ L e)

include hL in
lemma negativeCentral_lineator (X Y : SignKernel.Positive χ)
    (n : HomogeneousCategory χ d) :
    (ModuleAlphaInduction.centralLineator (M := C) ((K).obj X) Y.obj n.obj).inv =
      Functor.LaxLeftLinear.μₗ ((Alpha).obj X).toFunctor Y n := by
  have hi : ((K).obj X).2.β Y.obj =
      (SignKernel.inclusion χ).mapIso (β_ Y X).symm := Iso.ext (hL X Y)
  rw [ModuleAlphaInduction.negative_μ]
  dsimp only [ModuleAlphaInduction.centralLineator, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, MonoidalLeftAction.actionRight_map]
  rw [hi]
  simp only [Category.assoc]
  change (α_ Y.obj X.obj n.obj).inv ≫
      (show Y.obj ⊗ X.obj ⟶ X.obj ⊗ Y.obj from (β_ Y X).hom) ▷ n.obj ≫
        (α_ X.obj Y.obj n.obj).hom = _
  rfl

/-- Actual negative alpha induction is full when the neutral action has
the specified genuine central lift. Every actual preimage is constructed
by the normalized rigid contraction; the conclusion is not assumed. -/
def homogeneousNegativeFull (j : ι) (hj : Homogeneous χ d (S.simpleObject j)) :
    (Alpha).Full where
  map_surjective {X Y} τ := by
    let n : HomogeneousCategory χ d := ⟨S.simpleObject j, hj⟩
    let c : SignKernel.Positive χ :=
      ⟨S.simpleObject j ⊗ dual C (S.simpleObject j), simple_tensor_dual_positive S χ j⟩
    let v : c ⊙ₗ n ⟶ n :=
      ModuleAlphaInduction.capAction (ε_ (S.simpleObject j) (dual C (S.simpleObject j)))
    have hcap : ModuleAlphaInduction.centralCapAction ((K).obj X)
          (ε_ (S.simpleObject j) (dual C (S.simpleObject j))) ≫ τ.val.app n =
        (S.simpleObject j ⊗ dual C (S.simpleObject j)) ◁ τ.val.app n ≫
          ModuleAlphaInduction.centralCapAction ((K).obj Y)
            (ε_ (S.simpleObject j) (dual C (S.simpleObject j))) := by
      dsimp only [ModuleAlphaInduction.centralCapAction]
      rw [negativeCentral_lineator χ d L e hL X c n,
        negativeCentral_lineator χ d L e hL Y c n]
      simp only [Category.assoc]
      change Functor.LaxLeftLinear.μₗ ((Alpha).obj X).toFunctor c n ≫
          ((Alpha).obj X).toFunctor.map v ≫ τ.val.app n =
        (c ⊴ₗ τ.val.app n) ≫ Functor.LaxLeftLinear.μₗ ((Alpha).obj Y).toFunctor c n ≫
          ((Alpha).obj Y).toFunctor.map v
      rw [τ.val.naturality, ← ModuleFunctor.IsModuleNatural.lineator_assoc]
    obtain ⟨a, ha⟩ := ModuleAlphaInduction.exists_preimage_whiskerRight_of_capAction (K)
      (ModuleFunctor.normalizedLeftCup S (S.simpleObject j))
      (ε_ (S.simpleObject j) (dual C (S.simpleObject j)))
      (ModuleFunctor.normalizedLeftCup_evaluation S (S.simpleObject j)) (τ.val.app n) hcap
    refine ⟨a, ?_⟩
    apply ModuleFunctor.bundled_hom_ext
    apply homogeneousModuleNatTrans_ext S χ d ((Alpha).obj X).toFunctor
      ((Alpha).obj Y).toFunctor ((Alpha).map a).val τ.val j hj
    rw [ModuleAlphaInduction.negative_map]
    have hm : ((K).map a).f = (a : X.obj ⟶ Y.obj) :=
      ModuleFunctor.strictCenterFunctor_map_f L (SignKernel.inclusion χ) e a
    rw [hm] at ha
    exact ha.symm

end Paper18.Category.FixedBoundary

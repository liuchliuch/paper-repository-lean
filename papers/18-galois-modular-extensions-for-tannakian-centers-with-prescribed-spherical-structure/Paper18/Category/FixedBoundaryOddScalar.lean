import Paper18.Category.FixedBoundaryOddConnected
import Paper18.Category.SemisimpleSplitting

/-!
# Scalars extracted from actual homogeneous module automorphisms

Neutral tensor connectivity and naturality force a module-natural
endomorphism of the identity on one actual homogeneous component to have
one scalar on all its simple objects. Actual semisimple decompositions
then give the same scalar on every object of that component.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u w
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom] (d : ZMod 2)

/-- The actual Schur scalar of a component on an ambient simple. -/
def homogeneousModuleScalar (τ : 𝟭 (HomogeneousCategory χ d) ⟶
    𝟭 (HomogeneousCategory χ d))
    (i : {i : ι // Homogeneous χ d (S.simpleObject i)}) : ℂ :=
  simpleScalarEquiv (S.simpleObject i.val) (τ.app ⟨S.simpleObject i.val, i.property⟩)

@[simp] theorem homogeneousModuleScalar_spec
    (τ : 𝟭 (HomogeneousCategory χ d) ⟶ 𝟭 (HomogeneousCategory χ d))
    (i : {i : ι // Homogeneous χ d (S.simpleObject i)}) :
    homogeneousModuleScalar S χ d τ i • 𝟙 (S.simpleObject i.val) =
      τ.app ⟨S.simpleObject i.val, i.property⟩ :=
  simpleScalarEquiv_spec _ _

/-- No independent scalar choices on the simple labels survive actual
module naturality with respect to the neutral category. -/
theorem homogeneousModuleScalar_eq
    (τ : 𝟭 (HomogeneousCategory χ d) ⟶ 𝟭 (HomogeneousCategory χ d))
    [ModuleFunctor.IsModuleNatural (SignKernel.Positive χ) τ]
    (i j : {i : ι // Homogeneous χ d (S.simpleObject i)}) :
    homogeneousModuleScalar S χ d τ i = homogeneousModuleScalar S χ d τ j := by
  obtain ⟨k, hk, hn⟩ := neutral_tensor_connects S χ i.val j.val i.property j.property
  obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hn
  let K : SignKernel.Positive χ := ⟨S.simpleObject k, hk⟩
  let I : HomogeneousCategory χ d := ⟨S.simpleObject i.val, i.property⟩
  let J : HomogeneousCategory χ d := ⟨S.simpleObject j.val, j.property⟩
  have hmodule := ModuleFunctor.IsModuleNatural.lineator
    (C := SignKernel.Positive χ) (τ := τ) K I
  change 𝟙 _ ≫ τ.app (homogeneousActionObj χ d K I) =
    (K.obj ◁ (show I.obj ⟶ I.obj from τ.app I)) ≫ 𝟙 _ at hmodule
  simp only [Category.id_comp, Category.comp_id] at hmodule
  have hI : (show I.obj ⟶ I.obj from τ.app I) =
      homogeneousModuleScalar S χ d τ i • 𝟙 I.obj :=
    (homogeneousModuleScalar_spec S χ d τ i).symm
  have hJ : (show J.obj ⟶ J.obj from τ.app J) =
      homogeneousModuleScalar S χ d τ j • 𝟙 J.obj :=
    (homogeneousModuleScalar_spec S χ d τ j).symm
  have hnatur := τ.naturality
    (show J ⟶ homogeneousActionObj χ d K I from f)
  change f ≫ τ.app (homogeneousActionObj χ d K I) = τ.app J ≫ f at hnatur
  rw [hmodule] at hnatur
  have hnaturC : f ≫ (K.obj ◁ (show I.obj ⟶ I.obj from τ.app I)) =
      (show J.obj ⟶ J.obj from τ.app J) ≫ f := hnatur
  rw [hI, hJ] at hnaturC
  change f ≫ (S.simpleObject k ◁
    (homogeneousModuleScalar S χ d τ i • 𝟙 (S.simpleObject i.val))) =
    (homogeneousModuleScalar S χ d τ j • 𝟙 (S.simpleObject j.val)) ≫ f at hnaturC
  apply smul_left_injective ℂ hf
  simpa only [MonoidalLinear.whiskerLeft_smul, MonoidalCategory.whiskerLeft_id,
    Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp] using hnaturC

/-- One actual simple scalar determines the module endomorphism on every
actual object, using the inherited finite semisimple decomposition. -/
theorem homogeneousModuleNat_eq_scalar
    (τ : 𝟭 (HomogeneousCategory χ d) ⟶ 𝟭 (HomogeneousCategory χ d))
    [ModuleFunctor.IsModuleNatural (SignKernel.Positive χ) τ]
    (i : {i : ι // Homogeneous χ d (S.simpleObject i)})
    (X : HomogeneousCategory χ d) :
    τ.app X = homogeneousModuleScalar S χ d τ i • 𝟙 X := by
  apply (homogeneousSkeleton χ d S).hom_ext_simples
  intro j a
  have hn := τ.naturality a
  change a ≫ τ.app X = τ.app ⟨S.simpleObject j.val, j.property⟩ ≫ a at hn
  rw [← homogeneousModuleScalar_spec S χ d τ j,
    ← homogeneousModuleScalar_eq S χ d τ i j] at hn
  change (show S.simpleObject j.val ⟶ X.obj from a) ≫
    (show X.obj ⟶ X.obj from τ.app X) =
    (homogeneousModuleScalar S χ d τ i • 𝟙 (S.simpleObject j.val)) ≫
      (show S.simpleObject j.val ⟶ X.obj from a) at hn
  change (show S.simpleObject j.val ⟶ X.obj from a) ≫
    (show X.obj ⟶ X.obj from τ.app X) =
    (show S.simpleObject j.val ⟶ X.obj from a) ≫
      (homogeneousModuleScalar S χ d τ i • 𝟙 X.obj)
  simpa only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id] using hn

/-- The extracted scalar of an actual module natural automorphism is
nonzero, as tested on an actual nonzero simple object. -/
theorem homogeneousModuleScalar_ne_zero
    (τ : 𝟭 (HomogeneousCategory χ d) ≅ 𝟭 (HomogeneousCategory χ d))
    [ModuleFunctor.IsModuleNatural (SignKernel.Positive χ) τ.hom]
    (i : {i : ι // Homogeneous χ d (S.simpleObject i)}) :
    homogeneousModuleScalar S χ d τ.hom i ≠ 0 := by
  intro hz
  have hh := τ.hom_inv_id_app ⟨S.simpleObject i.val, i.property⟩
  change τ.hom.app ⟨S.simpleObject i.val, i.property⟩ ≫
    τ.inv.app ⟨S.simpleObject i.val, i.property⟩ = 𝟙 (S.simpleObject i.val) at hh
  rw [← homogeneousModuleScalar_spec S χ d τ.hom i, hz, zero_smul, zero_comp] at hh
  exact CategoryTheory.id_nonzero (S.simpleObject i.val) hh.symm

/-- Actual module automorphisms on a nonempty homogeneous component have
unique actual complex-unit coordinates. -/
theorem homogeneousModuleAut_unique_scalar
    (τ : 𝟭 (HomogeneousCategory χ d) ≅ 𝟭 (HomogeneousCategory χ d))
    [ModuleFunctor.IsModuleNatural (SignKernel.Positive χ) τ.hom]
    (i : {i : ι // Homogeneous χ d (S.simpleObject i)}) :
    ∃! z : ℂˣ, ∀ X : HomogeneousCategory χ d,
      τ.hom.app X = (z : ℂ) • 𝟙 X := by
  let z := Units.mk0 (homogeneousModuleScalar S χ d τ.hom i)
    (homogeneousModuleScalar_ne_zero S χ d τ i)
  refine ⟨z, homogeneousModuleNat_eq_scalar S χ d τ.hom i, ?_⟩
  intro y hy
  apply Units.ext
  change (y : ℂ) = homogeneousModuleScalar S χ d τ.hom i
  apply smul_left_injective ℂ (CategoryTheory.id_nonzero (S.simpleObject i.val))
  exact (hy ⟨S.simpleObject i.val, i.property⟩).symm.trans
    (homogeneousModuleScalar_spec S χ d τ.hom i).symm

end Paper18.Category.FixedBoundary

import Paper18.Category.FixedBoundaryTensoratorMixed
import Paper18.Category.ModuleFunctorFiniteRepresentable

/-! # Rigid scalar extraction from the actual odd tensorator defect

An actual cap has a one-dimensional Hom space by rigidity and Schur's
lemma. Actual defect associativity propagates this scalar to every odd
pair; no scalar-defect premise is used in the extraction theorem.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.FixedBoundary
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]

/-- The actual cap space of a genuine simple is one-dimensional. -/
lemma finrank_simple_dual_tensor_to_unit (X : C) [Simple X] :
    Module.finrank ℂ (dual C X ⊗ X ⟶ 𝟙_ C) = 1 := by
  calc
    _ = Module.finrank ℂ (X ⟶ X ⊗ 𝟙_ C) :=
      (tensorLeftHomLinearEquiv X X (dual C X) (𝟙_ C)).finrank_eq
    _ = Module.finrank ℂ (X ⟶ X) := finrank_hom_iso (Iso.refl X) (ρ_ X)
    _ = 1 := CategoryTheory.finrank_endomorphism_simple_eq_one ℂ X

variable (F : C ⥤ C) [F.Monoidal] (e : F ≅ 𝟭 C)
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]
  (h0l : ∀ {g : ZMod 2} {X Y : C}, Homogeneous χ 0 X → Homogeneous χ g Y →
    tensoratorDefect F e X Y = 𝟙 _)
  (h0r : ∀ {g : ZMod 2} {X Y : C}, Homogeneous χ g X → Homogeneous χ 0 Y →
    tensoratorDefect F e X Y = 𝟙 _)

include h0l h0r in
@[reassoc] lemma tensoratorDefect_odd_triple {X Y Z : C}
    (hX : Homogeneous χ 1 X) (hY : Homogeneous χ 1 Y) (hZ : Homogeneous χ 1 Z) :
    (tensoratorDefect F e X Y ▷ Z) ≫ (α_ X Y Z).hom =
      (α_ X Y Z).hom ≫ X ◁ tensoratorDefect F e Y Z := by
  have hXY : Homogeneous χ 0 (X ⊗ Y) := by simpa using homogeneous_tensor χ hX hY
  have hYZ : Homogeneous χ 0 (Y ⊗ Z) := by simpa using homogeneous_tensor χ hY hZ
  have hh := tensoratorDefect_associativity F e X Y Z
  rw [h0l hXY hZ, h0r hX hYZ] at hh
  simpa only [Category.id_comp, Category.comp_id] using hh

/-- Closing the actual odd triple equation with the actual evaluation
reflects the cap scalar to the entire adjacent tensor factor. -/
lemma tensoratorDefect_scalar_of_cap (n Y : C) (z : ℂ)
    (ht : (tensoratorDefect F e (dual C n) n ▷ Y) ≫ (α_ (dual C n) n Y).hom =
      (α_ (dual C n) n Y).hom ≫ dual C n ◁ tensoratorDefect F e n Y)
    (hc : tensoratorDefect F e (dual C n) n ≫ ε_ n (dual C n) = z • ε_ n (dual C n)) :
    tensoratorDefect F e n Y = z • 𝟙 _ := by
  apply (tensorLeftHomEquiv (n ⊗ Y) n (dual C n) Y).symm.injective
  change (dual C n ◁ tensoratorDefect F e n Y) ≫ (α_ (dual C n) n Y).inv ≫
      (ε_ n (dual C n) ▷ Y) ≫ (λ_ Y).hom =
    (dual C n ◁ (z • 𝟙 (n ⊗ Y))) ≫ (α_ (dual C n) n Y).inv ≫
      (ε_ n (dual C n) ▷ Y) ≫ (λ_ Y).hom
  apply (cancel_epi (α_ (dual C n) n Y).hom).mp
  rw [← reassoc_of% ht]
  simp only [Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, hc]
  simp only [MonoidalLinear.whiskerLeft_smul, MonoidalLinear.smul_whiskerRight,
    whiskerLeft_id, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
    Iso.hom_inv_id_assoc]

variable {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (j : ι) (hj : Homogeneous χ 1 (S.simpleObject j))

include h0l h0r hj in
/-- The actual odd tensorator defect is one and the same actual nonzero
scalar on every genuine pair of odd objects. -/
theorem exists_odd_tensorator_scalar :
    ∃ z : ℂˣ, ∀ (X Y : C), Homogeneous χ 1 X → Homogeneous χ 1 Y →
      tensoratorDefect F e X Y = (z : ℂ) • 𝟙 (X ⊗ Y) := by
  let n := S.simpleObject j
  letI : Simple (dual C n) := S.simple_rightDual n
  have hn : Homogeneous χ 1 n := hj
  have hnd : Homogeneous χ 1 (dual C n) := simple_rightDual_homogeneous S χ 1 j hj
  obtain ⟨z, hz⟩ := exists_smul_eq_of_finrank_eq_one
    (finrank_simple_dual_tensor_to_unit n)
    (exactPairing_evaluation_ne_zero n (dual C n))
    (tensoratorDefect F e (dual C n) n ≫ ε_ n (dual C n))
  have hrow (Y : C) (hY : Homogeneous χ 1 Y) : tensoratorDefect F e n Y = z • 𝟙 _ :=
    tensoratorDefect_scalar_of_cap F e n Y z
      (tensoratorDefect_odd_triple F e χ h0l h0r hnd hn hY) hz.symm
  have hz0 : z ≠ 0 := by
    intro hz0
    have hd := hrow (dual C n) hnd
    rw [hz0, zero_smul] at hd
    apply exactPairing_coevaluation_ne_zero n (dual C n)
    apply (cancel_mono (tensoratorDefect F e n (dual C n))).mp
    rw [hd]
    simp
  refine ⟨Units.mk0 z hz0, fun X Y hX hY => ?_⟩
  have hh : n ◁ tensoratorDefect F e X Y = n ◁ (z • 𝟙 (X ⊗ Y)) := by
    apply (cancel_epi (α_ n X Y).hom).mp
    rw [← tensoratorDefect_odd_triple F e χ h0l h0r hn hX hY, hrow X hX]
    simp
  have hc := congrArg (ModuleFunctor.simpleLeftContraction S n) hh
  simpa only [ModuleFunctor.simpleLeftContraction_whiskerLeft] using hc

include h0l h0r hj in
/-- The complete normalized scalar cocycle, derived from actual mixed
compatibility, rigidity and actual associativity. This theorem requires
no braiding on the ambient monoidal category. -/
theorem exists_tensorator_cocycle_of_mixed :
    ∃ lam : Paper18.Z2Cocycle, ∀ (g h : ZMod 2) (X Y : C),
      Homogeneous χ g X → Homogeneous χ h Y →
        tensoratorDefect F e X Y = (lam.toFun g h : ℂ) • 𝟙 (X ⊗ Y) := by
  obtain ⟨z, hz⟩ := exists_odd_tensorator_scalar F e χ h0l h0r S j hj
  let f : ZMod 2 → ZMod 2 → ℂˣ := fun g h => if g=0 ∨ h=0 then 1 else z
  have hf0 (h : ZMod 2) : f 0 h=1 := by simp [f]
  have hf1 (g : ZMod 2) : f g 0=1 := by simp [f]
  let lam : Paper18.Z2Cocycle :=
    { toFun := f
      norm_left := hf0
      norm_right := hf1
      cocycle := Paper18.Z2Cocycle.isCocycle_of_normalized f hf0 hf1 }
  refine ⟨lam, fun g h X Y hX hY => ?_⟩
  rcases Paper18.ZMod.two_eq_zero_or_one g with rfl | rfl
  · simpa [lam, f] using h0l hX hY
  rcases Paper18.ZMod.two_eq_zero_or_one h with rfl | rfl
  · simpa [lam, f] using h0r hX hY
  · simpa [lam, f] using hz X Y hX hY

end Paper18.Category.FixedBoundary

import Paper18.Category.SignKernelCenter
import Paper18.Category.CentralizerSimples

/-! # The actual transparent center of a sign kernel

A negative transparent simple lets every negative simple be recovered as
an actual retract of a tensor product of positive objects and transparent
objects. This identifies the actual center, without a dimension certificate.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.SignKernel
open FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [BraidedCategory C] [HasFiniteBiproducts C] [HasKernels C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (hχ : ∀ X : C, χ.hom.app X ≫ χ.hom.app X = 𝟙 X)

/-- The unit occurs as an actual retract of the dual-label tensor product. -/
def unitRetractDualTensor (a : ι) :
    Retract (𝟙_ C) (S.simpleObject (S.dualLabel a) ⊗ S.simpleObject a) := by
  have hn : S.fusionCoeff (S.dualLabel a) a S.unitLabel = 1 := by
    rw [S.fusionCoeff_right, S.fusionCoeff_one_left S.unitLabel S.unitIso]
    simp
  exact (Retract.ofIso S.unitIso.symm).trans
    (S.retractOfMultiplicityPos _ S.unitLabel (by
      change 0 < S.fusionCoeff (S.dualLabel a) a S.unitLabel
      rw [hn]; exact Nat.zero_lt_one))

include hχ in
/-- A negative transparent simple makes the actual centralizer of the positive
image equal to the entire ambient transparent center. -/
theorem centralizer_image_eq_of_negative_simple (a : ι)
    (ha : S.simpleObject a ∈ mugerCenter)
    (hneg : χ.hom.app (S.simpleObject a) = -𝟙 _) :
    centralizer (Set.range (inclusion χ).obj) = mugerCenter := by
  ext Z
  constructor
  · intro hZ
    apply (mem_mugerCenter_iff_simples S Z).mpr
    intro i
    obtain ⟨g, hg⟩ := simple_homogeneous χ hχ (S.simpleObject i)
    rcases Paper18.ZMod.two_eq_zero_or_one g with rfl | rfl
    · exact hZ _ ⟨⟨S.simpleObject i, hg⟩, rfl⟩
    · have ha1 : Homogeneous χ 1 (S.simpleObject a) := by
        simpa [Homogeneous] using hneg
      have hp : positiveProperty χ (S.simpleObject a ⊗ S.simpleObject i) := by
        simpa [positiveProperty, show (1 : ZMod 2) + 1 = 0 from by decide] using
          homogeneous_tensor χ ha1 hg
      have hc : Centralizes Z (S.simpleObject a ⊗ S.simpleObject i) :=
        hZ _ ⟨⟨_, hp⟩, rfl⟩
      have hd : S.simpleObject (S.dualLabel a) ∈ mugerCenter :=
        S.property_dualLabel (centralizerProperty (Set.univ : Set C)) a ha
      have hdc : Centralizes Z (S.simpleObject (S.dualLabel a)) :=
        (hd Z (Set.mem_univ _)).symm
      have htotal := hdc.tensor_right hc
      have hassoc : Centralizes Z
          ((S.simpleObject (S.dualLabel a) ⊗ S.simpleObject a) ⊗ S.simpleObject i) :=
        (centralizes_iso_right (α_ _ _ _)).mpr htotal
      let r : Retract (S.simpleObject i)
          ((S.simpleObject (S.dualLabel a) ⊗ S.simpleObject a) ⊗ S.simpleObject i) :=
        (Retract.ofIso (λ_ (S.simpleObject i)).symm).trans
          ((unitRetractDualTensor S a).map (tensorRight (S.simpleObject i)))
      exact hassoc.of_retract_right r
  · intro hZ Y _
    exact hZ Y (Set.mem_univ _)

include S hχ in
/-- Nontriviality on the ambient center identifies the actual ambient
centralizer of the positive image. -/
theorem centralizer_image_eq_of_nontrivial_center (X : C)
    (hZ : X ∈ mugerCenter) (hX : χ.hom.app X ≠ 𝟙 X) :
    centralizer (Set.range (inclusion χ).obj) = mugerCenter := by
  obtain ⟨a, ha, hneg⟩ := negative_transparent_simple χ S hχ X hZ hX
  exact centralizer_image_eq_of_negative_simple χ S hχ a ha hneg

include S hχ in
/-- Nontriviality of the character on the actual ambient center identifies
the actual transparent center of its positive full fusion subcategory. -/
theorem transparent_iff_ambient_of_nontrivial_center (X : C)
    (hZ : X ∈ mugerCenter) (hX : χ.hom.app X ≠ 𝟙 X) (Z : Positive χ) :
    Z ∈ mugerCenter ↔ Z.obj ∈ mugerCenter := by
  rw [← centralizer_image_eq_of_nontrivial_center χ S hχ X hZ hX]
  constructor
  · intro h Y hY
    obtain ⟨Y, rfl⟩ := hY
    exact (h Y (Set.mem_univ _)).map (inclusion χ)
  · intro h Y _
    exact (centralizes_map_iff (inclusion χ) Z Y).mp (h _ ⟨Y, rfl⟩)

end Paper18.Category.SignKernel

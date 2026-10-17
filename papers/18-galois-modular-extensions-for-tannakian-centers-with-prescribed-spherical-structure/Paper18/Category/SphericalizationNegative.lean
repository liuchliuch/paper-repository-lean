import Paper18.Category.SphericalizationFusion
import Paper18.Category.PivotalDimension
import Paper18.Category.Braided
import Paper18.Category.InvertibleObjects

/-!
# The canonical negative transparent object of sphericalization

This is the actual tensor unit of the original category, equipped with the
negative of the canonical double-dual identification. Its square equation,
transparency, order two, simplicity and negative pivotal dimension are proved
from the constructed category.
-/
noncomputable section
universe v u w
namespace Paper18.Category
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
namespace Sphericalized

/-- The negative canonical identification of the actual ambient unit. -/
def negativeUnitIso : 𝟙_ C ≅ (doubleDualFunctor C).obj (𝟙_ C) where
  hom := -ε (doubleDualFunctor C)
  inv := -η (doubleDualFunctor C)
  hom_inv_id := by
    simp only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, ε_η]
  inv_hom_id := by
    simp only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, η_ε]

/-- The canonical actual negative object in braided sphericalization. -/
def negativeGenerator : Sphericalized C :=
  ⟨⟨𝟙_ C, negativeUnitIso⟩, by
    change (-ε (doubleDualFunctor C)) ≫
      (doubleDualFunctor C).map (-ε (doubleDualFunctor C)) =
        (braidedFourDualIso (𝟙_ C)).hom
    have h := radfordSquareProperty_unit (C := C)
    change ε (doubleDualFunctor C) ≫ (doubleDualFunctor C).map (ε (doubleDualFunctor C)) =
      (braidedFourDualIso (𝟙_ C)).hom at h
    simpa only [Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg] using h⟩

@[simp] lemma negativeGenerator_obj : (negativeGenerator (C := C)).obj.obj = 𝟙_ C := rfl
@[simp] lemma negativeGenerator_phi : (negativeGenerator (C := C)).obj.phi.hom =
    -ε (doubleDualFunctor C) := rfl

/-- The canonical negative object centralizes every actual square object. -/
lemma negativeGenerator_centralizes (Y : Sphericalized C) :
    Centralizes (negativeGenerator (C := C)) Y := by
  apply (centralizes_map_iff (forget (C := C)) negativeGenerator Y).mp
  change Centralizes (𝟙_ C) (forget.obj Y)
  exact centralizes_unit_left _

/-- Its tensor square is the actual tensor unit, via the ambient unitor. -/
def negativeGeneratorSquareIso :
    negativeGenerator (C := C) ⊗ negativeGenerator ≅ 𝟙_ (Sphericalized C) :=
  radfordSquareProperty.isoMk (Pivotalized.mkIso (λ_ (𝟙_ C)) (by
    have h := (Pivotalized.leftUnitor (𝟙_ (Pivotalized C))).hom.comm
    change (λ_ (𝟙_ C)).hom ≫ ε (doubleDualFunctor C) =
      ((ε (doubleDualFunctor C) ⊗ₘ ε (doubleDualFunctor C)) ≫
        μ (doubleDualFunctor C) (𝟙_ C) (𝟙_ C)) ≫
          (doubleDualFunctor C).map (λ_ (𝟙_ C)).hom at h
    change (λ_ (𝟙_ C)).hom ≫ ε (doubleDualFunctor C) =
      (((-ε (doubleDualFunctor C)) ⊗ₘ (-ε (doubleDualFunctor C))) ≫
        μ (doubleDualFunctor C) (𝟙_ C) (𝟙_ C)) ≫
          (doubleDualFunctor C).map (λ_ (𝟙_ C)).hom
    have hn : (-ε (doubleDualFunctor C) ⊗ₘ -ε (doubleDualFunctor C)) =
        (ε (doubleDualFunctor C) ⊗ₘ ε (doubleDualFunctor C)) := by
      simp only [tensorHom_def]
      change (tensorRight (𝟙_ C)).map (-ε (doubleDualFunctor C)) ≫
        (tensorLeft ((doubleDualFunctor C).obj (𝟙_ C))).map (-ε (doubleDualFunctor C)) =
        (tensorRight (𝟙_ C)).map (ε (doubleDualFunctor C)) ≫
          (tensorLeft ((doubleDualFunctor C).obj (𝟙_ C))).map (ε (doubleDualFunctor C))
      simp only [Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
    rw [hn]
    exact h))

/-- Actual two-sided tensor-inverse data for the canonical negative object. -/
def negativeGeneratorTensorInverse : TensorInverse (negativeGenerator (C := C)) where
  inverse := negativeGenerator
  left := negativeGeneratorSquareIso
  right := negativeGeneratorSquareIso

/-- Its actual self-braiding is trivial: the canonical object is bosonic. -/
lemma negativeGenerator_selfBraiding :
    (β_ (negativeGenerator (C := C)) negativeGenerator).hom =
      𝟙 (negativeGenerator ⊗ negativeGenerator) := by
  apply (forget (C := C)).map_injective
  change (β_ (𝟙_ C) (𝟙_ C)).hom = 𝟙 ((𝟙_ C) ⊗ (𝟙_ C))
  rw [braiding_tensorUnit_left, unitors_equal, Iso.hom_inv_id]

/-- Negating the actual unit's chosen pivotal identification negates its
actual pivotal dimension. -/
lemma negativeGenerator_rightDimension :
    (pivotalStructure (C := C)).rightDimension negativeGenerator =
      -(pivotalStructure (C := C)).rightDimension (𝟙_ (Sphericalized C)) := by
  apply (forget (C := C)).map_injective
  change forget.map (pivotalStructure.rightTrace (𝟙 negativeGenerator)) =
    forget.map (-pivotalStructure.rightTrace (𝟙 (𝟙_ (Sphericalized C))))
  rw [Functor.map_neg, rightTrace_forget, rightTrace_forget]
  change η_ (𝟙_ C) (dual C (𝟙_ C)) ≫
      (𝟙 (𝟙_ C)) ▷ dual C (𝟙_ C) ≫ (-ε (doubleDualFunctor C)) ▷ dual C (𝟙_ C) ≫
        ε_ (dual C (𝟙_ C)) (dual C (dual C (𝟙_ C))) =
    -(η_ (𝟙_ C) (dual C (𝟙_ C)) ≫
      (𝟙 (𝟙_ C)) ▷ dual C (𝟙_ C) ≫ ε (doubleDualFunctor C) ▷ dual C (𝟙_ C) ≫
        ε_ (dual C (𝟙_ C)) (dual C (dual C (𝟙_ C))))
  have hn : (-ε (doubleDualFunctor C)) ▷ dual C (𝟙_ C) =
      -(ε (doubleDualFunctor C) ▷ dual C (𝟙_ C)) :=
    (tensorRight (dual C (𝟙_ C))).map_neg
  rw [hn]
  simp only [id_whiskerRight, id_comp, Preadditive.neg_comp, Preadditive.comp_neg]

section Fusion
variable [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- The canonical negative object is actually simple. -/
instance negativeGenerator_simple : Simple (negativeGenerator (C := C)) := by
  letI : Simple (toEquivariant.obj (negativeGenerator (C := C))).obj := by
    change Simple (𝟙_ C)
    infer_instance
  letI : Simple (toEquivariant.obj (negativeGenerator (C := C))) :=
    (sphericalizationAction C).simple_of_underlying_simple _
  exact simple_of_equivariant _

include S in
/-- The extracted categorical pivotal dimension is exactly minus one. -/
lemma negativeGenerator_rightDim :
    (pivotalStructure (C := C)).rightDim negativeGenerator = -1 := by
  dsimp only [PivotalStructure.rightDim]
  rw [negativeGenerator_rightDimension, map_neg]
  change -(pivotalStructure (C := C)).rightDim (𝟙_ (Sphericalized C)) = -1
  rw [PivotalStructure.rightDim_unit pivotalStructure (skeleton S)]

include S in
/-- The actual negative generator is distinct from the tensor unit. -/
lemma negativeGenerator_not_iso_unit :
    ¬ Nonempty (negativeGenerator (C := C) ≅ 𝟙_ (Sphericalized C)) := by
  rintro ⟨e⟩
  have h := (pivotalStructure (C := C)).rightDim_iso e
  rw [negativeGenerator_rightDim S,
    PivotalStructure.rightDim_unit pivotalStructure (skeleton S)] at h
  norm_num at h

end Fusion
end Sphericalized
end Paper18.Category

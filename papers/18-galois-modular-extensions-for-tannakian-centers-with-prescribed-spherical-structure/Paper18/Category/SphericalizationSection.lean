import Paper18.Category.SphericalizationFusion
import Paper18.Category.SphericalizationTraceSeparation

/-!
# A prescribed spherical structure has an actual section into sphericalization

The original category is not assumed pivotal in constructing sphericalization.
When it is supplied with a prescribed spherical structure, its actual objects
and morphisms lift fully faithfully, with all tensor, braiding and trace
compatibility proved below.
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
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (J : PivotalStructure C) (hJ : J.Spherical)
namespace Sphericalized

/-- The actual lift uses exactly the prescribed pivotal identification. -/
def sectionFunctor : C ⥤ Sphericalized C where
  obj X := ⟨⟨X, J.j.app X⟩, J.radfordSquare_of_spherical S hJ X⟩
  map f := ⟨f, J.j.hom.naturality f⟩
  map_id _ := rfl
  map_comp _ _ := rfl

instance section_faithful : (sectionFunctor S J hJ).Faithful where
  map_injective h := congrArg Pivotalized.Hom.hom h

instance section_full : (sectionFunctor S J hJ).Full where
  map_surjective f := ⟨f.hom, Pivotalized.Hom.ext rfl⟩

instance section_additive : (sectionFunctor S J hJ).Additive where
  map_add := by intros; rfl
instance section_linear : (sectionFunctor S J hJ).Linear ℂ where
  map_smul _ _ := rfl

/-- The tensor unit is identified by the actual identity map. -/
def sectionUnitIso : 𝟙_ (Sphericalized C) ≅ (sectionFunctor S J hJ).obj (𝟙_ C) :=
  radfordSquareProperty.isoMk (Pivotalized.mkIso (Iso.refl (𝟙_ C)) (by
    change 𝟙 (𝟙_ C) ≫ J.j.hom.app (𝟙_ C) =
      ε (doubleDualFunctor C) ≫ (doubleDualFunctor C).map (𝟙 (𝟙_ C))
    rw [id_comp, CategoryTheory.Functor.map_id, comp_id,
      J.unit, canonicalDoubleDual_unit]))

/-- The tensor comparison is the actual identity on the original tensor
product, and its commutation is precisely prescribed pivotal coherence. -/
def sectionTensorIso (X Y : C) :
    (sectionFunctor S J hJ).obj X ⊗ (sectionFunctor S J hJ).obj Y ≅
      (sectionFunctor S J hJ).obj (X ⊗ Y) :=
  radfordSquareProperty.isoMk (Pivotalized.mkIso (Iso.refl (X ⊗ Y)) (by
    change 𝟙 (X ⊗ Y) ≫ J.j.hom.app (X ⊗ Y) =
      ((J.j.hom.app X ⊗ₘ J.j.hom.app Y) ≫ μ (doubleDualFunctor C) X Y) ≫
        (doubleDualFunctor C).map (𝟙 (X ⊗ Y))
    rw [id_comp, CategoryTheory.Functor.map_id, comp_id,
      J.tensor, canonicalDoubleDual_tensor]))

/-- All strong monoidal functor coherence equations are actual ambient
coherence equations, reflected by the faithful forgetful functor. -/
def sectionCoreMonoidal : (sectionFunctor S J hJ).CoreMonoidal where
  εIso := sectionUnitIso S J hJ
  μIso := sectionTensorIso S J hJ
  μIso_hom_natural_left f X' := by
    apply Pivotalized.Hom.ext
    change (f ⊗ₘ 𝟙 X') ≫ 𝟙 _ = 𝟙 _ ≫ f ▷ X'
    simp
  μIso_hom_natural_right X' f := by
    apply Pivotalized.Hom.ext
    change (𝟙 X' ⊗ₘ f) ≫ 𝟙 _ = 𝟙 _ ≫ X' ◁ f
    simp
  associativity X Y Z := by
    apply Pivotalized.Hom.ext
    change (𝟙 (X ⊗ Y) ⊗ₘ 𝟙 Z) ≫ 𝟙 _ ≫ (α_ X Y Z).hom =
      (α_ X Y Z).hom ≫ (𝟙 X ⊗ₘ 𝟙 (Y ⊗ Z)) ≫ 𝟙 _
    simp
  left_unitality X := by
    apply Pivotalized.Hom.ext
    change (λ_ X).hom = (𝟙 (𝟙_ C) ⊗ₘ 𝟙 X) ≫ 𝟙 _ ≫ (λ_ X).hom
    simp
  right_unitality X := by
    apply Pivotalized.Hom.ext
    change (ρ_ X).hom = (𝟙 X ⊗ₘ 𝟙 (𝟙_ C)) ≫ 𝟙 _ ≫ (ρ_ X).hom
    simp

instance section_monoidal : (sectionFunctor S J hJ).Monoidal :=
  (sectionCoreMonoidal S J hJ).toMonoidal

instance section_braided : (sectionFunctor S J hJ).Braided where
  braided X Y := by
    apply Pivotalized.Hom.ext
    change 𝟙 (X ⊗ Y) ≫ (β_ X Y).hom = (β_ X Y).hom ≫ 𝟙 (Y ⊗ X)
    simp

/-- Forgetting the prescribed section gives the actual identity functor. -/
lemma section_comp_forget : sectionFunctor S J hJ ⋙ forget = 𝟭 C := rfl

/-- The actual right trace on the lifted object is the prescribed original
right trace, under the identity identification of the ambient unit. -/
lemma section_rightTrace {X : C} (f : X ⟶ X) :
    forget.map (pivotalStructure.rightTrace ((sectionFunctor S J hJ).map f)) =
      J.rightTrace f := by
  rw [rightTrace_forget]
  rfl

/-- Forgetting a chosen right mate in the square category gives the actual
chosen ambient mate. -/
lemma forget_dualMap {X Y : Sphericalized C} (f : X ⟶ Y) :
    forget.map (dualMap (Sphericalized C) f) = dualMap C (forget.map f) := by
  change (dualMap (Pivotalized C) f).hom = dualMap C f.hom
  exact Pivotalized.dualMap_hom f

/-- The section's canonical dual comparison is the ambient identity,
derived from its actual evaluation compatibility. -/
lemma section_dualComparison_hom (X : C) :
    forget.map (dualComparison (sectionFunctor S J hJ) X).hom = 𝟙 (dual C X) := by
  apply pairing_hom_ext (inferInstanceAs (ExactPairing X (dual C X)))
  have hc := dualComparison_evaluation (sectionFunctor S J hJ) X
  have hh := congrArg (fun t => forget.map t) hc
  change ((forget.map (dualComparison (sectionFunctor S J hJ) X).hom) ⊗ₘ 𝟙 X) ≫
      ε_ X (dual C X) = 𝟙 _ ≫ ε_ X (dual C X) ≫ 𝟙 _ at hh
  dsimp only [dual] at hh ⊢
  have hh' : forget.map (dualComparison (sectionFunctor S J hJ) X).hom ▷ X ≫
      ε_ X (dual C X) = ε_ X (dual C X) := by
    simpa only [tensorHom_id, Category.id_comp, Category.comp_id] using hh
  have hi : (𝟙 (dual C X)) ▷ X ≫ ε_ X (dual C X) = ε_ X (dual C X) :=
    (congrArg (fun t => t ≫ ε_ X (dual C X))
      (MonoidalCategory.id_whiskerRight (dual C X) X)).trans (Category.id_comp _)
  exact hh'.trans hi.symm

lemma section_dualComparison_inv (X : C) :
    forget.map (dualComparison (sectionFunctor S J hJ) X).inv = 𝟙 (dual C X) := by
  have hc := congrArg (fun t => forget.map t)
    (dualComparison (sectionFunctor S J hJ) X).hom_inv_id
  dsimp only at hc
  rw [Functor.map_comp, section_dualComparison_hom, CategoryTheory.Functor.map_id] at hc
  exact (Category.id_comp _).symm.trans hc

lemma section_doubleDualComparison_hom (X : C) :
    forget.map (doubleDualComparison (sectionFunctor S J hJ) X).hom =
      𝟙 ((doubleDualFunctor C).obj X) := by
  dsimp only [doubleDualComparison, Iso.trans_hom, Iso.symm_hom, dualMapIso]
  rw [Functor.map_comp, section_dualComparison_hom, forget_dualMap,
    section_dualComparison_inv]
  change 𝟙 (dual C (dual C X)) ≫ dualMap C (𝟙 (dual C X)) = 𝟙 (dual C (dual C X))
  have hid : dualMap C (𝟙 (dual C X)) = 𝟙 (dual C (dual C X)) := rightAdjointMate_id
  rw [hid]
  exact Category.id_comp (𝟙 (dual C (dual C X)))

/-- The section preserves the prescribed actual pivotal structure via the
canonical double-dual comparison, rather than by extra preservation data. -/
lemma section_preservesPivotal :
    PreservesPivotal (sectionFunctor S J hJ) J (pivotalStructure (C := C)) := by
  intro X
  apply (forget (C := C)).map_injective
  rw [Functor.map_comp, section_doubleDualComparison_hom]
  change J.j.hom.app X ≫ 𝟙 ((doubleDualFunctor C).obj X) = J.j.hom.app X
  exact Category.comp_id _

end Sphericalized
end Paper18.Category

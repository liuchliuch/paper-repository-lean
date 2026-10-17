import Paper18.Category.FixedBoundaryDescentFullyFaithful
import Paper18.Category.EquivariantMonoidal

/-! # The actual strong tensor comparison for arbitrary regular descent -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators MonObj Obj
universe v u
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [CategoryTheory.Limits.HasCoequalizers C]
  {G : Type} [Group G] [Fintype G]
  (F : FDRep ℂ G ⥤ C) [F.Braided] [F.Additive] [F.Linear ℂ]
open RelativeTensor

/-- Maps from a genuinely translated free module are detected on generators. -/
theorem translatedFree_hom_ext {X : C} {M : Modules F}
    {g : G} {f h : (moduleTranslation F g).obj ((regularFree F).obj X) ⟶ M}
    (e : RelativeTensor.freeUnit X ≫ f.hom = RelativeTensor.freeUnit X ≫ h.hom) : f = h := by
  apply (cancel_epi (freeEquivariantIso F X g).inv).mp
  apply RelativeTensor.free_hom_ext
  change RelativeTensor.freeUnit X ≫ (freeEquivariantIso F X g).inv.hom ≫ f.hom =
    RelativeTensor.freeUnit X ≫ (freeEquivariantIso F X g).inv.hom ≫ h.hom
  rw [freeEquivariantIso_inv_hom, freeUnit_translation_assoc, freeUnit_translation_assoc]
  exact e

/-- The actual unit comparison is equivariant by naturality of the
ordinary right unitor with respect to regular translation. -/
def descentUnitIso :
    (𝟙_ (regularAction F).Equivariant) ≅ (descentComparison F).obj (𝟙_ C) :=
  WeakAction.Equivariant.mkIso (regularAction F)
    (freeUnitIso (A := (regularAlgebra F))) (by
      intro g
      apply Mod_.Hom.ext
      change (freeUnitIso (A := (regularAlgebra F))).hom.hom ≫ ((regularTranslation F) g ▷ (𝟙_ C)) =
        (Functor.OplaxMonoidal.η ((moduleTranslation F) g)).hom ≫
          (freeUnitIso (A := (regularAlgebra F))).hom.hom
      rw [(moduleTranslation_η_hom F)]
      exact (rightUnitor_inv_naturality ((regularTranslation F) g)).symm)

/-- The inverse actual free tensor comparison is equivariant, as is
checked on actual free generators before the balancing quotient. -/
def descentTensorInvIso (X Y : C) :
    (descentComparison F).obj (X ⊗ Y) ≅ (descentComparison F).obj X ⊗ (descentComparison F).obj Y :=
  WeakAction.Equivariant.mkIso (regularAction F)
    (freeTensorIso (A := (regularAlgebra F)) X Y).symm (by
      intro g
      apply (translatedFree_hom_ext F)
      change freeUnit (X ⊗ Y) ≫ (freeTensorIso X Y).inv.hom ≫
          (Functor.OplaxMonoidal.δ ((moduleTranslation F) g)
            (InternalModule.free (regularAlgebra F) X) (InternalModule.free (regularAlgebra F) Y)).hom ≫
          (((freeEquivariantIso F) X g).hom ⊗ₘ ((freeEquivariantIso F) Y g).hom).hom =
        freeUnit (X ⊗ Y) ≫ ((regularTranslation F) g ▷ (X ⊗ Y)) ≫ (freeTensorIso X Y).inv.hom
      rw [freeUnit_freeTensorIso_inv_assoc, (π_moduleTranslation_δ_assoc F), π_tensorHom]
      simp only [(freeEquivariantIso_hom F)]
      rw [tensorHom_comp_tensorHom_assoc, (freeUnit_translation F), (freeUnit_translation F),
        (freeUnit_translation_assoc F), freeUnit_freeTensorIso_inv]
      rfl)

/-- The actual tensor comparison of the descent comparison. -/
def descentTensorIso (X Y : C) :
    (descentComparison F).obj X ⊗ (descentComparison F).obj Y ≅ (descentComparison F).obj (X ⊗ Y) :=
  ((descentTensorInvIso F) X Y).symm

/-- The actual free tensor comparisons satisfy all monoidal functor
coherences after lifting to actual equivariant objects. -/
def descentComparisonCoreMonoidal : (descentComparison F).CoreMonoidal where
  εIso := (descentUnitIso F)
  μIso := (descentTensorIso F)
  μIso_hom_natural_left f Z := by
    apply WeakAction.Equivariant.Hom.ext
    change (InternalModule.freeMap f ⊗ₘ 𝟙 (InternalModule.free (regularAlgebra F) Z)) ≫
        (freeTensorIso _ Z).hom = (freeTensorIso _ Z).hom ≫ InternalModule.freeMap (f ▷ Z)
    rw [MonoidalCategory.tensorHom_id]
    simpa only [freeFunctor_μ_eq] using
      Functor.LaxMonoidal.μ_natural_left (InternalModule.freeFunctor (A := (regularAlgebra F))) f Z
  μIso_hom_natural_right Z f := by
    apply WeakAction.Equivariant.Hom.ext
    change (𝟙 (InternalModule.free (regularAlgebra F) Z) ⊗ₘ InternalModule.freeMap f) ≫
        (freeTensorIso Z _).hom = (freeTensorIso Z _).hom ≫ InternalModule.freeMap (Z ◁ f)
    rw [MonoidalCategory.id_tensorHom]
    simpa only [freeFunctor_μ_eq] using
      Functor.LaxMonoidal.μ_natural_right (InternalModule.freeFunctor (A := (regularAlgebra F))) Z f
  associativity X Y Z := by
    apply WeakAction.Equivariant.Hom.ext
    change ((freeTensorIso X Y).hom ⊗ₘ 𝟙 (InternalModule.free (regularAlgebra F) Z)) ≫
        (freeTensorIso (X ⊗ Y) Z).hom ≫ InternalModule.freeMap (α_ X Y Z).hom =
      (α_ (InternalModule.free (regularAlgebra F) X) (InternalModule.free (regularAlgebra F) Y)
        (InternalModule.free (regularAlgebra F) Z)).hom ≫
          (𝟙 (InternalModule.free (regularAlgebra F) X) ⊗ₘ (freeTensorIso Y Z).hom) ≫
            (freeTensorIso X (Y ⊗ Z)).hom
    rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
    simpa only [freeFunctor_μ_eq] using
      Functor.LaxMonoidal.associativity (InternalModule.freeFunctor (A := (regularAlgebra F))) X Y Z
  left_unitality X := by
    apply WeakAction.Equivariant.Hom.ext
    change (λ_ (InternalModule.free (regularAlgebra F) X)).hom =
      ((freeUnitIso (A := (regularAlgebra F))).hom ⊗ₘ 𝟙 (InternalModule.free (regularAlgebra F) X)) ≫
        (freeTensorIso (𝟙_ C) X).hom ≫ InternalModule.freeMap (λ_ X).hom
    rw [MonoidalCategory.tensorHom_id]
    simpa only [freeFunctor_ε_eq, freeFunctor_μ_eq] using
      Functor.LaxMonoidal.left_unitality (InternalModule.freeFunctor (A := (regularAlgebra F))) X
  right_unitality X := by
    apply WeakAction.Equivariant.Hom.ext
    change (ρ_ (InternalModule.free (regularAlgebra F) X)).hom =
      (𝟙 (InternalModule.free (regularAlgebra F) X) ⊗ₘ (freeUnitIso (A := (regularAlgebra F))).hom) ≫
        (freeTensorIso X (𝟙_ C)).hom ≫ InternalModule.freeMap (ρ_ X).hom
    rw [MonoidalCategory.id_tensorHom]
    simpa only [freeFunctor_ε_eq, freeFunctor_μ_eq] using
      Functor.LaxMonoidal.right_unitality (InternalModule.freeFunctor (A := (regularAlgebra F))) X

instance descentComparisonMonoidal : (descentComparison F).Monoidal :=
  (descentComparisonCoreMonoidal F).toMonoidal

@[simp]
theorem descentComparison_μ_hom (X Y : C) :
    (Functor.LaxMonoidal.μ (descentComparison F) X Y).hom =
      (freeTensorIso (A := (regularAlgebra F)) X Y).hom := rfl

@[simp]
theorem descentComparison_ε_hom :
    (Functor.LaxMonoidal.ε (descentComparison F)).hom =
      (freeUnitIso (A := (regularAlgebra F))).hom := rfl

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- Forgetting the actual descent equivariance recovers the original
actual free-module functor on objects and morphisms. -/
@[simp]
theorem descentComparison_comp_forget :
    (descentComparison F) ⋙ (regularAction F).forget = (regularFree F) := rfl


end Paper18.Category.FixedBoundary

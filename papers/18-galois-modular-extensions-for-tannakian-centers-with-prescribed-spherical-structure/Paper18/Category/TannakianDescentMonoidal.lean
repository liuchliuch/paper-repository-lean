import Paper18.Category.TannakianActionMonoidal

/-! # The actual braided tensor Tannakian descent comparison -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u
namespace Paper18.Category
open RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [HasCoequalizers C]
  {G : Type} [Group G] [Fintype G] (T : TannakianCenter C G)

/-- The actual unit comparison is equivariant by naturality of the
ordinary right unitor with respect to regular translation. -/
def TannakianCenter.descentUnitIso :
    (𝟙_ T.deequivariantAction.Equivariant) ≅ T.descentComparison.obj (𝟙_ C) :=
  WeakAction.Equivariant.mkIso T.deequivariantAction
    (freeUnitIso (A := T.regularAlgebra)) (by
      intro g
      apply Mod_.Hom.ext
      change (freeUnitIso (A := T.regularAlgebra)).hom.hom ≫ (T.regularTranslation g ▷ (𝟙_ C)) =
        (Functor.OplaxMonoidal.η (T.moduleTranslation g)).hom ≫
          (freeUnitIso (A := T.regularAlgebra)).hom.hom
      rw [T.moduleTranslation_η_hom]
      exact (rightUnitor_inv_naturality (T.regularTranslation g)).symm)

/-- The inverse actual free tensor comparison is equivariant, as is
checked on actual free generators before the balancing quotient. -/
def TannakianCenter.descentTensorInvIso (X Y : C) :
    T.descentComparison.obj (X ⊗ Y) ≅ T.descentComparison.obj X ⊗ T.descentComparison.obj Y :=
  WeakAction.Equivariant.mkIso T.deequivariantAction
    (freeTensorIso (A := T.regularAlgebra) X Y).symm (by
      intro g
      apply T.translatedFree_hom_ext
      change freeUnit (X ⊗ Y) ≫ (freeTensorIso X Y).inv.hom ≫
          (Functor.OplaxMonoidal.δ (T.moduleTranslation g)
            (InternalModule.free T.regularAlgebra X) (InternalModule.free T.regularAlgebra Y)).hom ≫
          ((T.freeEquivariantIso X g).hom ⊗ₘ (T.freeEquivariantIso Y g).hom).hom =
        freeUnit (X ⊗ Y) ≫ (T.regularTranslation g ▷ (X ⊗ Y)) ≫ (freeTensorIso X Y).inv.hom
      rw [freeUnit_freeTensorIso_inv_assoc, T.π_moduleTranslation_δ_assoc, π_tensorHom]
      simp only [T.freeEquivariantIso_hom]
      rw [tensorHom_comp_tensorHom_assoc, T.freeUnit_translation, T.freeUnit_translation,
        T.freeUnit_translation_assoc, freeUnit_freeTensorIso_inv]
      rfl)

/-- The actual tensor comparison of the descent comparison. -/
def TannakianCenter.descentTensorIso (X Y : C) :
    T.descentComparison.obj X ⊗ T.descentComparison.obj Y ≅ T.descentComparison.obj (X ⊗ Y) :=
  (T.descentTensorInvIso X Y).symm

/-- The actual free tensor comparisons satisfy all monoidal functor
coherences after lifting to actual equivariant objects. -/
def TannakianCenter.descentComparisonCoreMonoidal : T.descentComparison.CoreMonoidal where
  εIso := T.descentUnitIso
  μIso := T.descentTensorIso
  μIso_hom_natural_left f Z := by
    apply WeakAction.Equivariant.Hom.ext
    change (InternalModule.freeMap f ⊗ₘ 𝟙 (InternalModule.free T.regularAlgebra Z)) ≫
        (freeTensorIso _ Z).hom = (freeTensorIso _ Z).hom ≫ InternalModule.freeMap (f ▷ Z)
    rw [MonoidalCategory.tensorHom_id]
    simpa only [freeFunctor_μ_eq] using
      Functor.LaxMonoidal.μ_natural_left (InternalModule.freeFunctor (A := T.regularAlgebra)) f Z
  μIso_hom_natural_right Z f := by
    apply WeakAction.Equivariant.Hom.ext
    change (𝟙 (InternalModule.free T.regularAlgebra Z) ⊗ₘ InternalModule.freeMap f) ≫
        (freeTensorIso Z _).hom = (freeTensorIso Z _).hom ≫ InternalModule.freeMap (Z ◁ f)
    rw [MonoidalCategory.id_tensorHom]
    simpa only [freeFunctor_μ_eq] using
      Functor.LaxMonoidal.μ_natural_right (InternalModule.freeFunctor (A := T.regularAlgebra)) Z f
  associativity X Y Z := by
    apply WeakAction.Equivariant.Hom.ext
    change ((freeTensorIso X Y).hom ⊗ₘ 𝟙 (InternalModule.free T.regularAlgebra Z)) ≫
        (freeTensorIso (X ⊗ Y) Z).hom ≫ InternalModule.freeMap (α_ X Y Z).hom =
      (α_ (InternalModule.free T.regularAlgebra X) (InternalModule.free T.regularAlgebra Y)
        (InternalModule.free T.regularAlgebra Z)).hom ≫
          (𝟙 (InternalModule.free T.regularAlgebra X) ⊗ₘ (freeTensorIso Y Z).hom) ≫
            (freeTensorIso X (Y ⊗ Z)).hom
    rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
    simpa only [freeFunctor_μ_eq] using
      Functor.LaxMonoidal.associativity (InternalModule.freeFunctor (A := T.regularAlgebra)) X Y Z
  left_unitality X := by
    apply WeakAction.Equivariant.Hom.ext
    change (λ_ (InternalModule.free T.regularAlgebra X)).hom =
      ((freeUnitIso (A := T.regularAlgebra)).hom ⊗ₘ 𝟙 (InternalModule.free T.regularAlgebra X)) ≫
        (freeTensorIso (𝟙_ C) X).hom ≫ InternalModule.freeMap (λ_ X).hom
    rw [MonoidalCategory.tensorHom_id]
    simpa only [freeFunctor_ε_eq, freeFunctor_μ_eq] using
      Functor.LaxMonoidal.left_unitality (InternalModule.freeFunctor (A := T.regularAlgebra)) X
  right_unitality X := by
    apply WeakAction.Equivariant.Hom.ext
    change (ρ_ (InternalModule.free T.regularAlgebra X)).hom =
      (𝟙 (InternalModule.free T.regularAlgebra X) ⊗ₘ (freeUnitIso (A := T.regularAlgebra)).hom) ≫
        (freeTensorIso X (𝟙_ C)).hom ≫ InternalModule.freeMap (ρ_ X).hom
    rw [MonoidalCategory.id_tensorHom]
    simpa only [freeFunctor_ε_eq, freeFunctor_μ_eq] using
      Functor.LaxMonoidal.right_unitality (InternalModule.freeFunctor (A := T.regularAlgebra)) X

instance TannakianCenter.descentComparisonMonoidal : T.descentComparison.Monoidal :=
  T.descentComparisonCoreMonoidal.toMonoidal

@[simp]
theorem TannakianCenter.descentComparison_μ_hom (X Y : C) :
    (Functor.LaxMonoidal.μ T.descentComparison X Y).hom =
      (freeTensorIso (A := T.regularAlgebra) X Y).hom := rfl

@[simp]
theorem TannakianCenter.descentComparison_ε_hom :
    (Functor.LaxMonoidal.ε T.descentComparison).hom =
      (freeUnitIso (A := T.regularAlgebra)).hom := rfl

omit [RightRigidCategory C] [HasCoequalizers C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- Forgetting the actual descent equivariance recovers the original
actual free-module functor on objects and morphisms. -/
@[simp]
theorem TannakianCenter.descentComparison_comp_forget :
    T.descentComparison ⋙ T.deequivariantAction.forget = T.deequivariantFree := rfl

/-- The actual descent comparison preserves the original ambient braiding
and the proved descended equivariant braiding. -/
def TannakianCenter.descentComparisonBraided :
    letI := T.deequivariantBraided
    letI := T.deequivariantActionBraided
    T.descentComparison.Braided := by
  letI := T.deequivariantBraided
  letI := T.deequivariantActionBraided
  exact
    { toMonoidal := T.descentComparisonMonoidal
      braided X Y := by
        apply WeakAction.Equivariant.Hom.ext
        change (freeTensorIso X Y).hom ≫ InternalModule.freeMap (β_ X Y).hom =
          (β_ (InternalModule.free T.regularAlgebra X) (InternalModule.free T.regularAlgebra Y)).hom ≫
            (freeTensorIso Y X).hom
        letI := T.deequivariantFreeBraided
        simpa only [TannakianCenter.deequivariantFree, freeFunctor_μ_eq] using
          (Functor.LaxBraided.braided (F := T.deequivariantFree) X Y) }

end Paper18.Category

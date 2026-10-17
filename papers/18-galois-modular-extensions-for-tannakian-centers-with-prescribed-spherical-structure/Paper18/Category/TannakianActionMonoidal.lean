import Paper18.Category.TannakianDeequivariantFusion
import Paper18.Category.TannakianDescentEquivalence
import Paper18.Category.EquivariantBraided
import Paper18.Category.RelativeTensorRestriction

/-! # Tensor quotient formulas for the actual Tannakian translation action -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u
namespace Paper18.Category.RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C] {A : C} [MonObj A] [IsCommMonObj A]

/-- The actual tensor of module maps is induced by the ordinary tensor
of their underlying maps before the balancing quotient. -/
@[reassoc]
theorem π_tensorHom {M N P Q : Mod_ C A} (f : M ⟶ P) (g : N ⟶ Q) :
    π M N ≫ (f ⊗ₘ g).hom = (f.hom ⊗ₘ g.hom) ≫ π P Q := by
  rw [MonoidalCategory.tensorHom_def]
  change π M N ≫ (f ▷ N).hom ≫ (P ◁ g).hom = (f.hom ⊗ₘ g.hom) ≫ π P Q
  rw [π_whiskerRight_assoc, π_whiskerLeft]
  simp only [MonoidalCategory.tensorHom_def, Category.assoc]

end Paper18.Category.RelativeTensor

namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {G : Type} [Group G] [Fintype G] (T : TannakianCenter C G)

instance TannakianCenter.regularTranslationIsoIsMonHom (g : G) :
    IsMonHom (T.regularTranslationIso g).hom := T.regularTranslationIsMonHom g

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- Module maps from a translated free module are determined on its
actual free generators, using the proved translation isomorphism. -/
theorem TannakianCenter.translatedFree_hom_ext {X : C} {M : T.Deequivariantization}
    {g : G} {f h : (T.moduleTranslation g).obj (T.deequivariantFree.obj X) ⟶ M}
    (e : RelativeTensor.freeUnit X ≫ f.hom = RelativeTensor.freeUnit X ≫ h.hom) : f = h := by
  apply (cancel_epi (T.freeEquivariantIso X g).inv).mp
  apply RelativeTensor.free_hom_ext
  change RelativeTensor.freeUnit X ≫ (T.freeEquivariantIso X g).inv.hom ≫ f.hom =
    RelativeTensor.freeUnit X ≫ (T.freeEquivariantIso X g).inv.hom ≫ h.hom
  rw [T.freeEquivariantIso_inv_hom, T.freeUnit_translation_assoc, T.freeUnit_translation_assoc]
  exact e

end Paper18.Category

namespace Paper18.Category
open RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [HasCoequalizers C]
  {G : Type} [Group G] [Fintype G] (T : TannakianCenter C G)

instance TannakianCenter.moduleTranslationMonoidal (g : G) :
    (T.moduleTranslation g).Monoidal :=
  restrictionMonoidal (T.regularTranslationIso g⁻¹)

instance TannakianCenter.deequivariantActionMonoidalFunctors (g : G) :
    (T.deequivariantAction.ρ g).Monoidal := T.moduleTranslationMonoidal g

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
@[reassoc (attr := simp)]
theorem TannakianCenter.π_moduleTranslation_μ (g : G) (M N : T.Deequivariantization) :
    π ((T.moduleTranslation g).obj M) ((T.moduleTranslation g).obj N) ≫
      (Functor.LaxMonoidal.μ (T.moduleTranslation g) M N).hom = π M N :=
  π_restrictionTensorHom (T.regularTranslationIso g⁻¹) M N

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
@[simp]
theorem TannakianCenter.moduleTranslation_ε_hom (g : G) :
    (Functor.LaxMonoidal.ε (T.moduleTranslation g)).hom = T.regularTranslation g⁻¹ := rfl

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
@[simp]
theorem TannakianCenter.moduleTranslation_η_hom (g : G) :
    (Functor.OplaxMonoidal.η (T.moduleTranslation g)).hom = T.regularTranslation g := by
  let e := T.regularTranslationIso g
  letI : IsIso e.inv := e.isIso_inv
  apply (cancel_mono e.inv).mp
  have h := congrArg (fun f => f.hom) (Functor.Monoidal.η_ε (T.moduleTranslation g))
  change (Functor.OplaxMonoidal.η (T.moduleTranslation g)).hom ≫ e.inv = 𝟙 _ at h
  rw [h]
  exact e.hom_inv_id.symm

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
@[reassoc]
theorem TannakianCenter.π_moduleTranslation_δ (g : G) (M N : T.Deequivariantization) :
    π M N ≫ (Functor.OplaxMonoidal.δ (T.moduleTranslation g) M N).hom =
      π ((T.moduleTranslation g).obj M) ((T.moduleTranslation g).obj N) := by
  have h := congrArg (fun f => f.hom) (Functor.Monoidal.μ_δ (T.moduleTranslation g) M N)
  change (Functor.LaxMonoidal.μ (T.moduleTranslation g) M N).hom ≫
    (Functor.OplaxMonoidal.δ (T.moduleTranslation g) M N).hom = 𝟙 _ at h
  rw [← T.π_moduleTranslation_μ g M N, Category.assoc, h]
  erw [Category.comp_id]

instance TannakianCenter.moduleTranslationUnitMonoidal :
    NatTrans.IsMonoidal T.moduleTranslationUnit.hom where
  unit := by
    apply Mod_.Hom.ext
    change (Functor.LaxMonoidal.ε (T.moduleTranslation 1)).hom ≫ 𝟙 _ = 𝟙 _
    rw [T.moduleTranslation_ε_hom, inv_one, T.regularTranslation_one]
    erw [Category.id_comp]
    rfl
  tensor M N := by
    apply module_hom_ext
    change π ((T.moduleTranslation 1).obj M) ((T.moduleTranslation 1).obj N) ≫
        (Functor.LaxMonoidal.μ (T.moduleTranslation 1) M N).hom ≫ 𝟙 _ =
      π ((T.moduleTranslation 1).obj M) ((T.moduleTranslation 1).obj N) ≫
        (T.moduleTranslationUnit.hom.app M ⊗ₘ T.moduleTranslationUnit.hom.app N).hom ≫ 𝟙 _
    rw [T.π_moduleTranslation_μ_assoc, π_tensorHom_assoc]
    change π M N ≫ 𝟙 _ = (𝟙 M.X ⊗ₘ 𝟙 N.X) ≫ π M N ≫ 𝟙 _
    simp

instance TannakianCenter.moduleTranslationMulMonoidal (g h : G) :
    NatTrans.IsMonoidal (T.moduleTranslationMul g h).hom where
  unit := by
    simp only [Functor.LaxMonoidal.comp_ε, Category.assoc]
    apply Mod_.Hom.ext
    change (Functor.LaxMonoidal.ε (T.moduleTranslation g)).hom ≫
        (Functor.LaxMonoidal.ε (T.moduleTranslation h)).hom ≫ 𝟙 _ =
      (Functor.LaxMonoidal.ε (T.moduleTranslation (g * h))).hom
    rw [T.moduleTranslation_ε_hom, T.moduleTranslation_ε_hom,
      T.moduleTranslation_ε_hom, Category.comp_id, mul_inv_rev, T.regularTranslation_mul]
  tensor M N := by
    simp only [Functor.LaxMonoidal.comp_μ, Category.assoc]
    apply module_hom_ext
    change π ((T.moduleTranslation g).obj ((T.moduleTranslation h).obj M))
        ((T.moduleTranslation g).obj ((T.moduleTranslation h).obj N)) ≫
      (Functor.LaxMonoidal.μ (T.moduleTranslation g)
        ((T.moduleTranslation h).obj M) ((T.moduleTranslation h).obj N)).hom ≫
      (Functor.LaxMonoidal.μ (T.moduleTranslation h) M N).hom ≫ 𝟙 _ =
      π ((T.moduleTranslation g).obj ((T.moduleTranslation h).obj M))
        ((T.moduleTranslation g).obj ((T.moduleTranslation h).obj N)) ≫
      ((T.moduleTranslationMul g h).hom.app M ⊗ₘ
        (T.moduleTranslationMul g h).hom.app N).hom ≫
          (Functor.LaxMonoidal.μ (T.moduleTranslation (g * h)) M N).hom
    rw [T.π_moduleTranslation_μ_assoc, T.π_moduleTranslation_μ_assoc, π_tensorHom_assoc]
    change π M N ≫ 𝟙 _ = (𝟙 M.X ⊗ₘ 𝟙 N.X) ≫
      π ((T.moduleTranslation (g * h)).obj M) ((T.moduleTranslation (g * h)).obj N) ≫
        (Functor.LaxMonoidal.μ (T.moduleTranslation (g * h)) M N).hom
    rw [MonoidalCategory.id_tensorHom_id, Category.id_comp, T.π_moduleTranslation_μ]
    simp

instance TannakianCenter.deequivariantActionMonoidal : T.deequivariantAction.IsMonoidal where
  unit_monoidal := T.moduleTranslationUnitMonoidal
  mul_monoidal := T.moduleTranslationMulMonoidal

/-- Restriction by each regular algebra translation preserves the actual
descended braiding on the actual module category. -/
def TannakianCenter.moduleTranslationBraided (g : G) :
    letI := T.deequivariantBraided
    (T.moduleTranslation g).Braided :=
  restrictionBraidedOfTransparent (T.regularTranslationIso g⁻¹) T.regularAlgebra_transparent

/-- The actual weak Tannakian translation action is braided with its
proved monoidal coherence maps. -/
def TannakianCenter.deequivariantActionBraided :
    letI := T.deequivariantBraided
    T.deequivariantAction.IsBraided := by
  letI := T.deequivariantBraided
  exact
    { braided g M N := by
        letI := T.moduleTranslationBraided g
        exact Functor.LaxBraided.braided (F := T.moduleTranslation g) M N }

end Paper18.Category

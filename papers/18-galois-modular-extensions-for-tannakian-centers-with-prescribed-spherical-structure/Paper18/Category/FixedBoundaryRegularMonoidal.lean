import Paper18.Category.FixedBoundaryRegularAction
import Paper18.Category.TannakianActionMonoidal
import Paper18.Category.RelativeTensorRestriction

/-! # The genuine monoidal regular action without a transparency hypothesis -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C]
  {G : Type} [Group G] [Fintype G] (F : FDRep ℂ G ⥤ C) [F.Braided]

instance regularAlgebraCommMonObj : IsCommMonObj (regularAlgebra F) :=
  Functor.isCommMonObj_obj

/-- Actual algebra isomorphism induced by regular right translation. -/
def regularTranslationIso (g : G) : regularAlgebra F ≅ regularAlgebra F :=
  F.mapIso (Representation.rightTranslationIso g)

instance regularTranslationIsoIsMonHom (g : G) :
    IsMonHom (regularTranslationIso F g).hom := regularTranslationIsMonHom F g

end Paper18.Category.FixedBoundary

namespace Paper18.Category.FixedBoundary
open RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [HasCoequalizers C]
  {G : Type} [Group G] [Fintype G] (F : FDRep ℂ G ⥤ C) [F.Braided]

instance moduleTranslationMonoidal (g : G) :
    ((moduleTranslation F) g).Monoidal :=
  restrictionMonoidal ((regularTranslationIso F) g⁻¹)

instance regularActionMonoidalFunctors (g : G) :
    ((regularAction F).ρ g).Monoidal := (moduleTranslationMonoidal F) g

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
@[reassoc (attr := simp)]
theorem π_moduleTranslation_μ (g : G) (M N : (Modules F)) :
    π (((moduleTranslation F) g).obj M) (((moduleTranslation F) g).obj N) ≫
      (Functor.LaxMonoidal.μ ((moduleTranslation F) g) M N).hom = π M N :=
  π_restrictionTensorHom ((regularTranslationIso F) g⁻¹) M N

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
@[simp]
theorem moduleTranslation_ε_hom (g : G) :
    (Functor.LaxMonoidal.ε ((moduleTranslation F) g)).hom = (regularTranslation F) g⁻¹ := rfl

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
@[simp]
theorem moduleTranslation_η_hom (g : G) :
    (Functor.OplaxMonoidal.η ((moduleTranslation F) g)).hom = (regularTranslation F) g := by
  let e := (regularTranslationIso F) g
  letI : IsIso e.inv := e.isIso_inv
  apply (cancel_mono e.inv).mp
  have h := congrArg (fun f => f.hom) (Functor.Monoidal.η_ε ((moduleTranslation F) g))
  change (Functor.OplaxMonoidal.η ((moduleTranslation F) g)).hom ≫ e.inv = 𝟙 _ at h
  rw [h]
  exact e.hom_inv_id.symm

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
@[reassoc]
theorem π_moduleTranslation_δ (g : G) (M N : (Modules F)) :
    π M N ≫ (Functor.OplaxMonoidal.δ ((moduleTranslation F) g) M N).hom =
      π (((moduleTranslation F) g).obj M) (((moduleTranslation F) g).obj N) := by
  have h := congrArg (fun f => f.hom) (Functor.Monoidal.μ_δ ((moduleTranslation F) g) M N)
  change (Functor.LaxMonoidal.μ ((moduleTranslation F) g) M N).hom ≫
    (Functor.OplaxMonoidal.δ ((moduleTranslation F) g) M N).hom = 𝟙 _ at h
  rw [← (π_moduleTranslation_μ F) g M N, Category.assoc, h]
  erw [Category.comp_id]

instance moduleTranslationUnitMonoidal :
    NatTrans.IsMonoidal (moduleTranslationUnit F).hom where
  unit := by
    apply Mod_.Hom.ext
    change (Functor.LaxMonoidal.ε ((moduleTranslation F) 1)).hom ≫ 𝟙 _ = 𝟙 _
    rw [(moduleTranslation_ε_hom F), inv_one, (regularTranslation_one F)]
    erw [Category.id_comp]
    rfl
  tensor M N := by
    apply module_hom_ext
    change π (((moduleTranslation F) 1).obj M) (((moduleTranslation F) 1).obj N) ≫
        (Functor.LaxMonoidal.μ ((moduleTranslation F) 1) M N).hom ≫ 𝟙 _ =
      π (((moduleTranslation F) 1).obj M) (((moduleTranslation F) 1).obj N) ≫
        ((moduleTranslationUnit F).hom.app M ⊗ₘ (moduleTranslationUnit F).hom.app N).hom ≫ 𝟙 _
    rw [(π_moduleTranslation_μ_assoc F), π_tensorHom_assoc]
    change π M N ≫ 𝟙 _ = (𝟙 M.X ⊗ₘ 𝟙 N.X) ≫ π M N ≫ 𝟙 _
    simp

instance moduleTranslationMulMonoidal (g h : G) :
    NatTrans.IsMonoidal ((moduleTranslationMul F) g h).hom where
  unit := by
    simp only [Functor.LaxMonoidal.comp_ε, Category.assoc]
    apply Mod_.Hom.ext
    change (Functor.LaxMonoidal.ε ((moduleTranslation F) g)).hom ≫
        (Functor.LaxMonoidal.ε ((moduleTranslation F) h)).hom ≫ 𝟙 _ =
      (Functor.LaxMonoidal.ε ((moduleTranslation F) (g * h))).hom
    rw [(moduleTranslation_ε_hom F), (moduleTranslation_ε_hom F),
      (moduleTranslation_ε_hom F), Category.comp_id, mul_inv_rev, (regularTranslation_mul F)]
  tensor M N := by
    simp only [Functor.LaxMonoidal.comp_μ, Category.assoc]
    apply module_hom_ext
    change π (((moduleTranslation F) g).obj (((moduleTranslation F) h).obj M))
        (((moduleTranslation F) g).obj (((moduleTranslation F) h).obj N)) ≫
      (Functor.LaxMonoidal.μ ((moduleTranslation F) g)
        (((moduleTranslation F) h).obj M) (((moduleTranslation F) h).obj N)).hom ≫
      (Functor.LaxMonoidal.μ ((moduleTranslation F) h) M N).hom ≫ 𝟙 _ =
      π (((moduleTranslation F) g).obj (((moduleTranslation F) h).obj M))
        (((moduleTranslation F) g).obj (((moduleTranslation F) h).obj N)) ≫
      (((moduleTranslationMul F) g h).hom.app M ⊗ₘ
        ((moduleTranslationMul F) g h).hom.app N).hom ≫
          (Functor.LaxMonoidal.μ ((moduleTranslation F) (g * h)) M N).hom
    rw [(π_moduleTranslation_μ_assoc F), (π_moduleTranslation_μ_assoc F), π_tensorHom_assoc]
    change π M N ≫ 𝟙 _ = (𝟙 M.X ⊗ₘ 𝟙 N.X) ≫
      π (((moduleTranslation F) (g * h)).obj M) (((moduleTranslation F) (g * h)).obj N) ≫
        (Functor.LaxMonoidal.μ ((moduleTranslation F) (g * h)) M N).hom
    rw [MonoidalCategory.id_tensorHom_id, Category.id_comp, (π_moduleTranslation_μ F)]
    simp

instance regularActionMonoidal : (regularAction F).IsMonoidal where
  unit_monoidal := (moduleTranslationUnitMonoidal F)
  mul_monoidal := (moduleTranslationMulMonoidal F)


end Paper18.Category.FixedBoundary

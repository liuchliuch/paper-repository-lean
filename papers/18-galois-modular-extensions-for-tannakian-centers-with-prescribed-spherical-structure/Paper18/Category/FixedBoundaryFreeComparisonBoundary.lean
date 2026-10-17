import Paper18.Category.FixedBoundaryFreeComparison
import Paper18.Category.FixedBoundaryNeutral

/-! # The free comparison retains every specified boundary component

Naturality at the actual free tensorator and monoidality of the original
boundary alpha identify the composite free comparison on boundary objects.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N]
  [RightRigidCategory N] [Limits.HasCoequalizers N]
  {i : A ⥤ N} [i.Braided] (P : BoundaryAutoequivalence i) (R : A)
  [MonObj R] [IsCommMonObj R]
  (β : P.moduleFunctor R ≅ 𝟭 (Mod_ N (i.obj R)))
  (hβ : ∀ M : Mod_ A R,
    (β.hom.app ((InternalModule.mapModules i).obj M)).hom = P.boundary.hom.app M.X)

include hβ in
/-- On every original boundary object, the actual free comparison followed
by beta is precisely the free extension of the specified alpha component. -/
theorem BoundaryAutoequivalence.moduleFreeIso_boundary (X : A) :
    (P.moduleFreeIso R (i.obj X)).hom ≫ β.hom.app (InternalModule.free (i.obj R) (i.obj X)) =
      InternalModule.freeMap (A := i.obj R) (P.boundary.hom.app X) := by
  let q := InternalModule.mapModuleFreeIso i (A := R) X
  apply (cancel_mono q.hom).mp
  rw [Category.assoc]
  have hn := β.hom.naturality q.hom
  change (P.moduleFunctor R).map q.hom ≫ β.hom.app _ = β.hom.app _ ≫ q.hom at hn
  erw [← hn]
  apply Mod_.Hom.ext
  change (P.moduleFreeIso R (i.obj X)).hom.hom ≫ P.functor.map q.hom.hom ≫
      (β.hom.app ((InternalModule.mapModules i).obj (InternalModule.free R X))).hom =
    (i.obj R ◁ P.boundary.hom.app X) ≫ q.hom.hom
  rw [hβ, P.moduleFreeIso_hom]
  change ((P.boundaryAlgebraIso R).inv ▷ P.functor.obj (i.obj X) ≫
      Functor.LaxMonoidal.μ P.functor (i.obj R) (i.obj X)) ≫
        P.functor.map (Functor.LaxMonoidal.μ i R X) ≫ P.boundary.hom.app (R ⊗ X) =
    (i.obj R ◁ P.boundary.hom.app X) ≫ Functor.LaxMonoidal.μ i R X
  have h := NatTrans.IsMonoidal.tensor (τ := P.boundary.hom) R X
  simp only [Functor.LaxMonoidal.comp_μ] at h
  simp only [Category.assoc]
  rw [← Category.assoc (Functor.LaxMonoidal.μ P.functor (i.obj R) (i.obj X)), h]
  rw [MonoidalCategory.tensorHom_def]
  simp only [Category.assoc]
  rw [← P.boundaryAlgebraIso_hom R]
  change ((P.boundaryAlgebraIso R).inv ▷ P.functor.obj (i.obj X)) ≫
      ((P.boundaryAlgebraIso R).hom ▷ P.functor.obj (i.obj X)) ≫
        (i.obj R ◁ P.boundary.hom.app X) ≫ Functor.LaxMonoidal.μ i R X = _
  rw [← comp_whiskerRight_assoc]
  rw [Iso.inv_hom_id, id_whiskerRight, Category.id_comp]

end Paper18.Category

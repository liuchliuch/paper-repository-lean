import Paper18.Category.FixedBoundaryModuleFunctorMonoidal
import Paper18.Category.TannakianActionMonoidal

/-! # Actual monoidal transformations of fixed-boundary module functors -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category
open RelativeTensor
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N]
  [RightRigidCategory N] [HasCoequalizers N]
  {i : A ⥤ N} [i.Braided] {P Q : BoundaryAutoequivalence i} (R : A)
  [MonObj R] [IsCommMonObj R]

/-- The specified fixed-boundary equality supplies precisely the unit
condition, while ambient monoidality descends through the actual balancing
quotients for the tensor condition. -/
instance BoundaryIso.moduleNatIsoMonoidal (f : BoundaryIso i P Q) :
    NatTrans.IsMonoidal (f.moduleNatIso R).hom where
  unit := by
    apply Mod_.Hom.ext
    change (Functor.LaxMonoidal.ε (P.moduleFunctor R)).hom ≫ f.iso.hom.app (i.obj R) =
      (Functor.LaxMonoidal.ε (Q.moduleFunctor R)).hom
    rw [P.moduleFunctor_ε_hom, Q.moduleFunctor_ε_hom]
    exact f.inverse_algebra R
  tensor M N := by
    apply module_hom_ext
    change π ((P.moduleFunctor R).obj M) ((P.moduleFunctor R).obj N) ≫
        (Functor.LaxMonoidal.μ (P.moduleFunctor R) M N).hom ≫ f.iso.hom.app (M ⊗ N).X =
      π ((P.moduleFunctor R).obj M) ((P.moduleFunctor R).obj N) ≫
        ((f.moduleNatIso R).hom.app M ⊗ₘ (f.moduleNatIso R).hom.app N).hom ≫
        (Functor.LaxMonoidal.μ (Q.moduleFunctor R) M N).hom
    rw [P.π_moduleFunctor_μ_assoc, π_tensorHom_assoc, Q.π_moduleFunctor_μ]
    have hn := f.iso.hom.naturality (π M N)
    change P.functor.map (π M N) ≫ f.iso.hom.app (M ⊗ N).X =
      f.iso.hom.app (M.X ⊗ N.X) ≫ Q.functor.map (π M N) at hn
    rw [hn, ← Category.assoc, NatTrans.IsMonoidal.tensor]
    simp only [Category.assoc]
    rfl

end Paper18.Category

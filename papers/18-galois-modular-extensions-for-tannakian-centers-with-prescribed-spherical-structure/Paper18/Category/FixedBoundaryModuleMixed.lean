import Paper18.Category.FixedBoundaryLocalCrossing
import Paper18.Category.FixedBoundaryTensoratorBasic

/-! # The genuine local crossing supplies the other mixed tensor equation

Only the actual central crossing of a local neutral module is used. The
category of all modules has no braiding assumption. The first mixed
equation, naturality of the ordinary comparison and the proved preservation
of the genuine crossing imply the second mixed equation.
-/
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
  {i : A ⥤ N} [i.Braided] (P : BoundaryAutoequivalence i) (R : A)
  [MonObj R] [IsCommMonObj R]

/-- The other actual mixed tensor equation follows from the real local
central crossing, its preservation and naturality. -/
theorem BoundaryAutoequivalence.moduleComparison_tensor_right
    (S : SeparableAlgebra (i.obj R))
    (e : P.moduleFunctor R ≅ 𝟭 (Mod_ N (i.obj R)))
    (V Y : Mod_ N (i.obj R)) (hV : IsLocalModule V)
    (hleft : Functor.LaxMonoidal.μ (P.moduleFunctor R) V Y ≫ e.hom.app (V ⊗ Y) =
      e.hom.app V ⊗ₘ e.hom.app Y) :
    Functor.LaxMonoidal.μ (P.moduleFunctor R) Y V ≫ e.hom.app (Y ⊗ V) =
      e.hom.app Y ⊗ₘ e.hom.app V := by
  let F := P.moduleFunctor R
  let c := (S.localHalfBraiding V hV).β Y
  let cF := (S.localHalfBraiding V hV).β (F.obj Y)
  have hc := P.moduleFunctor_localHalfBraiding_boundary R S V Y hV (e.app V)
  change (e.inv.app V ▷ F.obj Y) ≫ Functor.LaxMonoidal.μ F V Y ≫
      F.map c.hom = cF.hom ≫ (F.obj Y ◁ e.inv.app V) ≫
        Functor.LaxMonoidal.μ F Y V at hc
  have hn := e.hom.naturality c.hom
  change F.map c.hom ≫ e.hom.app (Y ⊗ V) = e.hom.app (V ⊗ Y) ≫ c.hom at hn
  have hh := congrArg (fun k => k ≫ e.hom.app (Y ⊗ V)) hc
  simp only [Category.assoc] at hh
  rw [hn, ← Category.assoc (Functor.LaxMonoidal.μ F V Y), hleft] at hh
  have hcan : (e.inv.app V ▷ F.obj Y) ≫ (e.hom.app V ⊗ₘ e.hom.app Y) =
      V ◁ e.hom.app Y := by
    rw [MonoidalCategory.tensorHom_def, ← Category.assoc, ← comp_whiskerRight,
      e.inv_hom_id_app, id_whiskerRight, Category.id_comp]
    rfl
  rw [← Category.assoc, hcan] at hh
  have hnat := (S.localHalfBraiding V hV).naturality (e.hom.app Y)
  change (V ◁ e.hom.app Y) ≫ c.hom = cF.hom ≫ (e.hom.app Y ▷ V) at hnat
  rw [hnat] at hh
  have hright := (cancel_epi cF.hom).mp hh
  apply (cancel_epi (F.obj Y ◁ e.inv.app V)).mp
  calc
    _ = e.hom.app Y ▷ V := by simpa only [Category.assoc] using hright.symm
    _ = (F.obj Y ◁ e.inv.app V) ≫ (e.hom.app Y ⊗ₘ e.hom.app V) := by
      rw [MonoidalCategory.tensorHom_def', ← whiskerLeft_comp_assoc,
        e.inv_hom_id_app, whiskerLeft_id, Category.id_comp]
      rfl

end Paper18.Category

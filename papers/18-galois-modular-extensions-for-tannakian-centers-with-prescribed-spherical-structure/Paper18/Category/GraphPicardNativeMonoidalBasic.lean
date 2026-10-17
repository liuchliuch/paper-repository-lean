import Paper18.Category.MonoidalOppositeFusion
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Simultaneously reversing the two tensor orders of a genuine functor

A strong monoidal functor induces a strong monoidal functor between the
monoidal opposites. Both tensor orders reverse, so this construction requires
no braiding on either category.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.Monoidal
universe v u v' u' v'' u''
namespace Paper18.Category.GraphPicard
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

/-- The actual functor obtained by simultaneously reversing the source
and target tensor orders. Its morphisms retain their actual orientation. -/
def simultaneousMop (F : C ⥤ D) : Cᴹᵒᵖ ⥤ Dᴹᵒᵖ :=
  unmopFunctor C ⋙ F ⋙ mopFunctor D

omit [MonoidalCategory C] [MonoidalCategory D] in
@[simp] theorem simultaneousMop_obj_unmop (F : C ⥤ D) (X : Cᴹᵒᵖ) :
    ((simultaneousMop F).obj X).unmop = F.obj X.unmop := rfl
omit [MonoidalCategory C] [MonoidalCategory D] in
@[simp] theorem simultaneousMop_map_unmop (F : C ⥤ D) {X Y : Cᴹᵒᵖ} (f : X ⟶ Y) :
    ((simultaneousMop F).map f).unmop = F.map f.unmop := rfl

/-- The tensorator uses the original tensorator in the reversed order;
all coherence follows from the genuine original coherence. -/
instance simultaneousMopMonoidal (F : C ⥤ D) [F.Monoidal] :
    (simultaneousMop F).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.mop (εIso F)
      μIso X Y := Iso.mop (μIso F Y.unmop X.unmop)
      μIso_hom_natural_left {X Y} f Z := by
        apply Quiver.Hom.unmop_inj
        exact μ_natural_right F Z.unmop f.unmop
      μIso_hom_natural_right {X Y} Z f := by
        apply Quiver.Hom.unmop_inj
        exact μ_natural_left F f.unmop Z.unmop
      associativity X Y Z := by
        apply Quiver.Hom.unmop_inj
        exact Functor.LaxMonoidal.associativity_inv F Z.unmop Y.unmop X.unmop
      left_unitality X := by
        apply Quiver.Hom.unmop_inj
        exact Functor.LaxMonoidal.right_unitality F X.unmop
      right_unitality X := by
        apply Quiver.Hom.unmop_inj
        exact Functor.LaxMonoidal.left_unitality F X.unmop }

@[simp] theorem simultaneousMop_μ_unmop (F : C ⥤ D) [F.Monoidal] (X Y : Cᴹᵒᵖ) :
    (μ (simultaneousMop F) X Y).unmop = μ F Y.unmop X.unmop := rfl
@[simp] theorem simultaneousMop_ε_unmop (F : C ⥤ D) [F.Monoidal] :
    (ε (simultaneousMop F)).unmop = ε F := rfl
@[simp] theorem simultaneousMop_δ_unmop (F : C ⥤ D) [F.Monoidal] (X Y : Cᴹᵒᵖ) :
    (Functor.OplaxMonoidal.δ (simultaneousMop F) X Y).unmop =
      Functor.OplaxMonoidal.δ F Y.unmop X.unmop := rfl
@[simp] theorem simultaneousMop_η_unmop (F : C ⥤ D) [F.Monoidal] :
    (Functor.OplaxMonoidal.η (simultaneousMop F)).unmop = Functor.OplaxMonoidal.η F := rfl

instance simultaneousMopFull (F : C ⥤ D) [F.Full] : (simultaneousMop F).Full := by
  unfold simultaneousMop
  infer_instance
instance simultaneousMopFaithful (F : C ⥤ D) [F.Faithful] : (simultaneousMop F).Faithful := by
  unfold simultaneousMop
  infer_instance
instance simultaneousMopIsEquivalence (F : C ⥤ D) [F.IsEquivalence] :
    (simultaneousMop F).IsEquivalence := by
  unfold simultaneousMop
  infer_instance
instance simultaneousMopAdditive [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] : (simultaneousMop F).Additive := by
  unfold simultaneousMop
  infer_instance
instance simultaneousMopLinear [Preadditive C] [Preadditive D] [Linear ℂ C] [Linear ℂ D]
    (F : C ⥤ D) [F.Linear ℂ] : (simultaneousMop F).Linear ℂ := by
  unfold simultaneousMop
  infer_instance

end Paper18.Category.GraphPicard

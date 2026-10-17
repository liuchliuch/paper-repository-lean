import Mathlib.CategoryTheory.Monoidal.Center
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Actual transport of half-braiding maps along tensor equivalences -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal CategoryTheory.Functor.Monoidal
universe v u v' u'
namespace Paper18.Category.DrinfeldEquivalence
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (E : C ≌ D) [E.functor.Monoidal]

/-- The actual transported crossing uses the chosen actual inverse and
counit of the equivalence, together with the actual tensorator. -/
def halfIso (Z : Center C) (U : D) : E.functor.obj Z.1 ⊗ U ≅ U ⊗ E.functor.obj Z.1 :=
  whiskerLeftIso _ (E.counitIso.app U).symm ≪≫
    μIso E.functor Z.1 (E.inverse.obj U) ≪≫
      E.functor.mapIso (Z.2.β (E.inverse.obj U)) ≪≫
        (μIso E.functor (E.inverse.obj U) Z.1).symm ≪≫
          whiskerRightIso (E.counitIso.app U) _

lemma halfIso_hom (Z : Center C) (U : D) :
    (halfIso E Z U).hom =
      E.functor.obj Z.1 ◁ E.counitIso.inv.app U ≫ μ E.functor Z.1 (E.inverse.obj U) ≫
        E.functor.map (Z.2.β (E.inverse.obj U)).hom ≫ δ E.functor (E.inverse.obj U) Z.1 ≫
          E.counitIso.hom.app U ▷ E.functor.obj Z.1 := rfl

@[reassoc]
lemma halfIso_naturality (Z : Center C) {U V : D} (f : U ⟶ V) :
    E.functor.obj Z.1 ◁ f ≫ (halfIso E Z V).hom =
      (halfIso E Z U).hom ≫ f ▷ E.functor.obj Z.1 := by
  have hn := E.counitIso.inv.naturality f
  change f ≫ E.counitIso.inv.app V = E.counitIso.inv.app U ≫ E.functor.map (E.inverse.map f) at hn
  have hc := E.counitIso.hom.naturality f
  change E.functor.map (E.inverse.map f) ≫ E.counitIso.hom.app V = E.counitIso.hom.app U ≫ f at hc
  simp only [halfIso_hom, assoc]
  rw [← whiskerLeft_comp_assoc, hn, whiskerLeft_comp_assoc,
    μ_natural_right_assoc E.functor Z.1 (E.inverse.map f)]
  rw [← E.functor.map_comp_assoc, Z.2.naturality, E.functor.map_comp_assoc,
    ← δ_natural_left_assoc E.functor (E.inverse.map f) Z.1]
  rw [← comp_whiskerRight, hc, comp_whiskerRight]

/-- The actual transported family is a natural isomorphism of tensor
functors; the tensor hexagon is established separately. -/
def halfNatIso (Z : Center C) : tensorLeft (E.functor.obj Z.1) ≅ tensorRight (E.functor.obj Z.1) :=
  NatIso.ofComponents (halfIso E Z) (fun f => halfIso_naturality E Z f)

@[reassoc]
lemma halfIso_image (Z : Center C) (U : C) :
    (halfIso E Z (E.functor.obj U)).hom =
      μ E.functor Z.1 U ≫ E.functor.map (Z.2.β U).hom ≫ δ E.functor U Z.1 := by
  rw [halfIso_hom, E.counit_app_functor, E.counitInv_app_functor]
  have hm : E.functor.obj Z.1 ◁ E.functor.map (E.unit.app U) ≫
      μ E.functor Z.1 (E.inverse.obj (E.functor.obj U)) =
      μ E.functor Z.1 U ≫ E.functor.map (Z.1 ◁ E.unit.app U) :=
    μ_natural_right E.functor Z.1 (E.unit.app U)
  have hb : Z.1 ◁ E.unit.app U ≫ (Z.2.β (E.inverse.obj (E.functor.obj U))).hom =
      (Z.2.β U).hom ≫ E.unit.app U ▷ Z.1 := Z.2.naturality (E.unit.app U)
  have hmap := congrArg E.functor.map hb
  simp only [E.functor.map_comp] at hmap
  have hd : E.functor.map (E.unit.app U ▷ Z.1) ≫
      δ E.functor (E.inverse.obj (E.functor.obj U)) Z.1 =
      δ E.functor U Z.1 ≫ E.functor.map (E.unit.app U) ▷ E.functor.obj Z.1 :=
    (δ_natural_left E.functor (E.unit.app U) Z.1).symm
  rw [reassoc_of% hm, reassoc_of% hmap, reassoc_of% hd]
  simp only [assoc, ← comp_whiskerRight, ← E.functor.map_comp, Iso.hom_inv_id_app, Functor.id_obj,
    E.functor.map_id, id_whiskerRight, comp_id]

end Paper18.Category.DrinfeldEquivalence

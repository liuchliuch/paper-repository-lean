import Paper18.Category.DrinfeldEquivalenceMap

/-! # Actual tensor and braid coherence of the induced center functor -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal CategoryTheory.Functor.Monoidal
universe v u v' u'
namespace Paper18.Category.DrinfeldEquivalence
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

lemma comm_of_image (F : C ⥤ D) [F.IsEquivalence] {A B : Center D} (f : A.1 ⟶ B.1)
    (h : ∀ U, f ▷ F.obj U ≫ (B.2.β (F.obj U)).hom =
      (A.2.β (F.obj U)).hom ≫ F.obj U ◁ f) (U : D) :
    f ▷ U ≫ (B.2.β U).hom = (A.2.β U).hom ≫ U ◁ f := by
  let a : tensorLeft A.1 ≅ tensorRight A.1 := NatIso.ofComponents A.2.β (fun g => A.2.naturality g)
  let b : tensorLeft B.1 ≅ tensorRight B.1 := NatIso.ofComponents B.2.β (fun g => B.2.naturality g)
  exact comm_of_iso a b f (F.asEquivalence.counitIso.app U) (h (F.asEquivalence.inverse.obj U))

lemma image_tensorator (F : C ⥤ D) [F.Monoidal] (Z W : Center C) (U : C) :
    μ F Z.1 W.1 ▷ F.obj U ≫ μ F (Z.1 ⊗ W.1) U ≫
      F.map ((Z ⊗ W).2.β U).hom ≫ δ F U (Z.1 ⊗ W.1) =
    (α_ (F.obj Z.1) (F.obj W.1) (F.obj U)).hom ≫
      F.obj Z.1 ◁ (μ F W.1 U ≫ F.map (W.2.β U).hom ≫ δ F U W.1) ≫
        (α_ (F.obj Z.1) (F.obj U) (F.obj W.1)).inv ≫
          (μ F Z.1 U ≫ F.map (Z.2.β U).hom ≫ δ F U Z.1) ▷ F.obj W.1 ≫
            (α_ (F.obj U) (F.obj Z.1) (F.obj W.1)).hom ≫ F.obj U ◁ μ F Z.1 W.1 := by
  have hb : ((Z ⊗ W).2.β U).hom = (α_ Z.1 W.1 U).hom ≫
      Z.1 ◁ (W.2.β U).hom ≫ (α_ Z.1 U W.1).inv ≫
        (Z.2.β U).hom ▷ W.1 ≫ (α_ U Z.1 W.1).hom := rfl
  have h := congrArg (fun f => μ F Z.1 W.1 ▷ F.obj U ≫ μ F (Z.1 ⊗ W.1) U ≫
    F.map f ≫ δ F U (Z.1 ⊗ W.1)) hb
  dsimp only at h
  simp only [F.map_comp, Functor.Monoidal.map_associator_inv F,
    Functor.Monoidal.map_associator F, Functor.Monoidal.map_whiskerLeft F,
    Functor.Monoidal.map_whiskerRight F, assoc, μ_δ_assoc,
    whiskerLeft_μ_δ_assoc, whiskerRight_μ_δ_assoc, μ_δ, comp_id] at h
  simpa only [comp_whiskerRight, whiskerLeft_comp, assoc] using h

lemma image_unit (F : C ⥤ D) [F.Monoidal] (U : C) :
    ε F ▷ F.obj U ≫ μ F (𝟙_ C) U ≫
      F.map (((𝟙_ (Center C)).2.β U).hom) ≫ δ F U (𝟙_ C) =
    (λ_ (F.obj U)).hom ≫ (ρ_ (F.obj U)).inv ≫ F.obj U ◁ ε F := by
  change ε F ▷ F.obj U ≫ μ F (𝟙_ C) U ≫
    F.map ((λ_ U).hom ≫ (ρ_ U).inv) ≫ δ F U (𝟙_ C) = _
  simp only [F.map_comp, Functor.Monoidal.map_leftUnitor F,
    Functor.Monoidal.map_rightUnitor_inv F, assoc, μ_δ_assoc,
    whiskerRight_ε_η_assoc, μ_δ, comp_id]

variable (F : C ⥤ D) [F.Monoidal] [F.IsEquivalence]

/-- The actual center tensorator is the original functor's actual tensorator. -/
def tensorator (Z W : Center C) : (map F).obj Z ⊗ (map F).obj W ≅ (map F).obj (Z ⊗ W) :=
  Center.isoMk {
    f := μ F Z.1 W.1
    comm U := comm_of_image F (A := (map F).obj Z ⊗ (map F).obj W) (B := (map F).obj (Z ⊗ W)) (μ F Z.1 W.1) (fun V => by
      change μ F Z.1 W.1 ▷ F.obj V ≫ (halfIso F.asEquivalence (Z ⊗ W) (F.obj V)).hom = _
      rw [halfIso_functor_image F (Z ⊗ W) V]
      simp only [Center.tensor_β, Iso.trans_hom, Iso.symm_hom,
        whiskerLeftIso_hom, whiskerRightIso_hom, assoc]
      change _ = (α_ (F.obj Z.1) (F.obj W.1) (F.obj V)).hom ≫
        F.obj Z.1 ◁ (halfIso F.asEquivalence W (F.obj V)).hom ≫
          (α_ (F.obj Z.1) (F.obj V) (F.obj W.1)).inv ≫
            (halfIso F.asEquivalence Z (F.obj V)).hom ▷ F.obj W.1 ≫
              (α_ (F.obj V) (F.obj Z.1) (F.obj W.1)).hom ≫ F.obj V ◁ μ F Z.1 W.1
      rw [halfIso_functor_image F W V, halfIso_functor_image F Z V]
      exact image_tensorator F Z W V) U }

def unitor : 𝟙_ (Center D) ≅ (map F).obj (𝟙_ (Center C)) :=
  Center.isoMk {
    f := ε F
    comm U := comm_of_image F (A := 𝟙_ (Center D)) (B := (map F).obj (𝟙_ (Center C))) (ε F) (fun V => by
      change ε F ▷ F.obj V ≫ (halfIso F.asEquivalence (𝟙_ (Center C)) (F.obj V)).hom = _
      rw [halfIso_functor_image F (𝟙_ (Center C)) V]
      simpa only [Center.tensorUnit_β, Iso.trans_hom, Iso.symm_hom, assoc] using image_unit F V) U }

instance map_monoidal : (map F).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := unitor F
    μIso := tensorator F
    μIso_hom_natural_left f Z := by apply Center.Hom.ext; exact μ_natural_left F f.f Z.1
    μIso_hom_natural_right Z f := by apply Center.Hom.ext; exact μ_natural_right F Z.1 f.f
    associativity Z W U := by apply Center.Hom.ext; exact Functor.LaxMonoidal.associativity F Z.1 W.1 U.1
    left_unitality Z := by apply Center.Hom.ext; exact Functor.LaxMonoidal.left_unitality F Z.1
    right_unitality Z := by apply Center.Hom.ext; exact Functor.LaxMonoidal.right_unitality F Z.1 }

@[simp] lemma map_ε_f : (ε (map F)).f = ε F := rfl
@[simp] lemma map_μ_f (Z W : Center C) : (μ (map F) Z W).f = μ F Z.1 W.1 := rfl

instance map_braided : (map F).Braided where
  braided Z W := by
    apply Center.Hom.ext
    change μ F Z.1 W.1 ≫ F.map (Z.2.β W.1).hom =
      (halfIso F.asEquivalence Z (F.obj W.1)).hom ≫ μ F W.1 Z.1
    rw [halfIso_functor_image F Z W.1]
    simp only [assoc, δ_μ, comp_id]

instance forgetIso_monoidal : NatTrans.IsMonoidal (forgetIso F).hom where
  unit := by
    simp only [Functor.LaxMonoidal.comp_ε, Center.forget_ε, map_map_f, forgetIso, Iso.refl_hom,
      NatTrans.id_app, Functor.map_id, comp_id, id_comp]
    rfl
  tensor Z W := by
    simp only [Functor.LaxMonoidal.comp_μ, Center.forget_μ, map_map_f, forgetIso, Iso.refl_hom,
      NatTrans.id_app, Functor.map_id, tensorHom_id, id_whiskerRight, comp_id, id_comp]
    change 𝟙 _ ≫ μ F Z.1 W.1 = μ F Z.1 W.1
    exact id_comp _

end Paper18.Category.DrinfeldEquivalence

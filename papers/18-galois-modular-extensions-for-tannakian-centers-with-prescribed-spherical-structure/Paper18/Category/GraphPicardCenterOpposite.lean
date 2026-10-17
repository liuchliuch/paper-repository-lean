import Paper18.Category.DrinfeldRigidBasic
import Paper18.Category.ModuleAlphaInductionOpposite

/-! # The actual center object for the opposite tensor order -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
universe v u
namespace Paper18.Category.GraphPicard
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

/-- Reversing the tensor order inverts the specified actual half-braiding. -/
def oppositeHalfBraiding (Z : Center D) : HalfBraiding (mop Z.1) where
  β X := (Z.2.β X.unmop).symm.mop
  monoidal X Y := by
    apply Quiver.Hom.unmop_inj
    change (Z.2.β (Y.unmop ⊗ X.unmop)).inv =
      (α_ Y.unmop X.unmop Z.1).hom ≫ Y.unmop ◁ (Z.2.β X.unmop).inv ≫
        (α_ Y.unmop Z.1 X.unmop).inv ≫ (Z.2.β Y.unmop).inv ▷ X.unmop ≫
          (α_ Z.1 Y.unmop X.unmop).hom
    exact Drinfeld.halfBraiding_inv_monoidal Z.2 Y.unmop X.unmop
  naturality f := by
    apply Quiver.Hom.unmop_inj
    exact Drinfeld.halfBraiding_inv_naturality Z.2 f.unmop

/-- Actual central morphisms retain their actual underlying maps when the
tensor order and the half-braidings are both reversed. -/
def centerOpposite : Center D ⥤ Center Dᴹᵒᵖ where
  obj Z := ⟨mop Z.1, oppositeHalfBraiding Z⟩
  map {Z W} f :=
    { f := f.f.mop
      comm X := by
        apply Quiver.Hom.unmop_inj
        change X.unmop ◁ f.f ≫ (W.2.β X.unmop).inv =
          (Z.2.β X.unmop).inv ≫ f.f ▷ X.unmop
        apply (cancel_epi (Z.2.β X.unmop).hom).mp
        rw [← f.comm_assoc]
        simp only [Category.assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc,
          Category.comp_id] }
  map_id Z := by apply Center.ext; rfl
  map_comp f g := by apply Center.ext; rfl

@[simp] lemma centerOpposite_obj_fst (Z : Center D) :
    (centerOpposite.obj Z).1 = mop Z.1 := rfl

@[simp] lemma centerOpposite_obj_halfBraiding (Z : Center D) (X : Dᴹᵒᵖ) :
    ((centerOpposite.obj Z).2.β X).hom.unmop = (Z.2.β X.unmop).inv := rfl

/-- Reversing the tensor order also reverses the two central factors;
the actual underlying comparison is the actual identity map. -/
def centerOppositeTensorIso (Z W : Center D) :
    centerOpposite.obj W ⊗ centerOpposite.obj Z ≅ centerOpposite.obj (Z ⊗ W) := by
  refine Center.isoMk ⟨𝟙 _, ?_⟩
  intro X
  simp only [MonoidalCategory.id_whiskerRight, MonoidalCategory.whiskerLeft_id,
    Category.id_comp, Category.comp_id]
  apply Quiver.Hom.unmop_inj
  change (((Center.tensorObj Z W).2.β X.unmop).inv) =
    ((Center.tensorObj (⟨mop W.1, oppositeHalfBraiding W⟩ : Center Dᴹᵒᵖ)
      (⟨mop Z.1, oppositeHalfBraiding Z⟩ : Center Dᴹᵒᵖ)).2.β X).hom.unmop
  simp only [Center.tensorObj_snd_β, Iso.trans_inv, Iso.symm_inv,
    whiskerLeftIso_inv, whiskerRightIso_inv, Iso.trans_hom, Iso.symm_hom,
    whiskerLeftIso_hom, whiskerRightIso_hom, oppositeHalfBraiding,
    Functor.mapIso_hom, Functor.mapIso_inv, unmop_comp,
    unmop_hom_associator, unmop_inv_associator,
    unmop_whiskerLeft, unmop_whiskerRight,
    Category.assoc]
  rfl

/-- The opposite-center unit comparison is the actual identity on its
underlying tensor unit. -/
def centerOppositeUnitIso : 𝟙_ (Center Dᴹᵒᵖ) ≅ centerOpposite.obj (𝟙_ (Center D)) := by
  refine Center.isoMk ⟨𝟙 _, ?_⟩
  intro X
  simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
  apply Quiver.Hom.unmop_inj
  change ((𝟙_ (Center D)).2.β X.unmop).inv =
    ((λ_ X).hom ≫ (ρ_ X).inv).unmop
  simp only [Center.tensorUnit_β, Iso.trans_inv, Iso.symm_inv,
    unmop_comp, unmop_hom_leftUnitor, unmop_inv_rightUnitor]

section Braided
variable [BraidedCategory D]

/-- Reversing tensor order carries the actual positive half-braiding to
the actual negative half-braiding for the monoidal opposite. -/
def oppositePositiveIso (X : D) :
    centerOpposite.obj ((Drinfeld.positive D).obj X) ≅
      (Drinfeld.negative Dᴹᵒᵖ).obj (mop X) := by
  refine Center.isoMk ⟨𝟙 _, ?_⟩
  intro Y
  simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
  rfl

/-- The actual negative half-braiding becomes the actual positive one. -/
def oppositeNegativeIso (X : D) :
    centerOpposite.obj ((Drinfeld.negative D).obj X) ≅
      (Drinfeld.positive Dᴹᵒᵖ).obj (mop X) := by
  refine Center.isoMk ⟨𝟙 _, ?_⟩
  intro Y
  simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
  rfl
end Braided

end Paper18.Category.GraphPicard

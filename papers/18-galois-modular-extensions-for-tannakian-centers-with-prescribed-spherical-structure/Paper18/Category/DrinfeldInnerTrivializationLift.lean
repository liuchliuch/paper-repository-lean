import Paper18.Category.DrinfeldEquivalenceMapEquivalence
import Paper18.Category.DrinfeldGeneralNondegenerateBasic

/-! # Lifting an actual monoidal isomorphism over the dominant center forgetful functor -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
open CategoryTheory.Functor.Monoidal
universe v u w
namespace Paper18.Category.DrinfeldInner
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (F : C ⥤ C) [F.Monoidal] [F.IsEquivalence]
  (σ : DrinfeldEquivalence.map F ⋙ Center.forget C ≅ Center.forget C)
  [NatTrans.IsMonoidal σ.hom]

lemma overForget_tensor (Z W : Center C) :
    μ F Z.1 W.1 ≫ σ.hom.app (Z ⊗ W) = σ.hom.app Z ⊗ₘ σ.hom.app W := by
  have h := NatTrans.IsMonoidal.tensor (τ := σ.hom) Z W
  simp only [Functor.LaxMonoidal.comp_μ, Center.forget_μ] at h
  change (𝟙 _ ≫ μ F Z.1 W.1) ≫ σ.hom.app (Z ⊗ W) =
    (σ.hom.app Z ⊗ₘ σ.hom.app W) ≫ 𝟙 _ at h
  simpa only [id_comp, comp_id] using h

/-- Monoidality and naturality at the actual central braiding force the
underlying component to respect crossings with every central image. -/
lemma overForget_comm_image (Z W : Center C) :
    σ.hom.app Z ▷ F.obj W.1 ≫ (Z.2.β (F.obj W.1)).hom =
      (((DrinfeldEquivalence.map F).obj Z).2.β (F.obj W.1)).hom ≫
        F.obj W.1 ◁ σ.hom.app Z := by
  have hZW := overForget_tensor F σ Z W
  have hWZ := overForget_tensor F σ W Z
  have hn := σ.hom.naturality (β_ Z W).hom
  change F.map (Z.2.β W.1).hom ≫ σ.hom.app (W ⊗ Z) =
    σ.hom.app (Z ⊗ W) ≫ (Z.2.β W.1).hom at hn
  have hb : (((DrinfeldEquivalence.map F).obj Z).2.β (F.obj W.1)).hom ≫
      (σ.hom.app W ⊗ₘ σ.hom.app Z) =
        (σ.hom.app Z ⊗ₘ σ.hom.app W) ≫ (Z.2.β W.1).hom := by
    change (DrinfeldEquivalence.halfIso F.asEquivalence Z (F.obj W.1)).hom ≫ _ = _
    rw [DrinfeldEquivalence.halfIso_functor_image F Z W.1, ← hWZ]
    simp only [Category.assoc, δ_μ_assoc]
    rw [hn, ← Category.assoc, hZW]
  apply (cancel_mono (σ.hom.app W ▷ Z.1)).mp
  have hw := Z.2.naturality (σ.hom.app W)
  change Z.1 ◁ σ.hom.app W ≫ (Z.2.β W.1).hom =
    (Z.2.β (F.obj W.1)).hom ≫ σ.hom.app W ▷ Z.1 at hw
  calc
    _ = (σ.hom.app Z ⊗ₘ σ.hom.app W) ≫ (Z.2.β W.1).hom := by
      rw [Category.assoc, ← hw,
        ← Category.assoc, MonoidalCategory.tensorHom_def]
      rfl
    _ = _ := by
      rw [← hb, MonoidalCategory.tensorHom_def', Category.assoc]
      rfl

/-- A crossing equation descends along an actual retract in the testing object. -/
lemma comm_of_retract {Z W : Center C} (f : Z.1 ⟶ W.1) {Y V : C}
    (r : Retract Y V)
    (hc : f ▷ V ≫ (W.2.β V).hom = (Z.2.β V).hom ≫ V ◁ f) :
    f ▷ Y ≫ (W.2.β Y).hom = (Z.2.β Y).hom ≫ Y ◁ f := by
  let sm : SplitMono (r.i ▷ W.1) :=
    { retraction := r.r ▷ W.1
      id := by rw [← comp_whiskerRight, r.retract, id_whiskerRight] }
  letI : IsSplitMono (r.i ▷ W.1) := ⟨⟨sm⟩⟩
  apply (cancel_mono (r.i ▷ W.1)).mp
  calc
    _ = Z.1 ◁ r.i ≫ (f ▷ V ≫ (W.2.β V).hom) := by
      simp only [Category.assoc]
      rw [← W.2.naturality r.i, ← whisker_exchange_assoc f r.i]
    _ = Z.1 ◁ r.i ≫ ((Z.2.β V).hom ≫ V ◁ f) := by rw [hc]
    _ = (Z.2.β Y).hom ≫ (r.i ▷ Z.1 ≫ V ◁ f) := by
      rw [← Category.assoc, Z.2.naturality r.i]
      simp only [Category.assoc]
    _ = _ := by rw [← whisker_exchange r.i f]; simp only [Category.assoc]

section Fusion
variable [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)
include S J

/-- Actual unit-coordinate induction supplies density of the central
objects even after applying an arbitrary tensor equivalence. -/
def imageInductionRetract (Y : C) :
    Retract Y (F.obj (Drinfeld.inductionUnderlying S (F.asEquivalence.inverse.obj Y))) :=
  (F.asEquivalence.counitIso.app Y).symm.retract.trans
    ((Drinfeld.inductionUnderlyingUnitRetract S (F.asEquivalence.inverse.obj Y)).map F)

lemma overForget_comm (Z : Center C) (Y : C) :
    σ.hom.app Z ▷ Y ≫ (Z.2.β Y).hom =
      (((DrinfeldEquivalence.map F).obj Z).2.β Y).hom ≫ Y ◁ σ.hom.app Z := by
  exact comm_of_retract (σ.hom.app Z) (imageInductionRetract F S Y)
    (overForget_comm_image F σ Z
      (Drinfeld.inductionObj S J (F.asEquivalence.inverse.obj Y)))

/-- The actual monoidal isomorphism over forgetting lifts to the actual
center; no central-morphism equation is supplied as data. -/
def liftOverForget : DrinfeldEquivalence.map F ≅ 𝟭 (Center C) :=
  NatIso.ofComponents (fun Z => Center.isoMk {
    f := σ.hom.app Z
    comm Y := overForget_comm F σ S J Z Y })
    (by intro Z W f; apply Center.Hom.ext; exact σ.hom.naturality f)

@[simp] lemma liftOverForget_hom_app_f (Z : Center C) :
    ((liftOverForget F σ S J).hom.app Z).f = σ.hom.app Z := rfl

instance liftOverForget_monoidal : NatTrans.IsMonoidal (liftOverForget F σ S J).hom where
  unit := by
    apply Center.Hom.ext
    simpa only [Functor.LaxMonoidal.comp_ε, Center.forget_ε,
      DrinfeldEquivalence.map_ε_f, Functor.map_id, id_comp, comp_id] using
      (NatTrans.IsMonoidal.unit (τ := σ.hom))
  tensor Z W := by
    apply Center.Hom.ext
    change μ F Z.1 W.1 ≫ σ.hom.app (Z ⊗ W) =
      (σ.hom.app Z ⊗ₘ σ.hom.app W) ≫ 𝟙 _
    simpa only [comp_id] using overForget_tensor F σ Z W

end Fusion
end Paper18.Category.DrinfeldInner

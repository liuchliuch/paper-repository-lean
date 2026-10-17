import Paper18.Category.DrinfeldGeneralNondegenerateBasic

/-! # Actual fullness of forgetting transparent central objects -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
include S

/-- Every actual underlying morphism between transparent central objects
respects all half-braidings. Induction and its unit-coordinate retract
supply all ambient test objects. -/
lemma transparent_hom_comm (J : PivotalStructure C)
    (Z W : Center C) (hZ : Z ∈ mugerCenter) (hW : W ∈ mugerCenter)
    (f : Z.1 ⟶ W.1) (Y : C) :
    f ▷ Y ≫ (W.2.β Y).hom = (Z.2.β Y).hom ≫ Y ◁ f := by
  let I := inductionObj S J Y
  let r := inductionUnderlyingUnitRetract S Y
  have hz := congrArg Center.Hom.f (hZ I (Set.mem_univ _))
  have hw := congrArg Center.Hom.f (hW I (Set.mem_univ _))
  change (Z.2.β I.1).hom ≫ (I.2.β Z.1).hom = 𝟙 _ at hz
  change (W.2.β I.1).hom ≫ (I.2.β W.1).hom = 𝟙 _ at hw
  have hc : f ▷ I.1 ≫ (W.2.β I.1).hom = (Z.2.β I.1).hom ≫ I.1 ◁ f := by
    apply (cancel_mono (I.2.β W.1).hom).mp
    simp only [assoc]
    rw [hw, comp_id, I.2.naturality, ← assoc, hz, id_comp]
  change f ▷ inductionUnderlying S Y ≫ (W.2.β (inductionUnderlying S Y)).hom =
    (Z.2.β (inductionUnderlying S Y)).hom ≫ inductionUnderlying S Y ◁ f at hc
  let sm : SplitMono (r.i ▷ W.1) :=
    { retraction := r.r ▷ W.1
      id := by rw [← comp_whiskerRight, r.retract, id_whiskerRight] }
  letI : IsSplitMono (r.i ▷ W.1) := ⟨⟨sm⟩⟩
  apply (cancel_mono (r.i ▷ W.1)).mp
  calc
    _ = Z.1 ◁ r.i ≫ (f ▷ inductionUnderlying S Y ≫ (W.2.β (inductionUnderlying S Y)).hom) := by
      simp only [assoc]
      rw [← W.2.naturality r.i, ← whisker_exchange_assoc f r.i]
    _ = Z.1 ◁ r.i ≫ ((Z.2.β (inductionUnderlying S Y)).hom ≫ inductionUnderlying S Y ◁ f) := by rw [hc]
    _ = (Z.2.β Y).hom ≫ (r.i ▷ Z.1 ≫ inductionUnderlying S Y ◁ f) := by
      rw [← assoc, Z.2.naturality r.i]
      simp only [assoc]
    _ = _ := by rw [← whisker_exchange r.i f]; simp only [assoc]

/-- The actual lift of every underlying map between transparent objects. -/
def transparentHom (J : PivotalStructure C)
    (Z W : Center C) (hZ : Z ∈ mugerCenter) (hW : W ∈ mugerCenter)
    (f : Z.1 ⟶ W.1) : Z ⟶ W where
  f := f
  comm Y := transparent_hom_comm S J Z W hZ hW f Y

@[simp] lemma transparentHom_f (J : PivotalStructure C)
    (Z W : Center C) (hZ : Z ∈ mugerCenter) (hW : W ∈ mugerCenter)
    (f : Z.1 ⟶ W.1) : (transparentHom S J Z W hZ hW f).f = f := rfl

end Paper18.Category.Drinfeld

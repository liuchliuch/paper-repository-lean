import Paper18.Category.DrinfeldLoopTraceProjection
import Paper18.Category.NondegenerateBasic

/-! # Unit-coordinate tests for arbitrary actual Drinfeld centers -/
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

/-- The actual unit-labelled diagonal of induction is canonically the
original object. -/
def inductionUnitDiagonalIso (X : C) : inductionDiagonal S X S.unitLabel ≅ X :=
  (((S.unitIso ⊗ᵢ Iso.refl X) ⊗ᵢ
    ((dualMapIso S.unitIso).symm ≪≫ dualUnitIso)) ≪≫
      ((λ_ X) ⊗ᵢ Iso.refl (𝟙_ C))) ≪≫ ρ_ X

/-- Every actual object is an actual retract of the underlying object of
its induction, by the actual unit coordinate of the coend. -/
def inductionUnderlyingUnitRetract (X : C) : Retract X (inductionUnderlying S X) where
  i := (inductionUnitDiagonalIso S X).inv ≫ inductionι S X (S.simpleObject S.unitLabel)
  r := inductionProjection S X S.unitLabel ≫ (inductionUnitDiagonalIso S X).hom
  retract := by
    rw [assoc, inductionι_projection_self_assoc S X S.unitLabel]
    rw [Category.id_comp (inductionUnitDiagonalIso S X).hom]
    exact (inductionUnitDiagonalIso S X).inv_hom_id

/-- The unit-coordinate crossing test is an actual natural endomorphism.
It is constructed without a braiding on the underlying category. -/
def inductionUnitTest (J : PivotalStructure C) : 𝟭 C ⟶ 𝟭 C where
  app U := (λ_ U).inv ≫ (inductionUnderlyingUnitRetract S (𝟙_ C)).i ▷ U ≫
    ((inductionObj S J (𝟙_ C)).2.β U).hom ≫
      U ◁ (inductionUnderlyingUnitRetract S (𝟙_ C)).r ≫ (ρ_ U).hom
  naturality {X Y} f := by
    simp only [Functor.id_map, assoc]
    rw [leftUnitor_inv_naturality_assoc f]
    have hn : inductionUnderlying S (𝟙_ C) ◁ f ≫
        ((inductionObj S J (𝟙_ C)).2.β Y).hom =
      ((inductionObj S J (𝟙_ C)).2.β X).hom ≫ f ▷ inductionUnderlying S (𝟙_ C) :=
      (inductionObj S J (𝟙_ C)).2.naturality f
    rw [whisker_exchange_assoc (inductionUnderlyingUnitRetract S (𝟙_ C)).i f,
      reassoc_of% hn,
      ← whisker_exchange_assoc f (inductionUnderlyingUnitRetract S (𝟙_ C)).r,
      rightUnitor_naturality f]

/-- Transparency in the actual center makes the unit-coordinate crossing
test equal the identity on the underlying object. -/
lemma inductionUnitTest_eq_id_of_transparent (J : PivotalStructure C)
    (Z : Center C) (hZ : Z ∈ mugerCenter) :
    (inductionUnitTest S J).app Z.1 = 𝟙 Z.1 := by
  let I := inductionObj S J (𝟙_ C)
  let r := inductionUnderlyingUnitRetract S (𝟙_ C)
  have hz := congrArg Center.Hom.f (hZ I (Set.mem_univ _))
  change (Z.2.β I.1).hom ≫ (I.2.β Z.1).hom = 𝟙 _ at hz
  have hn := Z.2.naturality r.i
  change (Z.1 ◁ r.i) ≫ (Z.2.β I.1).hom =
    (Z.2.β (𝟙_ C)).hom ≫ r.i ▷ Z.1 at hn
  have hb : r.i ▷ Z.1 ≫ (I.2.β Z.1).hom =
      (Z.2.β (𝟙_ C)).inv ≫ Z.1 ◁ r.i := by
    apply (cancel_epi (Z.2.β (𝟙_ C)).hom).mp
    rw [← assoc, ← hn, assoc, hz, Iso.hom_inv_id_assoc]
    exact Category.comp_id _
  change (λ_ Z.1).inv ≫ r.i ▷ Z.1 ≫ (I.2.β Z.1).hom ≫
    Z.1 ◁ r.r ≫ (ρ_ Z.1).hom = _
  rw [reassoc_of% hb]
  have hu : (Z.2.β (𝟙_ C)).inv = (λ_ Z.1).hom ≫ (ρ_ Z.1).inv := by
    apply (cancel_epi (Z.2.β (𝟙_ C)).hom).mp
    rw [Iso.hom_inv_id, halfBraiding_unit]
    simp only [assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  rw [hu]
  simp only [assoc, Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc, r.retract,
    whiskerLeft_id, id_comp, Iso.inv_hom_id]

end Paper18.Category.Drinfeld

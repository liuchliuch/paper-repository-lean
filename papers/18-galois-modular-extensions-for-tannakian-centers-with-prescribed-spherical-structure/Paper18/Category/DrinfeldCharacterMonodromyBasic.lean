import Paper18.Category.DrinfeldCharacterFactorization
import Paper18.Category.InvertibleMonodromy

/-! # The actual monodromy encoded by a central character isomorphism -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
universe v u
namespace Paper18.Category.Drinfeld
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]

lemma character_relativeMonodromy (U : C) :
    (((characterObject χ).2).β U).hom ≫ (β_ U (𝟙_ C)).hom =
      (𝟙_ C) ◁ χ.hom.app U := by
  rw [characterObject_halfBraiding, braiding_tensorUnit_right]
  simp only [assoc, Iso.inv_hom_id_assoc]
  rw [← leftUnitor_naturality_assoc]
  simp

/-- An actual central isomorphism to the unit character fixes the entire
relative monodromy, by actual centrality and ambient braiding naturality. -/
lemma relativeMonodromy_of_characterIso {Z : Center C} (e : Z ≅ characterObject χ) (U : C) :
    (Z.2.β U).hom ≫ (β_ U Z.1).hom = Z.1 ◁ χ.hom.app U := by
  haveI : IsIso e.hom.f := by
    change IsIso ((Center.forget C).map e.hom)
    infer_instance
  apply (cancel_mono (e.hom.f ▷ U)).1
  calc
    _ = (Z.2.β U).hom ≫ U ◁ e.hom.f ≫ (β_ U (𝟙_ C)).hom := by
      rw [assoc, ← braiding_naturality_right]
      rfl
    _ = e.hom.f ▷ U ≫ (((characterObject χ).2).β U).hom ≫
        (β_ U (𝟙_ C)).hom := by
      rw [← reassoc_of% (e.hom.comm U)]
    _ = e.hom.f ▷ U ≫ (𝟙_ C) ◁ χ.hom.app U := by
      rw [character_relativeMonodromy χ U]
    _ = _ := (whisker_exchange e.hom.f (χ.hom.app U)).symm

/-- Reorder the negative strand past the test object. -/
def characterPairCrossing (X Y U : C) : (X ⊗ Y) ⊗ U ≅ (X ⊗ U) ⊗ Y :=
  (α_ X Y U) ≪≫ whiskerLeftIso X (β_ U Y).symm ≪≫ (α_ X U Y).symm

/-- The pair's relative monodromy is the positive strand's actual double
braiding, conjugated by an actual negative crossing. -/
lemma characterPair_relativeMonodromy (X Y U : C) :
    ((((positive C).obj X ⊗ (negative C).obj Y).2).β U).hom ≫ (β_ U (X ⊗ Y)).hom =
      (characterPairCrossing X Y U).hom ≫ (doubleBraiding X U).hom ▷ Y ≫
        (characterPairCrossing X Y U).inv := by
  change (((factorizationBifunctor C).obj (X,Y)).2.β U).hom ≫ (β_ U (X ⊗ Y)).hom = _
  rw [factorizationHalfBraiding, braiding_tensor_right_hom]
  simp only [characterPairCrossing, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, whiskerLeftIso_hom, whiskerLeftIso_inv, doubleBraiding,
    assoc, Iso.hom_inv_id_assoc, comp_whiskerRight]

/-- The same crossing transports any actual endomorphism of the test
object to its expected whiskered endomorphism. -/
lemma characterPairCrossing_conjugate (X Y U : C) (f : U ⟶ U) :
    (characterPairCrossing X Y U).hom ≫ (X ◁ f) ▷ Y ≫
      (characterPairCrossing X Y U).inv = (X ⊗ Y) ◁ f := by
  calc
    _ = (α_ X Y U).hom ≫ X ◁ ((β_ U Y).inv ≫ f ▷ Y ≫ (β_ U Y).hom) ≫
        (α_ X Y U).inv := by
      simp only [characterPairCrossing, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
        Iso.symm_inv, whiskerLeftIso_hom, whiskerLeftIso_inv]
      monoidal
    _ = (α_ X Y U).hom ≫ X ◁ (Y ◁ f) ≫ (α_ X Y U).inv := by
      rw [← braiding_inv_naturality_right_assoc]
      simp
    _ = _ := by monoidal

/-- Forgetting an actual central pair isomorphism supplies actual inverse data. -/
def characterPairInverse {X Y : C}
    (e : (positive C).obj X ⊗ (negative C).obj Y ≅ characterObject χ) : TensorInverse X where
  inverse := Y
  right := (Center.forget C).mapIso e
  left := (β_ Y X) ≪≫ (Center.forget C).mapIso e

/-- The positive factor of an actual character pair represents that exact
character, with the stated orientation rather than its inverse. -/
lemma characterPairInverse_monodromy {X Y : C}
    (e : (positive C).obj X ⊗ (negative C).obj Y ≅ characterObject χ) :
    (characterPairInverse χ e).monodromyCharacter = χ := by
  let A := characterPairInverse χ e
  letI : (tensorLeft Y).IsEquivalence := A.symm.tensorLeftIsEquivalence
  letI : (tensorRight Y).Faithful := Functor.Faithful.of_iso (tensorLeftIsoTensorRight Y)
  apply A.monodromyCharacter_eq_of_spec χ
  intro U
  have hr := relativeMonodromy_of_characterIso χ e U
  change ((((positive C).obj X ⊗ (negative C).obj Y).2).β U).hom ≫
      (β_ U (X ⊗ Y)).hom = (X ⊗ Y) ◁ χ.hom.app U at hr
  rw [characterPair_relativeMonodromy X Y U] at hr
  have hh : (characterPairCrossing X Y U).hom ≫ (doubleBraiding X U).hom ▷ Y ≫
      (characterPairCrossing X Y U).inv =
    (characterPairCrossing X Y U).hom ≫ (X ◁ χ.hom.app U) ▷ Y ≫
      (characterPairCrossing X Y U).inv :=
    hr.trans (characterPairCrossing_conjugate X Y U (χ.hom.app U)).symm
  have hm : (doubleBraiding X U).hom ▷ Y = (X ◁ χ.hom.app U) ▷ Y := by
    apply (cancel_epi (characterPairCrossing X Y U).hom).1
    apply (cancel_mono (characterPairCrossing X Y U).inv).1
    simpa only [assoc] using hh
  symm
  exact (tensorRight Y).map_injective hm

end Paper18.Category.Drinfeld

import Paper18.Category.LocalModulesPivotalRibbon

/-! # Reversing the braiding of an actual spherical pivotal category -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
universe v u w
namespace Paper18.Category.PivotalStructure
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C] (J : PivotalStructure C)

/-- Ribbon dual compatibility and balancing identify the reversed crossing
cap with the actual pivotal cap preceded by the actual twist. -/
lemma reverse_braiding_evaluation (hJ : J.TwistSelfDual) (X : C) :
    (β_ (dual C X) X).inv ≫ ε_ X (dual C X) =
      (J.twistIso X).hom ▷ dual C X ≫ J.leftEvaluation X := by
  have hn := J.twist_naturality (ε_ X (dual C X))
  rw [J.twist_unit, comp_id, J.twist_tensor] at hn
  have hh := congrArg (fun f => (β_ (dual C X) X).inv ≫ f) hn
  simp only [doubleBraiding, Iso.trans_hom, ← assoc, Iso.inv_hom_id, id_comp] at hh
  symm
  calc
    _ = ((J.twistIso X).hom ▷ dual C X) ≫
        ((J.twistIso X).hom ▷ dual C X) ≫
          (β_ X (dual C X)).hom ≫ ε_ X (dual C X) := by
      rw [← J.twist_evaluation]
    _ = (β_ X (dual C X)).hom ≫
        ((J.twistIso (dual C X)).hom ⊗ₘ (J.twistIso X).hom) ≫
          ε_ X (dual C X) := by
      rw [hJ X, tensorHom_def', assoc, rightAdjointMate_comp_evaluation]
      rw [braiding_naturality_left_assoc, braiding_naturality_left_assoc]
    _ = _ := by simpa only [assoc] using hh.symm

/-- The reverse Drinfeld comparison is the actual pivotal map preceded by
the original twist. The identity is detected by its actual evaluation. -/
lemma drinfeldIso_reverse (hJ : J.TwistSelfDual) (X : C) :
    (letI : BraidedCategory C := reverseBraiding C; (drinfeldIso X).hom) =
      (J.twistIso X).hom ≫ J.j.hom.app X := by
  apply pairing_hom_ext
    (inferInstanceAs (ExactPairing (dual C X) (dual C (dual C X))))
  have he := @drinfeldIso_evaluation C _ _ _ (reverseBraiding C) X
  change (letI : BraidedCategory C := reverseBraiding C; (drinfeldIso X).hom) ▷ dual C X ≫
      ε_ (dual C X) (dual C (dual C X)) =
    ((J.twistIso X).hom ≫ J.j.hom.app X) ▷ dual C X ≫
      ε_ (dual C X) (dual C (dual C X))
  rw [he]
  change (β_ (dual C X) X).inv ≫ ε_ X (dual C X) = _
  rw [J.reverse_braiding_evaluation hJ X, comp_whiskerRight, assoc]
  rfl

/-- Reversing the braiding inverts the actual twist when the given pivotal
structure has self-dual twist. -/
theorem twist_reverse_of_selfDual (hJ : J.TwistSelfDual) (X : C) :
    (letI : BraidedCategory C := reverseBraiding C; (J.twistIso X).hom) =
      (J.twistIso X).inv := by
  let u : X ≅ (doubleDualFunctor C).obj X :=
    letI : BraidedCategory C := reverseBraiding C
    drinfeldIso X
  apply (cancel_mono u.hom).mp
  have he := @twist_comp_drinfeld C _ _ _ (reverseBraiding C) J X
  change (letI : BraidedCategory C := reverseBraiding C; (J.twistIso X).hom) ≫ u.hom =
    (J.twistIso X).inv ≫ u.hom
  rw [he, J.drinfeldIso_reverse hJ X]
  simp only [← assoc, Iso.inv_hom_id, id_comp]

section Fusion
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [CategoryTheory.Limits.HasKernels C] [CategoryTheory.Limits.HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
include S

/-- The actual prescribed spherical pivotal structure has inverse twist
for the reversed braiding, on every actual object. -/
theorem twist_reverse_of_spherical (hJ : J.Spherical) (X : C) :
    (letI : BraidedCategory C := reverseBraiding C; (J.twistIso X).hom) =
      (J.twistIso X).inv :=
  J.twist_reverse_of_selfDual (J.twistSelfDual_of_spherical S hJ) X

end Fusion
end Paper18.Category.PivotalStructure

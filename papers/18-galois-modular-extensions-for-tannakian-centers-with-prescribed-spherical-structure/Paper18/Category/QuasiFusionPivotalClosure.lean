import Paper18.Category.QuasiFusionPivotalBasic
import Paper18.Category.PointedTrace
import Paper18.Category.QuasiFusionPivotalCriterion

/-! # Actual closures of the weighted cocycle bidual maps -/
noncomputable section
set_option maxHeartbeats 1200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
namespace Paper18.Category.QuasiFusion.CocycleVec
attribute [local instance 2000] RightRigidCategory.rightDual
variable {G : Type} [Group G] [Fintype G] (ψ : ThreeCocycle G)

private lemma mate_eqToHom {V W : FGModuleCat ℂ} (h : V = W) :
    dualMap (FGModuleCat ℂ) (eqToHom h) =
      eqToHom (congrArg (fun U => dual (FGModuleCat ℂ) U) h).symm := by
  subst W
  change dualMap (FGModuleCat ℂ) (𝟙 V) = 𝟙 (dual (FGModuleCat ℂ) V)
  exact rightAdjointMate_id

lemma bidualFiberIso_inv (X : CocycleVec ψ) (a : Additive G) :
    (bidualFiberIso ψ X a).inv =
      dualMap (FGModuleCat ℂ) (PointedVec.dualFiberIso X a).hom := by
  symm
  exact mate_eqToHom (congrArg (fun b => (X b)ᘁ) (neg_neg a))

/-- The actual unweighted fiber map has the ordinary flipped vector cap,
including the actual chosen inverse-degree transport. -/
@[reassoc]
lemma unweightedPivotalFiber_evaluation (X : CocycleVec ψ) (a : Additive G) :
    (unweightedPivotalFiber ψ X a).hom ▷ (PointedVec.gradedDual X (-a)) ≫
      ε_ (PointedVec.gradedDual X (-a)) (dual (FGModuleCat ℂ) (PointedVec.gradedDual X (-a))) =
    (X a) ◁ (PointedVec.dualFiberIso X a).hom ≫
      (β_ (X a) (X a)ᘁ).hom ≫ ε_ (X a) (X a)ᘁ := by
  simp only [unweightedPivotalFiber, Iso.trans_hom, Iso.symm_hom, comp_whiskerRight, assoc]
  rw [bidualFiberIso_inv,
    rightAdjointMate_comp_evaluation (PointedVec.dualFiberIso X a).hom]
  have hx := whisker_exchange (drinfeldIso (X a)).hom (PointedVec.dualFiberIso X a).hom
  dsimp only [doubleDualFunctor] at hx
  rw [← reassoc_of% hx, drinfeldIso_evaluation]

lemma dualPairIso_opposite (X : PointedVec (Additive G)) (a : Additive G) :
    PointedVec.dualPairIso X a (-a) (add_neg_cancel a) =
      Iso.refl (PointedVec.gradedDual X a) := by
  apply Iso.ext
  simp [PointedVec.dualPairIso, PointedVec.dualFiberIso, PointedVec.gradedDual]

open GradedObject.Monoidal

/-- An individual actual cup-cap summand closes to its vector-space
rank, multiplied by the prescribed bidual correction. -/
lemma pivotal_closure_summand (X : CocycleVec ψ) (a : Additive G) :
    η_ (X a) (X a)ᘁ ≫ (X a) ◁ (PointedVec.dualFiberIso X a).inv ≫
      ιTensorObj X (PointedVec.gradedDual X) a (-a) 0 (add_neg_cancel a) ≫
      GradedObject.Monoidal.whiskerRight ((pivotalNatIso ψ).hom.app X)
        (PointedVec.gradedDual X) 0 ≫
      PointedVec.gradedEvaluation (PointedVec.gradedDual X) 0 =
      ((pivotalWeight ψ a : ℂ) * (Module.finrank ℂ (X a) : ℂ)) •
        PointedVec.unitFiberIso.inv := by
  change η_ (X a) (X a)ᘁ ≫ (X a) ◁ (PointedVec.dualFiberIso X a).inv ≫
    ιTensorObj X (PointedVec.gradedDual X) a (-a) 0 (add_neg_cancel a) ≫
    GradedObject.Monoidal.tensorHom ((pivotalNatIso ψ).hom.app X) (𝟙 (PointedVec.gradedDual X)) 0 ≫ _ = _
  rw [ι_tensorHom_assoc]
  change η_ (X a) (X a)ᘁ ≫ (X a) ◁ (PointedVec.dualFiberIso X a).inv ≫
    (((pivotalWeight ψ a : ℂ) • (unweightedPivotalFiber ψ X a).hom) ⊗ₘ
      𝟙 (PointedVec.gradedDual X (-a))) ≫
    ιTensorObj (PointedVec.gradedDual (PointedVec.gradedDual X))
      (PointedVec.gradedDual X) a (-a) 0 (add_neg_cancel a) ≫ _ = _
  rw [PointedVec.inclusion_evaluation_zero, dualPairIso_opposite]
  simp only [Iso.refl_hom, id_whiskerRight, id_comp, tensorHom_id,
    MonoidalLinear.smul_whiskerRight, Linear.comp_smul, Linear.smul_comp]
  rw [unweightedPivotalFiber_evaluation_assoc]
  simp only [← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, id_comp]
  rw [PointedVec.vector_braidedDimension_assoc]
  simp only [Linear.smul_comp, id_comp, smul_smul]

/-- The actual twisted cup closes against the weighted bidual map to the
sum of the actual homogeneous vector-space ranks. -/
lemma pivotal_closure (X : CocycleVec ψ) :
    PivotalCriterion.closure ((pivotalNatIso ψ).hom.app X) =
      (∑ a, (Module.finrank ℂ (X a) : ℂ)) • 𝟙 (𝟙_ (CocycleVec ψ)) := by
  funext k
  by_cases hk : k = 0
  · subst k
    change (twistedCoevaluation (fun (a b c : Additive G) =>
      ψ.val a.toMul b.toMul c.toMul) X) 0 ≫
      GradedObject.Monoidal.whiskerRight ((pivotalNatIso ψ).hom.app X)
        (PointedVec.gradedDual X) 0 ≫
      PointedVec.gradedEvaluation (PointedVec.gradedDual X) 0 = _
    simp only [twistedCoevaluation, PointedVec.mapFromUnit_zero, twistedCoevaluationZero,
      assoc, Preadditive.sum_comp, Preadditive.comp_sum, Linear.smul_comp]
    simp only [pivotal_closure_summand, Linear.comp_smul, smul_smul, Iso.hom_inv_id]
    have hc (a : Additive G) :
        cupWeight (fun (a b c : Additive G) => ψ.val a.toMul b.toMul c.toMul) a *
          ((pivotalWeight ψ a : ℂ) * (Module.finrank ℂ (X a) : ℂ)) =
          (Module.finrank ℂ (X a) : ℂ) := by
      simp [cupWeight, pivotalWeight, ← mul_assoc]
    simp only [hc]
    rw [← Finset.sum_smul]
    rfl
  · have hz : IsZero ((𝟙_ (CocycleVec ψ)) k) :=
      (GradedObject.Monoidal.isInitialTensorUnitApply k hk).isZero
    exact hz.eq_of_src _ _

lemma homogeneousFiber_finrank (a k : Additive G) :
    Module.finrank ℂ (PointedVec.simpleObject (Additive G) a k) = if k = a then 1 else 0 := by
  by_cases hk : k = a
  · subst k
    rw [if_pos rfl, ← LinearEquiv.finrank_eq
      (FGModuleCat.isoToLinearEquiv (PointedVec.simpleFiberIso (Additive G) a)).symm]
    exact Module.finrank_self ℂ
  · rw [if_neg hk]
    have hz := PointedVec.simpleFiber_isZero (Additive G) a k hk
    have hz' : IsZero ((PointedVec.simpleObject (Additive G) a k).obj) :=
      (forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)).map_isZero hz
    letI : Subsingleton (PointedVec.simpleObject (Additive G) a k) :=
      ModuleCat.isZero_iff_subsingleton.mp hz'
    exact Module.finrank_zero_of_subsingleton

/-- The normalized actual cup-cap closure on each homogeneous line is one. -/
lemma pivotal_closure_homogeneous (a : Additive G) :
    PivotalCriterion.closure ((pivotalNatIso ψ).hom.app ((skeleton ψ).simpleObject a)) =
      𝟙 (𝟙_ (CocycleVec ψ)) := by
  rw [pivotal_closure]
  change (∑ k, (Module.finrank ℂ (PointedVec.simpleObject (Additive G) a k) : ℂ)) • _ = _
  simp [homogeneousFiber_finrank]

/-- Every actual categorical simple has the normalized actual closure. -/
lemma pivotal_closure_simple (X : CocycleVec ψ) [Simple X] :
    PivotalCriterion.closure ((pivotalNatIso ψ).hom.app X) = 𝟙 (𝟙_ (CocycleVec ψ)) := by
  obtain ⟨a, ⟨e⟩⟩ := (skeleton ψ).simple_isomorphic_representative X
  rw [PivotalCriterion.closure_iso (pivotalNatIso ψ) e]
  exact pivotal_closure_homogeneous ψ a

end Paper18.Category.QuasiFusion.CocycleVec

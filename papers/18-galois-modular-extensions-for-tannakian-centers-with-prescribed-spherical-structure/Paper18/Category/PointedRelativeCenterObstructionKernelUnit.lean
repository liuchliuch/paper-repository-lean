import Paper18.Category.PointedRelativeCenterObstructionKernelCoherence

/-! # Actual unit coherence of kernel restriction -/
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 2000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
namespace Paper18.Category.PointedRelativeCenterObstruction
open GradedObject.Monoidal
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G] (p : Γ →* G)
local notation "K" => p.ker
local notation "F" => kernelRestriction p
local instance kernelUnitDecidableEq : DecidableEq (Additive K) := Classical.typeDecidableEq _
local instance ambientUnitDecidableEq : DecidableEq (Additive Γ) := Classical.typeDecidableEq _

lemma kernelTensorHom_left_unitality (X : NeutralVec.{0} p) :
    (λ_ ((F).obj X)).hom =
      (kernelUnitIso p).hom ▷ (F).obj X ≫ kernelTensorHom p (𝟙_ (NeutralVec p)) X ≫
        (F).map (λ_ X).hom := by
  apply GradedObject.hom_ext
  intro k
  apply tensorObj_ext
  intro a b hab
  by_cases ha : a = 0
  · subst a
    have hb : b = k := by simpa only [zero_add] using hab
    cases hb
    change ιTensorObj (𝟙_ (PointedVec.{0} (Additive K))) ((F).obj X) 0 k k (zero_add k) ≫
      (GradedObject.Monoidal.leftUnitor ((F).obj X)).hom k =
      ιTensorObj (𝟙_ (PointedVec.{0} (Additive K))) ((F).obj X) 0 k k (zero_add k) ≫
        GradedObject.Monoidal.tensorHom (kernelUnitIso p).hom (𝟙 ((F).obj X)) k ≫
          kernelTensorHom p (𝟙_ (NeutralVec p)) X k ≫
            (GradedObject.Monoidal.leftUnitor X.obj).hom (kernelDegree p k)
    have ht := PointedVec.inclusion_leftUnitor ((F).obj X) k
    have hs := PointedVec.inclusion_leftUnitor X.obj (kernelDegree p k)
    rw [ht]
    erw [ι_tensorHom_assoc (kernelUnitIso p).hom (𝟙 ((F).obj X)) 0 k k (zero_add k),
      kernelTensorHom_ι_assoc p (𝟙_ (NeutralVec p)) X 0 k k (zero_add k)]
    rw [kernelUnitIso_hom_zero]
    erw [hs]
    simp only [PointedVec.id_apply, kernelRestriction, kernelDegree,
      MonoidalCategory.tensorHom_id, comp_whiskerRight, Category.assoc,
      ← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]

  · have h0 : IsZero ((𝟙_ (PointedVec.{0} (Additive K))) a) := by
      change IsZero ((PointedVec.simpleObject (Additive K) 0) a)
      exact PointedVec.simpleFiber_isZero (Additive K) 0 a ha
    exact ((tensorRight (((F).obj X) b)).map_isZero h0).eq_of_src _ _

lemma kernelTensorHom_right_unitality (X : NeutralVec.{0} p) :
    (ρ_ ((F).obj X)).hom =
      (F).obj X ◁ (kernelUnitIso p).hom ≫ kernelTensorHom p X (𝟙_ (NeutralVec p)) ≫
        (F).map (ρ_ X).hom := by
  apply GradedObject.hom_ext
  intro k
  apply tensorObj_ext
  intro a b hab
  by_cases hb : b = 0
  · subst b
    have ha : a = k := by simpa only [add_zero] using hab
    cases ha
    change ιTensorObj ((F).obj X) (𝟙_ (PointedVec.{0} (Additive K))) k 0 k (add_zero k) ≫
      (GradedObject.Monoidal.rightUnitor ((F).obj X)).hom k =
      ιTensorObj ((F).obj X) (𝟙_ (PointedVec.{0} (Additive K))) k 0 k (add_zero k) ≫
        GradedObject.Monoidal.tensorHom (𝟙 ((F).obj X)) (kernelUnitIso p).hom k ≫
          kernelTensorHom p X (𝟙_ (NeutralVec p)) k ≫
            (GradedObject.Monoidal.rightUnitor X.obj).hom (kernelDegree p k)
    have ht := PointedVec.inclusion_rightUnitor ((F).obj X) k
    have hs := PointedVec.inclusion_rightUnitor X.obj (kernelDegree p k)
    rw [ht]
    erw [ι_tensorHom_assoc (𝟙 ((F).obj X)) (kernelUnitIso p).hom k 0 k (add_zero k),
      kernelTensorHom_ι_assoc p X (𝟙_ (NeutralVec p)) k 0 k (add_zero k)]
    rw [kernelUnitIso_hom_zero]
    erw [hs]
    simp only [PointedVec.id_apply, kernelRestriction, kernelDegree,
      MonoidalCategory.id_tensorHom, whiskerLeft_comp, Category.assoc,
      ← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]

  · have h0 : IsZero ((𝟙_ (PointedVec.{0} (Additive K))) b) := by
      change IsZero ((PointedVec.simpleObject (Additive K) 0) b)
      exact PointedVec.simpleFiber_isZero (Additive K) 0 b hb
    exact ((tensorLeft (((F).obj X) a)).map_isZero h0).eq_of_src _ _

end Paper18.Category.PointedRelativeCenterObstruction

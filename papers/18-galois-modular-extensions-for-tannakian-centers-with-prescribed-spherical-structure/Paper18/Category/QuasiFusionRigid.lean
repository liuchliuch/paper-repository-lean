import Paper18.Category.QuasiFusionDualExpansion

/-! # Actual rigidity of cocycle-twisted graded vector spaces -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace Paper18.Category.QuasiFusion
variable {A : Type} [Fintype A] [AddGroup A]
local instance rigidBaseMonoidal : MonoidalCategory (GradedObject A (FGModuleCat ℂ)) :=
  GradedObject.monoidalCategory

variable (r : A → A → A → ℂˣ)
  (hr : ∀ a b c d, r b c d * r a (b + c) d * r a b c =
    r (a + b) c d * r a b (c + d)) (h₀ : ∀ a c, r a 0 c = 1)
  (hinv : ∀ a, r (-a) a (-a) * r a (-a) a = 1)

/-- The prescribed weighted cup and the ordinary cap are an actual exact
pairing for the actual twisted associator. -/
def scalarExactPairing (X : PointedVec A) :
    letI := scalarMonoidalCategory r hr h₀
    ExactPairing X (PointedVec.gradedDual X) := by
  letI := scalarMonoidalCategory r hr h₀
  refine
    { coevaluation' := twistedCoevaluation r X
      evaluation' := PointedVec.gradedEvaluation X
      evaluation_coevaluation' := ?_
      coevaluation_evaluation' := ?_ }
  · change GradedObject.Monoidal.whiskerLeft (PointedVec.gradedDual X) (twistedCoevaluation r X) ≫
        (scalarAssociator r (PointedVec.gradedDual X) X (PointedVec.gradedDual X)).inv ≫
        GradedObject.Monoidal.whiskerRight (PointedVec.gradedEvaluation X) (PointedVec.gradedDual X) =
      (GradedObject.Monoidal.rightUnitor (PointedVec.gradedDual X)).hom ≫
        (GradedObject.Monoidal.leftUnitor (PointedVec.gradedDual X)).inv
    apply (cancel_epi (GradedObject.Monoidal.rightUnitor (PointedVec.gradedDual X)).inv).mp
    apply (cancel_mono (GradedObject.Monoidal.leftUnitor (PointedVec.gradedDual X)).hom).mp
    simpa only [twistedLeftSnake, assoc, Iso.inv_hom_id, Iso.hom_inv_id,
      id_comp, comp_id] using twistedLeftSnake_eq_id r hinv X

  · change GradedObject.Monoidal.whiskerRight (twistedCoevaluation r X) X ≫
        (scalarAssociator r X (PointedVec.gradedDual X) X).hom ≫
        GradedObject.Monoidal.whiskerLeft X (PointedVec.gradedEvaluation X) =
      (GradedObject.Monoidal.leftUnitor X).hom ≫ (GradedObject.Monoidal.rightUnitor X).inv
    apply (cancel_epi (GradedObject.Monoidal.leftUnitor X).inv).mp
    apply (cancel_mono (GradedObject.Monoidal.rightUnitor X).hom).mp
    simpa only [twistedRightSnake, assoc, Iso.inv_hom_id, Iso.hom_inv_id,
      id_comp, comp_id] using twistedRightSnake_eq_id r X

/-- Right duals in the actual twisted convolution category are the actual
degree-inverted vector-space duals, with the proved weighted pairing. -/
def scalarRightRigid :
    letI := scalarMonoidalCategory r hr h₀
    RightRigidCategory (PointedVec A) := by
  letI := scalarMonoidalCategory r hr h₀
  exact { rightDual := fun X =>
    { rightDual := PointedVec.gradedDual X
      exact := scalarExactPairing r hr h₀ hinv X } }

variable {G : Type} [Group G] [Fintype G]

/-- An actual normalized third cocycle yields an actual rigid twisted
graded-vector-space monoidal category. -/
def twistedRightRigid (ψ : ThreeCocycle G) :
    letI := twistedMonoidalCategory ψ
    RightRigidCategory (PointedVec (Additive G)) :=
  scalarRightRigid (A := Additive G) (fun (a b c : Additive G) => ψ.val a.toMul b.toMul c.toMul)
    (fun (a b c d : Additive G) => ψ.pentagon a.toMul b.toMul c.toMul d.toMul)
    (fun (a c : Additive G) => ψ.one₂ a.toMul c.toMul)
    (fun (a : Additive G) => ψ.inverse_pair a.toMul)

end Paper18.Category.QuasiFusion

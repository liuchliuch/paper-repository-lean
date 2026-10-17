import Paper18.Category.LinearMatMonoidalRigid
import Paper18.Category.PivotalBalancing

/-! # Extending actual balancing and rigid mates to the additive envelope -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u
namespace Paper18.Category.LinearMat
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C] [RightRigidCategory C] [BraidedCategory C]

set_option maxRecDepth 3000 in
/-- The chosen rigid mate of an actual finite matrix is the transpose
matrix of the actual rigid mates. -/
lemma dualMap_apply {X Y : Mat_ C} (f : X ⟶ Y) (i : Y.ι) (j : X.ι) :
    (dualMap (Mat_ C) f) i j = dualMap C (f j i) := by
  let g : dual (Mat_ C) Y ⟶ dual (Mat_ C) X := fun a b => dualMap C (f b a)
  have hg : dualMap (Mat_ C) f = g := by
    apply pairing_hom_ext (inferInstanceAs (ExactPairing X (dual (Mat_ C) X)))
    rw [rightAdjointMate_comp_evaluation]
    ext ⟨a,b⟩ ⟨⟩
    change (∑ p : Y.ι × Y.ι,
        ((𝟙 (dualObject Y)) a p.1 ⊗ₘ f b p.2) ≫ evaluation Y p PUnit.unit) =
      ∑ p : X.ι × X.ι,
        (dualMap C (f p.1 a) ⊗ₘ (𝟙 X) b p.2) ≫ evaluation X p PUnit.unit
    simp only [Fintype.sum_prod_type, evaluation, Mat_.id_apply]
    simp only [apply_ite, apply_dite, dite_comp, comp_dite,
      MonoidalPreadditive.zero_tensor, MonoidalPreadditive.tensor_zero,
      zero_comp, comp_zero]
    simp
    change (∑ x : Y.ι, (((𝟙 (dualObject Y)) a x) ⊗ₘ f b x) ≫
      ε_ (Y.X x) (Y.X x)ᘁ) = _
    have hs : (∑ x : Y.ι, (((𝟙 (dualObject Y)) a x) ⊗ₘ f b x) ≫
        ε_ (Y.X x) (Y.X x)ᘁ) =
        (((𝟙 (dualObject Y)) a a) ⊗ₘ f b a) ≫ ε_ (Y.X a) (Y.X a)ᘁ :=
      Finset.sum_eq_single a (by
        intro k _ hk
        simp [Mat_.id_apply, Ne.symm hk]) (by simp)
    apply hs.trans
    simpa [Mat_.id_apply] using
        (rightAdjointMate_comp_evaluation (f b a)).symm
  exact congrFun (congrFun hg i) j

variable (θ : 𝟭 C ≅ 𝟭 C)

def matrixTwist : 𝟭 (Mat_ C) ≅ 𝟭 (Mat_ C) :=
  NatIso.ofComponents (fun X => indexEquivIso (Equiv.refl X.ι) (fun i => θ.app (X.X i)))
    (fun {X Y} f => by
      change f ≫ indexEquivHom (Equiv.refl Y.ι) (fun i => θ.hom.app (Y.X i)) =
        indexEquivHom (Equiv.refl X.ι) (fun i => θ.hom.app (X.X i)) ≫ f
      ext i j
      have h := comp_indexEquivHom_apply f (Equiv.refl Y.ι)
        (fun i => θ.hom.app (Y.X i)) i j
      exact h.trans ((θ.hom.naturality (f i j)).trans
        (indexEquivHom_comp_apply (Equiv.refl X.ι)
          (fun i => θ.hom.app (X.X i)) f i j).symm))

lemma matrixTwist_hom (X : Mat_ C) :
    (matrixTwist θ).hom.app X =
      indexEquivHom (Equiv.refl X.ι) (fun i => θ.hom.app (X.X i)) := rfl

lemma matrixTwist_unit (hu : θ.hom.app (𝟙_ C) = 𝟙 (𝟙_ C)) :
    (matrixTwist θ).hom.app (𝟙_ (Mat_ C)) = 𝟙 (𝟙_ (Mat_ C)) := by
  change indexEquivHom _ _ = _
  ext ⟨⟩ ⟨⟩
  simpa [indexEquivHom, Mat_.id_apply] using hu

lemma matrixTwist_tensor
    (ht : ∀ X Y : C, θ.hom.app (X ⊗ Y) =
      (doubleBraiding X Y).hom ≫ (θ.hom.app X ⊗ₘ θ.hom.app Y))
    (X Y : Mat_ C) :
    (matrixTwist θ).hom.app (X ⊗ Y) = (doubleBraiding X Y).hom ≫
      ((matrixTwist θ).hom.app X ⊗ₘ (matrixTwist θ).hom.app Y) := by
  simp only [matrixTwist_hom, doubleBraiding, Iso.trans_hom]
  change indexEquivHom _ _ =
    ((braidingIso X Y).hom ≫ (braidingIso Y X).hom) ≫ _
  simp only [braidingIso, indexEquivIso_hom, tensorMap_indexEquivHom,
    indexEquivHom_comp]
  congr 1
  funext p
  exact ht (X.X p.1) (Y.X p.2)

/-- A proved actual balancing on the original category supplies a
coherent actual pivotal structure on its finite additive envelope. -/
def matrixPivotal (hu : θ.hom.app (𝟙_ C) = 𝟙 (𝟙_ C))
    (ht : ∀ X Y : C, θ.hom.app (X ⊗ Y) =
      (doubleBraiding X Y).hom ≫ (θ.hom.app X ⊗ₘ θ.hom.app Y)) :
    PivotalStructure (Mat_ C) :=
  pivotalOfBalancing (matrixTwist θ) (matrixTwist_unit θ hu) (matrixTwist_tensor θ ht)

@[simp] lemma matrixPivotal_twist (hu ht) :
    (matrixPivotal θ hu ht).twistNatIso = matrixTwist θ :=
  pivotalOfBalancing_twist _ _ _

lemma matrixTwist_dual
    (hd : ∀ X : C, θ.hom.app (dual C X) = dualMap C (θ.hom.app X))
    (X : Mat_ C) :
    (matrixTwist θ).hom.app (dual (Mat_ C) X) =
      dualMap (Mat_ C) ((matrixTwist θ).hom.app X) := by
  ext i j
  rw [dualMap_apply]
  by_cases hij : i = j
  · subst j
    simpa [matrixTwist_hom, indexEquivHom] using hd (X.X i)
  · simp [matrixTwist_hom, indexEquivHom, hij, Ne.symm hij, dualMap, rightAdjointMate]

end Paper18.Category.LinearMat

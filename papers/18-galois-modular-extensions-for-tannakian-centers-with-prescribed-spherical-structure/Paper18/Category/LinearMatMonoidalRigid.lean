import Paper18.Category.LinearMatMonoidalBraided
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-! # Actual right duals in the finite matrix additive envelope -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u
namespace Paper18.Category.LinearMat
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C]

@[simp] lemma leftUnitor_inv (X : Mat_ C) :
    (λ_ X).inv = indexEquivHom (X := X) (Y := (𝟙_ (Mat_ C)) ⊗ X)
      (Equiv.punitProd X.ι).symm (fun i => (λ_ (X.X i)).inv) := by
  change (leftUnitorIso X).inv = _
  rw [leftUnitorIso, indexEquivIso_inv]
  congr 1
  funext i
  simp

@[simp] lemma rightUnitor_inv (X : Mat_ C) :
    (ρ_ X).inv = indexEquivHom (X := X) (Y := X ⊗ (𝟙_ (Mat_ C)))
      (Equiv.prodPUnit X.ι).symm (fun i => (ρ_ (X.X i)).inv) := by
  change (rightUnitorIso X).inv = _
  rw [rightUnitorIso, indexEquivIso_inv]
  congr 1
  funext i
  simp

variable [RightRigidCategory C]
attribute [local instance 2000] RightRigidCategory.rightDual

/-- The chosen dual has the same actual finite indices and dual fibers. -/
abbrev dualObject (X : Mat_ C) : Mat_ C := ⟨X.ι, fun i => (X.X i)ᘁ⟩

/-- Coevaluation is the diagonal matrix of the actual fiber coevaluations. -/
def coevaluation (X : Mat_ C) : 𝟙_ (Mat_ C) ⟶ X ⊗ dualObject X := fun _ p =>
  if h : p.1 = p.2 then (η_ (X.X p.1) (X.X p.1)ᘁ) ≫
    eqToHom (congrArg (fun i => X.X p.1 ⊗ (X.X i)ᘁ) h) else 0

/-- Evaluation is the diagonal matrix of the actual fiber evaluations. -/
def evaluation (X : Mat_ C) : dualObject X ⊗ X ⟶ 𝟙_ (Mat_ C) := fun p _ =>
  if h : p.1 = p.2 then
    eqToHom (congrArg (fun i => (X.X i)ᘁ ⊗ X.X p.2) h) ≫
      (ε_ (X.X p.2) (X.X p.2)ᘁ) else 0

@[simp] lemma coevaluation_diagonal (X : Mat_ C) (i : X.ι) :
    coevaluation X PUnit.unit (i,i) = η_ (X.X i) (X.X i)ᘁ := by simp [coevaluation]

@[simp] lemma evaluation_diagonal (X : Mat_ C) (i : X.ι) :
    evaluation X (i,i) PUnit.unit = ε_ (X.X i) (X.X i)ᘁ := by simp [evaluation]

set_option maxRecDepth 3000 in
lemma evaluation_coevaluation (X : Mat_ C) :
    coevaluation X ▷ X ≫ (α_ X (dualObject X) X).hom ≫ X ◁ evaluation X =
      (λ_ X).hom ≫ (ρ_ X).inv := by
  rw [associator_hom, leftUnitor_hom, rightUnitor_inv, indexEquivHom_comp]
  ext ⟨⟨⟩,i⟩ ⟨j,⟨⟩⟩
  rw [Mat_.comp_apply]
  simp only [indexEquivHom_comp_apply]
  change (∑ p : (X.ι × X.ι) × X.ι,
    (coevaluation X PUnit.unit p.1 ⊗ₘ (𝟙 X) i p.2) ≫
      (α_ (X.X p.1.1) (X.X p.1.2)ᘁ (X.X p.2)).hom ≫
      ((𝟙 X) p.1.1 j ⊗ₘ evaluation X (p.1.2,p.2) PUnit.unit)) = _
  by_cases hij : i = j
  · subst j
    simp [Fintype.sum_prod_type, coevaluation, evaluation, Mat_.id_apply,
      tensorHom_def, dite_comp, comp_dite, apply_dite, indexEquivHom]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  · simp [Fintype.sum_prod_type, coevaluation, evaluation, Mat_.id_apply,
      tensorHom_def, dite_comp, comp_dite, apply_dite, indexEquivHom, hij]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : b = i
    · subst b; simp [hij]
    · simp [hb]

set_option maxRecDepth 3000 in
lemma coevaluation_evaluation (X : Mat_ C) :
    dualObject X ◁ coevaluation X ≫ (α_ (dualObject X) X (dualObject X)).inv ≫
      evaluation X ▷ dualObject X = (ρ_ (dualObject X)).hom ≫ (λ_ (dualObject X)).inv := by
  rw [associator_inv, rightUnitor_hom, leftUnitor_inv, indexEquivHom_comp]
  ext ⟨i,⟨⟩⟩ ⟨⟨⟩,j⟩
  rw [Mat_.comp_apply]
  simp only [indexEquivHom_comp_apply]
  change (∑ p : X.ι × (X.ι × X.ι),
    ((𝟙 (dualObject X)) i p.1 ⊗ₘ coevaluation X PUnit.unit p.2) ≫
      (α_ (X.X p.1)ᘁ (X.X p.2.1) (X.X p.2.2)ᘁ).inv ≫
      (evaluation X (p.1,p.2.1) PUnit.unit ⊗ₘ (𝟙 (dualObject X)) p.2.2 j)) = _
  by_cases hij : i = j
  · subst j
    simp [Fintype.sum_prod_type, coevaluation, evaluation, Mat_.id_apply,
      tensorHom_def, dite_comp, comp_dite, apply_dite, indexEquivHom]
  · simp [Fintype.sum_prod_type, coevaluation, evaluation, Mat_.id_apply,
      tensorHom_def, dite_comp, comp_dite, apply_dite, indexEquivHom, hij]

instance exactPairing (X : Mat_ C) : ExactPairing X (dualObject X) where
  coevaluation' := coevaluation X
  evaluation' := evaluation X
  coevaluation_evaluation' := coevaluation_evaluation X
  evaluation_coevaluation' := evaluation_coevaluation X

instance rightRigidCategory : RightRigidCategory (Mat_ C) where
  rightDual X := ⟨dualObject X⟩

end Paper18.Category.LinearMat

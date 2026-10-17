import Paper18.Category.TensorCharacters
import Paper18.Category.PivotalDimension
import Paper18.Fusion.Grading

/-!
# Comparing actual spherical structures

The quotient of two pivotal identifications is an actual monoidal natural
automorphism of the identity. Its scalar on a simple scales the right trace,
while its inverse scales the left trace. Sphericality and nonzero simple
dimensions therefore force a sign, without assuming any character laws.
-/

noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual

namespace PivotalStructure
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  (J K : PivotalStructure C)

/-- Quotient of two actual pivotal identifications, as a natural isomorphism. -/
def ratio : 𝟭 C ≅ 𝟭 C := J.j ≪≫ K.j.symm

@[simp] lemma ratio_hom_app (X : C) :
    (J.ratio K).hom.app X = J.j.hom.app X ≫ K.j.inv.app X := rfl

@[simp] lemma ratio_inv_app (X : C) :
    (J.ratio K).inv.app X = K.j.hom.app X ≫ J.j.inv.app X := rfl

/-- Canonical pivotal tensor coherence forces the quotient to be monoidal. -/
instance ratio_isMonoidal : NatTrans.IsMonoidal (J.ratio K).hom where
  unit := by
    change 𝟙 (𝟙_ C) ≫ (J.j.hom.app (𝟙_ C) ≫ K.j.inv.app (𝟙_ C)) = 𝟙 (𝟙_ C)
    rw [id_comp, J.unit, ← K.unit]
    exact K.j.hom_inv_id_app _
  tensor X Y := by
    change 𝟙 (X ⊗ Y) ≫ (J.j.hom.app (X ⊗ Y) ≫ K.j.inv.app (X ⊗ Y)) =
      ((J.j.hom.app X ≫ K.j.inv.app X) ⊗ₘ
        (J.j.hom.app Y ≫ K.j.inv.app Y)) ≫ 𝟙 (X ⊗ Y)
    apply (cancel_mono (K.j.hom.app (X ⊗ Y))).1
    calc
      _ = J.j.hom.app (X ⊗ Y) := by simp only [id_comp, assoc, K.j.inv_hom_id_app, comp_id]
      _ = (J.j.hom.app X ⊗ₘ J.j.hom.app Y) ≫ doubleDualTensorHom C X Y := J.tensor X Y
      _ = (((J.j.hom.app X ≫ K.j.inv.app X) ≫ K.j.hom.app X) ⊗ₘ
          ((J.j.hom.app Y ≫ K.j.inv.app Y) ≫ K.j.hom.app Y)) ≫
          doubleDualTensorHom C X Y := by simp only [assoc, K.j.inv_hom_id_app, comp_id]
      _ = _ := by
        simp only [K.tensor, ← tensorHom_comp_tensorHom, Category.assoc]
        exact congrArg (fun f =>
          (J.j.hom.app X ⊗ₘ J.j.hom.app Y) ≫
          (K.j.inv.app X ⊗ₘ K.j.inv.app Y) ≫ f)
          (Category.id_comp ((K.j.hom.app X ⊗ₘ K.j.hom.app Y) ≫ doubleDualTensorHom C X Y)).symm


variable [Preadditive C] [Linear ℂ C] [HasKernels C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]

/-- The comparison scalar is extracted from an actual component by Schur. -/
def comparisonScalar (X : C) [Simple X] : ℂ :=
  TensorAutomorphism.scalar (J.ratio K) X

lemma comparisonScalar_ne_zero (X : C) [Simple X] : J.comparisonScalar K X ≠ 0 :=
  TensorAutomorphism.scalar_ne_zero (J.ratio K) X

lemma pivotal_hom_eq_smul (X : C) [Simple X] :
    J.j.hom.app X = J.comparisonScalar K X • K.j.hom.app X := by
  have hs := TensorAutomorphism.scalar_spec (J.ratio K) X
  have ht := congrArg (fun f => f ≫ K.j.hom.app X) hs
  simpa [comparisonScalar, assoc] using ht.symm

lemma pivotal_inv_eq_inv_smul (X : C) [Simple X] :
    J.j.inv.app X = (J.comparisonScalar K X)⁻¹ • K.j.inv.app X := by
  have hs := TensorAutomorphism.scalar_spec (J.ratio K).symm X
  rw [TensorAutomorphism.inv_scalar] at hs
  have ht := congrArg (fun f => K.j.inv.app X ≫ f) hs
  simpa [comparisonScalar, assoc] using ht.symm

variable [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Changing the pivotal identification scales the actual right trace. -/
lemma rightTrace_comparison {X : C} [Simple X] (f : X ⟶ X) :
    J.rightTrace f = J.comparisonScalar K X • K.rightTrace f := by
  simp [rightTrace, leftEvaluation, J.pivotal_hom_eq_smul K X]

/-- The actual left trace acquires the inverse scalar. -/
lemma leftTrace_comparison {X : C} [Simple X] (f : X ⟶ X) :
    J.leftTrace f = (J.comparisonScalar K X)⁻¹ • K.leftTrace f := by
  simp [leftTrace, leftCoevaluation, J.pivotal_inv_eq_inv_smul K X]

variable [Simple (𝟙_ C)]

lemma rightDim_comparison (X : C) [Simple X] :
    J.rightDim X = J.comparisonScalar K X * K.rightDim X := by
  simp only [rightDim, rightDimension, J.rightTrace_comparison K, map_smul,
    smul_eq_mul]

lemma leftDim_comparison (X : C) [Simple X] :
    J.leftDim X = (J.comparisonScalar K X)⁻¹ * K.leftDim X := by
  simp only [leftDim, leftDimension, J.leftTrace_comparison K, map_smul,
    smul_eq_mul]

variable [HasFiniteBiproducts C] {ι : Type w} [Fintype ι]
  (S : FiniteSemisimpleSkeleton C ι)
include S

/-- Sphericality compares the right and left trace transformation laws;
nonvanishing of the actual simple dimension permits cancellation. -/
lemma comparisonScalar_eq_inv (hJ : J.Spherical) (hK : K.Spherical)
    (X : C) [Simple X] : J.comparisonScalar K X = (J.comparisonScalar K X)⁻¹ := by
  apply mul_right_cancel₀ (K.rightDim_ne_zero S X)
  calc
    J.comparisonScalar K X * K.rightDim X = J.rightDim X := (J.rightDim_comparison K X).symm
    _ = J.leftDim X := (J.leftDim_eq_rightDim hJ X).symm
    _ = (J.comparisonScalar K X)⁻¹ * K.leftDim X := J.leftDim_comparison K X
    _ = (J.comparisonScalar K X)⁻¹ * K.rightDim X := by rw [K.leftDim_eq_rightDim hK X]

/-- The comparison between any two actual spherical structures is a sign. -/
lemma comparisonScalar_sign (hJ : J.Spherical) (hK : K.Spherical)
    (X : C) [Simple X] : J.comparisonScalar K X = 1 ∨ J.comparisonScalar K X = -1 := by
  have hq : J.comparisonScalar K X ^ 2 = 1 := by
    calc
      _ = J.comparisonScalar K X * (J.comparisonScalar K X)⁻¹ := by
        rw [pow_two]
        exact congrArg (fun c => J.comparisonScalar K X * c) (J.comparisonScalar_eq_inv K S hJ hK X)
      _ = 1 := mul_inv_cancel₀ (J.comparisonScalar_ne_zero K X)
  exact (sq_eq_one_iff).mp hq

lemma comparisonScalar_eq_dimension_ratio (X : C) [Simple X] :
    J.comparisonScalar K X = J.rightDim X / K.rightDim X := by
  apply (eq_div_iff (K.rightDim_ne_zero S X)).mpr
  exact (J.rightDim_comparison K X).symm

/-- The comparison character inverts under actual chosen rigid duality. -/
lemma comparisonScalar_dualLabel (i : ι) :
    J.comparisonScalar K (S.simpleObject (S.dualLabel i)) =
      (J.comparisonScalar K (S.simpleObject i))⁻¹ :=
  TensorAutomorphism.scalar_dualLabel (J.ratio K) S i

/-- Sphericality forces the comparison character to agree on duals. -/
lemma comparisonScalar_dual_eq (hJ : J.Spherical) (hK : K.Spherical) (i : ι) :
    J.comparisonScalar K (S.simpleObject (S.dualLabel i)) =
      J.comparisonScalar K (S.simpleObject i) := by
  rw [J.comparisonScalar_dualLabel K S,
    ← J.comparisonScalar_eq_inv K S hJ hK (S.simpleObject i)]

omit [Simple (𝟙_ C)] in
/-- Multiplication on every categorical fusion constituent is a theorem. -/
lemma comparisonScalar_fusion (i j k : ι) (h : 0 < S.fusionCoeff i j k) :
    J.comparisonScalar K (S.simpleObject k) =
      J.comparisonScalar K (S.simpleObject i) * J.comparisonScalar K (S.simpleObject j) :=
  TensorAutomorphism.scalar_fusion (J.ratio K) S i j k h

/-- The sign character used in the paper, now extracted from actual pivotal
structures instead of given as numerical input. -/
def signCharacter (hJ : J.Spherical) (hK : K.Spherical) : Paper18.SignCharacter S.fusionBasis where
  val i := J.comparisonScalar K (S.simpleObject i)
  val_mem i := J.comparisonScalar_sign K S hJ hK (S.simpleObject i)
  val_one := TensorAutomorphism.scalar_unitLabel (J.ratio K) S
  val_dual i := TensorAutomorphism.scalar_dualLabel (J.ratio K) S i
  val_tensor i j k h := J.comparisonScalar_fusion K S i j k h

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] [Simple (𝟙_ C)] in
/-- Equality of the comparison scalars at actual simple representatives
determines equality of the entire pivotal structures. -/
lemma eq_of_comparisonScalar_eq_one
    (h : ∀ i, J.comparisonScalar K (S.simpleObject i) = 1) : J = K := by
  have hr : J.ratio K = Iso.refl (𝟭 C) :=
    TensorAutomorphism.ext_simple (J.ratio K) (Iso.refl (𝟭 C)) S (by
      intro i
      simpa only [comparisonScalar, TensorAutomorphism.scalar_refl] using h i)
  have hj : J.j = K.j := by
    ext X
    have hx := congrArg (fun a : 𝟭 C ≅ 𝟭 C => a.hom.app X) hr
    have ht := congrArg (fun f => f ≫ K.j.hom.app X) hx
    simpa only [ratio_hom_app, assoc, K.j.inv_hom_id_app, comp_id,
      Iso.refl_hom, NatTrans.id_app, id_comp] using ht
  cases J
  cases K
  cases hj
  rfl

end PivotalStructure
end Paper18.Category

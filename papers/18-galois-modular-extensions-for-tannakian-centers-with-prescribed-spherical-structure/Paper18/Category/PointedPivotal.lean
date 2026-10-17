import Paper18.Category.PointedRigid
import Paper18.Category.PointedBraiding
import Paper18.Category.PivotalBalancingTensor
import Paper18.Category.PointedTrace

/-!
# The canonical pivotal structure on finite graded vector spaces

The ordinary vector-space flip defines a symmetric braiding on convolution.
Its actual Drinfeld comparison identifies each object with its double dual.
The resulting pivotal structure uses only the underlying monoidal category
and chosen graded duals, so it remains available with any bicharacter braiding.
-/

noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedVec
attribute [local instance 2000] RightRigidCategory.rightDual
variable (A : Type) [Fintype A] [AddCommGroup A]

/-- The trivial bicharacter gives the ordinary flip of homogeneous vectors. -/
def trivialBicharacter : ComplexBicharacter A where
  val _ _ := 1
  add_left _ _ _ := by simp
  add_right _ _ _ := by simp

omit [Fintype A] in
@[simp] lemma trivialBicharacter_val (a b : A) :
    (trivialBicharacter A).val a b = 1 := rfl

/-- The ordinary flip is symmetric on the actual convolution category. -/
def canonicalSymmetricCategory : SymmetricCategory (PointedVec A) where
  toBraidedCategory := bicharacterBraidedCategory (trivialBicharacter A)
  symmetry X Y := by
    apply GradedObject.hom_ext
    intro k
    apply GradedObject.Monoidal.tensorObj_ext
    intro i j h
    change GradedObject.Monoidal.ιTensorObj X Y i j k h ≫
        ((bicharacterBraiding (trivialBicharacter A) X Y).hom k ≫
          (bicharacterBraiding (trivialBicharacter A) Y X).hom k) = _
    simp
    rfl

/-- The canonical double-dual identification, constructed from the actual
graded cups and caps and the ordinary symmetric flip. -/
def canonicalPivotalIso : 𝟭 (PointedVec A) ≅ doubleDualFunctor (PointedVec A) := by
  letI := canonicalSymmetricCategory A
  exact drinfeldNatIso

/-- Its evaluation is the ordinary flip followed by the graded evaluation. -/
lemma canonicalPivotalIso_evaluation (X : PointedVec A) :
    (canonicalPivotalIso A).hom.app X ▷ dual (PointedVec A) X ≫
        ε_ (dual (PointedVec A) X) (dual (PointedVec A) (dual (PointedVec A) X)) =
      (bicharacterBraiding (trivialBicharacter A) X (dual (PointedVec A) X)).hom ≫
        ε_ X (dual (PointedVec A) X) := by
  letI := canonicalSymmetricCategory A
  exact drinfeldIso_evaluation X

/-- Its coevaluation is the ordinary flipped graded coevaluation. -/
lemma canonicalPivotalIso_coevaluation (X : PointedVec A) :
    η_ X (dual (PointedVec A) X) ≫
        (bicharacterBraiding (trivialBicharacter A) (dual (PointedVec A) X) X).inv ≫
        dual (PointedVec A) X ◁ (canonicalPivotalIso A).hom.app X =
      η_ (dual (PointedVec A) X) (dual (PointedVec A) (dual (PointedVec A) X)) := by
  letI := canonicalSymmetricCategory A
  exact drinfeldIso_coevaluation X

/-- The left cup induced by the canonical identification is the flipped
ordinary graded cup. -/
lemma canonicalPivotalIso_leftCoevaluation (X : PointedVec A) :
    η_ (dual (PointedVec A) X) (dual (PointedVec A) (dual (PointedVec A) X)) ≫
        dual (PointedVec A) X ◁ (canonicalPivotalIso A).inv.app X =
      η_ X (dual (PointedVec A) X) ≫
        (bicharacterBraiding (trivialBicharacter A) (dual (PointedVec A) X) X).inv := by
  rw [← canonicalPivotalIso_coevaluation A X]
  simp only [Category.assoc, ← whiskerLeft_comp, Iso.hom_inv_id_app]
  erw [whiskerLeft_id, Category.comp_id]

/-- The actual canonical cups and caps have equal left and right closures
on every endomorphism, by symmetry and naturality of the ordinary flip. -/
lemma canonicalPivotalIso_traces (X : PointedVec A) (f : X ⟶ X) :
    (η_ (dual (PointedVec A) X) (dual (PointedVec A) (dual (PointedVec A) X)) ≫
        dual (PointedVec A) X ◁ (canonicalPivotalIso A).inv.app X) ≫
        dual (PointedVec A) X ◁ f ≫ ε_ X (dual (PointedVec A) X) =
      η_ X (dual (PointedVec A) X) ≫ f ▷ dual (PointedVec A) X ≫
        (canonicalPivotalIso A).hom.app X ▷ dual (PointedVec A) X ≫
        ε_ (dual (PointedVec A) X) (dual (PointedVec A) (dual (PointedVec A) X)) := by
  letI := canonicalSymmetricCategory A
  rw [canonicalPivotalIso_leftCoevaluation A X, Category.assoc,
    canonicalPivotalIso_evaluation A X]
  change η_ X (dual (PointedVec A) X) ≫
      (β_ (dual (PointedVec A) X) X).inv ≫
      dual (PointedVec A) X ◁ f ≫ ε_ X (dual (PointedVec A) X) = _
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding,
    ← BraidedCategory.braiding_naturality_left_assoc]
  rfl

/-- The canonical pivotal structure on finite abelian-group graded vector
spaces. Its unit and tensor laws are the fixed categorical duality laws. -/
def pivotalStructure : PivotalStructure (PointedVec A) where
  j := canonicalPivotalIso A
  unit := by
    letI := canonicalSymmetricCategory A
    exact drinfeldIso_unit
  tensor X Y := by
    letI := canonicalSymmetricCategory A
    have h := drinfeldIso_tensor X Y
    simpa only [doubleBraiding, Iso.trans_hom, SymmetricCategory.symmetry,
      Category.id_comp] using h

@[simp] lemma pivotalStructure_j : (pivotalStructure A).j = canonicalPivotalIso A := rfl

/-- The canonical pivotal structure is spherical on every actual
endomorphism, by the proved symmetry calculation of the cups and caps. -/
theorem pivotalStructure_spherical : (pivotalStructure A).Spherical := by
  intro X f
  exact canonicalPivotalIso_traces A X f

/-- The actual categorical dimension of every homogeneous simple line is one. -/
@[simp] theorem pivotalStructure_rightDimension_simple (a : A) :
    (pivotalStructure A).rightDimension (simpleObject A a) =
      𝟙 (𝟙_ (PointedVec A)) := by
  let X := simpleObject A a
  change gradedCoevaluation X ≫ (𝟙 X) ▷ gradedDual X ≫
    (canonicalPivotalIso A).hom.app X ▷ gradedDual X ≫
      gradedEvaluation (gradedDual X) = _
  rw [id_whiskerRight]
  erw [Category.id_comp]
  erw [canonicalPivotalIso_evaluation A X]
  simpa using simple_braidedDimension (trivialBicharacter A) a

/-- Extracting the scalar from that actual trace gives dimension one. -/
@[simp] theorem pivotalStructure_rightDim_simple (a : A) :
    (pivotalStructure A).rightDim (simpleObject A a) = 1 := by
  unfold PivotalStructure.rightDim
  rw [pivotalStructure_rightDimension_simple, unitScalarEquiv_id]

/-- Positivity follows from the actual simple decomposition and the computed
categorical simple dimensions. -/
theorem pivotalStructure_positive : (pivotalStructure A).Positive := by
  intro X hX
  letI := hX
  obtain ⟨a, ⟨e⟩⟩ := (skeleton A).simple_isomorphic_representative X
  rw [(pivotalStructure A).rightDim_iso e]
  change 0 < ((pivotalStructure A).rightDim (simpleObject A a)).re ∧
    ((pivotalStructure A).rightDim (simpleObject A a)).im = 0
  rw [pivotalStructure_rightDim_simple]
  norm_num

end Paper18.Category.PointedVec

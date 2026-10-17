import Paper18.Category.PivotalDimension
import Paper18.Category.PivotalPartialTrace
import Paper18.Category.SemisimpleSplitting

/-! # Actual rigid contractions without an ambient braiding or pivot

The actual nonzero cup out of the simple unit is mono and has a proved
semisimple retraction. The actual nonzero cap onto the simple unit has a
proved semisimple section. These actual choices normalize the two closing
operations; no braiding on odd objects or pivotal structure is assumed.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.ModuleFunctor
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- A real retraction of the actual right cup, constructed by semisimplicity. -/
def normalizedRightCap (X : C) [Simple X] : X ⊗ dual C X ⟶ 𝟙_ C := by
  letI := mono_of_nonzero_from_simple (exactPairing_coevaluation_ne_zero X (dual C X))
  exact (S.splitMono (η_ X (dual C X))).retraction

@[simp] theorem cup_normalizedRightCap (X : C) [Simple X] :
    η_ X (dual C X) ≫ normalizedRightCap S X = 𝟙 (𝟙_ C) := by
  letI := mono_of_nonzero_from_simple (exactPairing_coevaluation_ne_zero X (dual C X))
  exact (S.splitMono (η_ X (dual C X))).id

/-- A real section of the actual right evaluation, with the reverse cup
orientation needed for contraction, constructed from the actual simple
summands of its source. -/
def normalizedLeftCup (X : C) [Simple X] : 𝟙_ C ⟶ dual C X ⊗ X := by
  letI : Simple (dual C X) := S.simple_rightDual X
  exact Classical.choose (S.section_of_nonzero_to_simple (ε_ X (dual C X))
    (exactPairing_evaluation_ne_zero X (dual C X)))

@[simp] theorem normalizedLeftCup_evaluation (X : C) [Simple X] :
    normalizedLeftCup S X ≫ ε_ X (dual C X) = 𝟙 (𝟙_ C) := by
  letI : Simple (dual C X) := S.simple_rightDual X
  exact Classical.choose_spec (S.section_of_nonzero_to_simple (ε_ X (dual C X))
    (exactPairing_evaluation_ne_zero X (dual C X)))

/-- Any genuine normalized cup and cap retract tensoring, by monoidal
naturality alone. This lemma has no braiding assumption. -/
lemma rightClosure_whiskerRight_of_normalized {A B X P : C}
    (cup : 𝟙_ C ⟶ X ⊗ P) (cap : X ⊗ P ⟶ 𝟙_ C)
    (h : cup ≫ cap = 𝟙 (𝟙_ C)) (f : A ⟶ B) :
    rightClosure cup cap (f ▷ X) = f := by
  calc
    _ = f ≫ (ρ_ B).inv ≫ B ◁ (cup ≫ cap) ≫ (ρ_ B).hom := by
      simp only [rightClosure, whiskerLeft_comp, Category.assoc]
      rw [associator_naturality_left_assoc, Iso.inv_hom_id_assoc,
        whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]
    _ = _ := by rw [h]; simp

/-- Actual normalized complex-linear partial contraction of the right
factor, using only rigidity and the constructed semisimple cup retraction. -/
def simpleContraction {A B : C} (X : C) [Simple X] :
    (A ⊗ X ⟶ B ⊗ X) →ₗ[ℂ] (A ⟶ B) where
  toFun f := rightClosure (η_ X (dual C X)) (normalizedRightCap S X) f
  map_add' _ _ := by simp [rightClosure]
  map_smul' _ _ := by simp [rightClosure]

@[simp] theorem simpleContraction_whiskerRight {A B : C} (X : C) [Simple X] (f : A ⟶ B) :
    simpleContraction S X (f ▷ X) = f :=
  rightClosure_whiskerRight_of_normalized _ _ (cup_normalizedRightCap S X) f

/-- Close a genuine left tensor factor with actual cup and cap morphisms. -/
def leftClosure {A B X P : C} (cup : 𝟙_ C ⟶ P ⊗ X) (cap : P ⊗ X ⟶ 𝟙_ C)
    (f : X ⊗ A ⟶ X ⊗ B) : A ⟶ B :=
  (λ_ A).inv ≫ cup ▷ A ≫ (α_ P X A).hom ≫ P ◁ f ≫
    (α_ P X B).inv ≫ cap ▷ B ≫ (λ_ B).hom

lemma leftClosure_whiskerLeft_of_normalized {A B X P : C}
    (cup : 𝟙_ C ⟶ P ⊗ X) (cap : P ⊗ X ⟶ 𝟙_ C)
    (h : cup ≫ cap = 𝟙 (𝟙_ C)) (f : A ⟶ B) :
    leftClosure cup cap (X ◁ f) = f := by
  calc
    _ = f ≫ (λ_ B).inv ≫ (cup ≫ cap) ▷ B ≫ (λ_ B).hom := by
      simp only [leftClosure, comp_whiskerRight, Category.assoc]
      rw [← associator_naturality_right_assoc, Iso.hom_inv_id_assoc,
        ← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]
    _ = _ := by rw [h]; simp

/-- Actual normalized left partial contraction, using a genuine section
of the right evaluation. This uses no braiding on the contracted object. -/
def simpleLeftContraction {A B : C} (X : C) [Simple X] :
    (X ⊗ A ⟶ X ⊗ B) →ₗ[ℂ] (A ⟶ B) where
  toFun f := leftClosure (normalizedLeftCup S X) (ε_ X (dual C X)) f
  map_add' _ _ := by simp [leftClosure]
  map_smul' _ _ := by simp [leftClosure]

@[simp] theorem simpleLeftContraction_whiskerLeft {A B : C} (X : C) [Simple X] (f : A ⟶ B) :
    simpleLeftContraction S X (X ◁ f) = f :=
  leftClosure_whiskerLeft_of_normalized _ _ (normalizedLeftCup_evaluation S X) f

end Paper18.Category.ModuleFunctor

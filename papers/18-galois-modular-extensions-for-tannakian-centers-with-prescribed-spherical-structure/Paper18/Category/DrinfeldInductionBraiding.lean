import Paper18.Category.DrinfeldInductionCoend
import Paper18.Category.RigidDoubleDual

/-!
# The universal components of the central-induction half-braiding

The coend component is obtained by inserting an actual duality cup, using
the prescribed pivotal identification on the final strand, and applying the
canonical dual tensor comparison before the actual coend inclusion.
-/
noncomputable section
universe v u w
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- Right tensoring is a left adjoint by the actual right-duality adjunction. -/
instance tensorRight_isLeftAdjoint (U : C) : (tensorRight U).IsLeftAdjoint :=
  (tensorRightAdjunction U Uᘁ).isLeftAdjoint

/-- The pivotal component with its source and target unfolded for tensor coherence. -/
abbrev pivotalMap (J : PivotalStructure C) (U : C) : U ⟶ dual C (dual C U) :=
  J.j.hom.app U

/-- Insertion of a cup followed by the pivotal identification of the last strand. -/
def rigidInsertion (J : PivotalStructure C) (U A : C) :
    A ⊗ U ⟶ U ⊗ ((dual C U ⊗ A) ⊗ dual C (dual C U)) :=
  𝟙 (A ⊗ U) ⊗≫ η_ U (dual C U) ▷ (A ⊗ U) ⊗≫
    (U ⊗ (dual C U ⊗ A)) ◁ pivotalMap J U ⊗≫
      𝟙 (U ⊗ ((dual C U ⊗ A) ⊗ dual C (dual C U)))

/-- Insertion is natural in the strand surrounded by the cup and pivotal map. -/
lemma rigidInsertion_naturality (J : PivotalStructure C) (U : C)
    {A B : C} (f : A ⟶ B) :
    (f ▷ U) ≫ rigidInsertion J U B =
      rigidInsertion J U A ≫ U ◁ ((dual C U ◁ f) ▷ dual C (dual C U)) := by
  calc
    _ = 𝟙 (A ⊗ U) ⊗≫
        ((𝟙_ C) ◁ (f ▷ U) ≫ η_ U (dual C U) ▷ (B ⊗ U)) ⊗≫
        (U ⊗ (dual C U ⊗ B)) ◁ pivotalMap J U ⊗≫
          𝟙 (U ⊗ ((dual C U ⊗ B) ⊗ dual C (dual C U))) := by
      dsimp [rigidInsertion]
      monoidal
    _ = 𝟙 (A ⊗ U) ⊗≫ η_ U (dual C U) ▷ (A ⊗ U) ⊗≫
        ((U ◁ (dual C U ◁ f)) ▷ U ≫
          (U ⊗ (dual C U ⊗ B)) ◁ pivotalMap J U) ⊗≫
            𝟙 (U ⊗ ((dual C U ⊗ B) ⊗ dual C (dual C U))) := by
      rw [whisker_exchange]
      monoidal
    _ = _ := by
      rw [← whisker_exchange]
      dsimp [rigidInsertion]
      monoidal

/-- Naturality of the inverse canonical dual tensor comparison. -/
lemma dualTensorIso_inv_naturality_right (D : C) {T V : C} (f : T ⟶ V) :
    (dualMap C f ▷ dual C D) ≫ (dualTensorIso D T).inv =
      (dualTensorIso D V).inv ≫ dualMap C (D ◁ f) := by
  apply (cancel_epi (dualTensorIso D V).hom).mp
  rw [← assoc, ← dualTensorIso_naturality_right]
  simp only [assoc, Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc]

section Coend
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- The tail of a universal component, before the external strand is restored. -/
def inductionBraidingTail (X U T : C) :
    (dual C U ⊗ ((T ⊗ X) ⊗ dual C T)) ⊗ dual C (dual C U) ⟶
      inductionUnderlying S X :=
  𝟙 ((dual C U ⊗ ((T ⊗ X) ⊗ dual C T)) ⊗ dual C (dual C U)) ⊗≫
    ((dual C U ⊗ T) ⊗ X) ◁ (dualTensorIso (dual C U) T).inv ⊗≫
      inductionι S X (dual C U ⊗ T)

/-- Dinaturality of the tail follows from canonical dual-comparison
naturality and the actual induction coend relation. -/
lemma inductionBraidingTail_dinatural (X U : C) {T V : C} (f : T ⟶ V) :
    (dual C U ◁ ((T ⊗ X) ◁ dualMap C f)) ▷ dual C (dual C U) ≫
      inductionBraidingTail S X U T =
    (dual C U ◁ ((f ▷ X) ▷ dual C V)) ▷ dual C (dual C U) ≫
      inductionBraidingTail S X U V := by
  calc
    _ = 𝟙 ((dual C U ⊗ ((T ⊗ X) ⊗ dual C V)) ⊗ dual C (dual C U)) ⊗≫
        (((dual C U ⊗ T) ⊗ X) ◁
          ((dualMap C f ▷ dual C (dual C U)) ≫ (dualTensorIso (dual C U) T).inv)) ⊗≫
        inductionι S X (dual C U ⊗ T) := by
      dsimp [inductionBraidingTail]
      monoidal
    _ = 𝟙 ((dual C U ⊗ ((T ⊗ X) ⊗ dual C V)) ⊗ dual C (dual C U)) ⊗≫
        (((dual C U ⊗ T) ⊗ X) ◁ (dualTensorIso (dual C U) V).inv) ⊗≫
        ((((dual C U ⊗ T) ⊗ X) ◁ dualMap C (dual C U ◁ f)) ≫
          inductionι S X (dual C U ⊗ T)) := by
      rw [dualTensorIso_inv_naturality_right]
      monoidal
    _ = _ := by
      rw [inductionι_dinatural]
      calc
        _ = 𝟙 ((dual C U ⊗ ((T ⊗ X) ⊗ dual C V)) ⊗ dual C (dual C U)) ⊗≫
            ((((dual C U ⊗ T) ⊗ X) ◁ (dualTensorIso (dual C U) V).inv) ≫
              (((dual C U ◁ f) ▷ X) ▷ (dual C U ⊗ V)ᘁ)) ⊗≫
            inductionι S X (dual C U ⊗ V) := by monoidal
        _ = _ := by
          rw [whisker_exchange]
          dsimp [inductionBraidingTail]
          monoidal

/-- The component defining central induction's actual commutation map. -/
def inductionHalfBraidingComponent (J : PivotalStructure C) (X U T : C) :
    ((T ⊗ X) ⊗ dual C T) ⊗ U ⟶ U ⊗ inductionUnderlying S X :=
  rigidInsertion J U ((T ⊗ X) ⊗ dual C T) ≫ U ◁ inductionBraidingTail S X U T

/-- These components are dinatural in the coend variable. -/
lemma inductionHalfBraidingComponent_dinatural (J : PivotalStructure C) (X U : C)
    {T V : C} (f : T ⟶ V) :
    (((T ⊗ X) ◁ dualMap C f) ▷ U) ≫ inductionHalfBraidingComponent S J X U T =
      (((f ▷ X) ▷ dual C V) ▷ U) ≫ inductionHalfBraidingComponent S J X U V := by
  unfold inductionHalfBraidingComponent
  rw [← assoc, rigidInsertion_naturality, assoc]
  rw [← whiskerLeft_comp]
  rw [inductionBraidingTail_dinatural]
  rw [whiskerLeft_comp, ← assoc, ← rigidInsertion_naturality, assoc]

/-- The universal coend commutation map is derived by descent after tensoring.
All coend-existence and preservation instances are constructed from prior theory. -/
def inductionHalfBraidingHom (J : PivotalStructure C) (X U : C) :
    inductionUnderlying S X ⊗ U ⟶ U ⊗ inductionUnderlying S X := by
  letI := inductionHasCoend S X
  exact mappedCoendDesc (inductionDiagram X) (tensorRight U)
    (inductionHalfBraidingComponent S J X U)
    (fun f => inductionHalfBraidingComponent_dinatural S J X U f)

@[reassoc (attr := simp)]
lemma inductionHalfBraidingHom_ι (J : PivotalStructure C) (X U T : C) :
    (inductionι S X T ▷ U) ≫ inductionHalfBraidingHom S J X U =
      inductionHalfBraidingComponent S J X U T := by
  letI := inductionHasCoend S X
  exact mappedCoendDesc_ι (inductionDiagram X) (tensorRight U) _ _ T

end Coend
end Paper18.Category.Drinfeld

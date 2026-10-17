import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Pivotal structures and categorical traces

The duals, evaluations and coevaluations here are the chosen mathlib right duals.
A pivotal structure is a natural isomorphism from the identity to the double-dual
functor, with the unit and tensor compatibility given by the canonical comparison
maps built from evaluation and coevaluation. The resulting strong monoidal
structure is constructed by transport and its tensorator is proved to equal that
canonical comparison. Thus the definition includes the full monoidal coherence;
it is not a choice of dimensions on a fusion basis.

Traces take values in the actual endomorphisms of the monoidal unit.
-/

noncomputable section

universe v u

namespace Paper18.Category

open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.Monoidal

-- Use the category's chosen dual uniformly, including at the unit and at dual objects.
attribute [local instance 2000] RightRigidCategory.rightDual

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The right dual chosen by the rigid structure. -/
abbrev dual (X : C) : C := Xᘁ

/-- The contravariant action of the chosen duals on morphisms. -/
abbrev dualMap {X Y : C} (f : X ⟶ Y) : dual C Y ⟶ dual C X := rightAdjointMate f

/-- Double dualization as an actual functor, using the rigid adjoint mates. -/
def doubleDualFunctor : C ⥤ C where
  obj X := dual C (dual C X)
  map f := dualMap C (dualMap C f)
  map_id X := by simp [dualMap]
  map_comp f g := by simp [dualMap, comp_rightAdjointMate]

/-- Coevaluation for the tensor product pairing against `Y* ⊗ X*`. -/
def tensorCoevaluation (X Y : C) :
    𝟙_ C ⟶ (X ⊗ Y) ⊗ (dual C Y ⊗ dual C X) :=
  η_ X (dual C X) ≫
    X ◁ ((λ_ (dual C X)).inv ≫ η_ Y (dual C Y) ▷ dual C X ≫
      (α_ Y (dual C Y) (dual C X)).hom) ≫
    (α_ X Y (dual C Y ⊗ dual C X)).inv

/-- Evaluation for the tensor product pairing against `Y* ⊗ X*`. -/
def tensorEvaluation (X Y : C) :
    (dual C Y ⊗ dual C X) ⊗ (X ⊗ Y) ⟶ 𝟙_ C :=
  (α_ (dual C Y) (dual C X) (X ⊗ Y)).hom ≫
    dual C Y ◁ ((α_ (dual C X) X Y).inv ≫
      ε_ X (dual C X) ▷ Y ≫ (λ_ Y).hom) ≫ ε_ Y (dual C Y)

/-- The canonical comparison `(X ⊗ Y)* → Y* ⊗ X*` written using the cups and caps. -/
def dualTensorTo (X Y : C) : dual C (X ⊗ Y) ⟶ dual C Y ⊗ dual C X :=
  (ρ_ (dual C (X ⊗ Y))).inv ≫
    dual C (X ⊗ Y) ◁ tensorCoevaluation C X Y ≫
    (α_ (dual C (X ⊗ Y)) (X ⊗ Y) (dual C Y ⊗ dual C X)).inv ≫
    ε_ (X ⊗ Y) (dual C (X ⊗ Y)) ▷ (dual C Y ⊗ dual C X) ≫
    (λ_ (dual C Y ⊗ dual C X)).hom

/-- The reverse canonical comparison `Y* ⊗ X* → (X ⊗ Y)*`. -/
def dualTensorFrom (X Y : C) : dual C Y ⊗ dual C X ⟶ dual C (X ⊗ Y) :=
  (ρ_ (dual C Y ⊗ dual C X)).inv ≫
    (dual C Y ⊗ dual C X) ◁ η_ (X ⊗ Y) (dual C (X ⊗ Y)) ≫
    (α_ (dual C Y ⊗ dual C X) (X ⊗ Y) (dual C (X ⊗ Y))).inv ≫
    tensorEvaluation C X Y ▷ dual C (X ⊗ Y) ≫
    (λ_ (dual C (X ⊗ Y))).hom

/-- The canonical tensorator for double dualization, defined from actual duality maps. -/
def doubleDualTensorHom (X Y : C) :
    (doubleDualFunctor C).obj X ⊗ (doubleDualFunctor C).obj Y ⟶
      (doubleDualFunctor C).obj (X ⊗ Y) :=
  dualTensorFrom C (dual C Y) (dual C X) ≫ dualMap C (dualTensorTo C X Y)

/-- The canonical unit comparison `1* → 1`. -/
def dualUnitTo : dual C (𝟙_ C) ⟶ 𝟙_ C :=
  (ρ_ (dual C (𝟙_ C))).inv ≫ ε_ (𝟙_ C) (dual C (𝟙_ C))

/-- The canonical unit comparison `1 → 1*`. -/
def dualUnitFrom : 𝟙_ C ⟶ dual C (𝟙_ C) :=
  η_ (𝟙_ C) (dual C (𝟙_ C)) ≫ (λ_ (dual C (𝟙_ C))).hom

/-- The canonical unit morphism for double dualization. -/
def doubleDualUnitHom : 𝟙_ C ⟶ (doubleDualFunctor C).obj (𝟙_ C) :=
  dualUnitFrom C ≫ dualMap C (dualUnitTo C)

/-- A coherent pivotal structure on the chosen rigid monoidal category.

The two coherence equations use fixed duality formulas; in particular the
monoidal structure is not an arbitrary structure chosen to make `j` monoidal. -/
structure PivotalStructure where
  j : 𝟭 C ≅ doubleDualFunctor C
  unit : j.hom.app (𝟙_ C) = doubleDualUnitHom C
  tensor (X Y : C) : j.hom.app (X ⊗ Y) =
    (j.hom.app X ⊗ₘ j.hom.app Y) ≫ doubleDualTensorHom C X Y

namespace PivotalStructure

variable {C} (J : PivotalStructure C)
include J

/-- Full strong monoidal coherence on double dualization, induced by the pivotal
isomorphism. Its structure maps are identified with the fixed duality maps below. -/
def doubleDualMonoidal : (doubleDualFunctor C).Monoidal :=
  Functor.Monoidal.transport J.j

@[simp] lemma doubleDualMonoidal_unit :
    @ε _ _ _ _ _ _ (doubleDualFunctor C) J.doubleDualMonoidal.toLaxMonoidal =
      doubleDualUnitHom C := by
  simpa [doubleDualMonoidal, Functor.Monoidal.transport,
    Functor.Monoidal.coreMonoidalTransport, Functor.CoreMonoidal.toMonoidal,
    Functor.CoreMonoidal.toLaxMonoidal, Functor.LaxMonoidal.ε, εIso] using J.unit

@[simp] lemma doubleDualMonoidal_tensor (X Y : C) :
    @μ _ _ _ _ _ _ (doubleDualFunctor C) J.doubleDualMonoidal.toLaxMonoidal X Y =
      doubleDualTensorHom C X Y := by
  dsimp [doubleDualMonoidal, Functor.Monoidal.transport,
    Functor.Monoidal.coreMonoidalTransport, Functor.CoreMonoidal.toMonoidal,
    Functor.CoreMonoidal.toLaxMonoidal, Functor.LaxMonoidal.μ, μIso]
  rw [J.tensor, ← assoc]
  simp

/-- In a pivotal category the canonical duality tensor comparison is invertible. -/
lemma doubleDualTensorHom_isIso (X Y : C) : IsIso (doubleDualTensorHom C X Y) := by
  letI := J.doubleDualMonoidal
  rw [← J.doubleDualMonoidal_tensor X Y]
  infer_instance

/-- The canonical double-dual unit comparison is invertible. -/
lemma doubleDualUnitHom_isIso : IsIso (doubleDualUnitHom C) := by
  letI := J.doubleDualMonoidal
  rw [← J.doubleDualMonoidal_unit]
  infer_instance

/-- The pivotal isomorphism is a monoidal natural isomorphism, with the full
mathlib monoidal natural transformation interface. -/
lemma j_isMonoidal :
    @NatTrans.IsMonoidal _ _ _ _ _ _ (𝟭 C) (doubleDualFunctor C) J.j.hom
      inferInstance J.doubleDualMonoidal.toLaxMonoidal := by
  letI := J.doubleDualMonoidal
  constructor
  · change 𝟙 _ ≫ _ = _
    rw [id_comp, J.unit, J.doubleDualMonoidal_unit]
  · intro X Y
    change 𝟙 _ ≫ _ = _
    rw [id_comp, J.tensor, J.doubleDualMonoidal_tensor]

/-- The left evaluation induced from the pivotal identification `X ≅ X**`. -/
def leftEvaluation (X : C) : X ⊗ dual C X ⟶ 𝟙_ C :=
  J.j.hom.app X ▷ dual C X ≫ ε_ (dual C X) (dual C (dual C X))

/-- The left coevaluation induced from the pivotal identification. -/
def leftCoevaluation (X : C) : 𝟙_ C ⟶ dual C X ⊗ X :=
  η_ (dual C X) (dual C (dual C X)) ≫ dual C X ◁ J.j.inv.app X

/-- These induced cups and caps satisfy both snake identities: they form an
actual exact pairing, by transport along the pivotal isomorphism. -/
def leftExactPairing (X : C) : ExactPairing (dual C X) X := by
  letI : ExactPairing (dual C X) ((doubleDualFunctor C).obj X) :=
    inferInstanceAs (ExactPairing (dual C X) (dual C (dual C X)))
  exact exactPairingCongrRight (J.j.app X)

@[simp] lemma leftExactPairing_evaluation (X : C) :
    @ExactPairing.evaluation _ _ _ (dual C X) X (J.leftExactPairing X) =
      J.leftEvaluation X := rfl

@[simp] lemma leftExactPairing_coevaluation (X : C) :
    @ExactPairing.coevaluation _ _ _ (dual C X) X (J.leftExactPairing X) =
      J.leftCoevaluation X := rfl

/-- The right pivotal trace of an actual endomorphism. -/
def rightTrace {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ X (dual C X) ≫ f ▷ dual C X ≫ J.leftEvaluation X

/-- The left pivotal trace of an actual endomorphism. -/
def leftTrace {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  J.leftCoevaluation X ≫ dual C X ◁ f ≫ ε_ X (dual C X)

/-- Sphericality is equality of the two traces on every endomorphism, not only
an equality of assigned dimensions of simples. -/
def Spherical : Prop := ∀ (X : C) (f : X ⟶ X), J.leftTrace f = J.rightTrace f

/-- The right categorical dimension is an actual endomorphism of the unit. -/
def rightDimension (X : C) : 𝟙_ C ⟶ 𝟙_ C := J.rightTrace (𝟙 X)

/-- The left categorical dimension is an actual endomorphism of the unit. -/
def leftDimension (X : C) : 𝟙_ C ⟶ 𝟙_ C := J.leftTrace (𝟙 X)

lemma dimensions_eq_of_spherical (h : J.Spherical) (X : C) :
    J.leftDimension X = J.rightDimension X := h X (𝟙 X)

end PivotalStructure

end Paper18.Category

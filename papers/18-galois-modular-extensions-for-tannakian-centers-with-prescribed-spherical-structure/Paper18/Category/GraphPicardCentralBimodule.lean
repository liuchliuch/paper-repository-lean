import Paper18.Category.DrinfeldRigidBasic
import Paper18.Category.SeparableModules
import Paper18.Category.RelativeTensorAmbient

/-! # Actual bimodules from a commutative algebra in the Drinfeld center

Only the algebra's actual half-braiding is used. Its underlying algebra
need not be commutative for the ambient braiding, and the ambient category
need not carry a braiding.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u
namespace Paper18.Category.GraphPicard
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  (A : Center D) [MonObj A]

local instance underlyingMonObj : MonObj A.1 := Functor.monObjObj (F := Center.forget D) A

@[simp] lemma underlying_unit : η[A.1] = (η[A]).f := by
  change (𝟙 _ ≫ (η[A]).f) = (η[A]).f
  exact Category.id_comp _

@[simp] lemma underlying_mul : μ[A.1] = (μ[A]).f := by
  change (𝟙 _ ≫ (μ[A]).f) = (μ[A]).f
  exact Category.id_comp _

/-- The actual right action induced by the specified central half-braiding. -/
def centralRightAction (M : Mod_ D A.1) : M.X ⊗ A.1 ⟶ M.X :=
  (A.2.β M.X).inv ≫ γ[A.1,M.X]

@[reassoc]
lemma centralRightAction_naturality {M N : Mod_ D A.1} (f : M ⟶ N) :
    centralRightAction A M ≫ f.hom = (f.hom ▷ A.1) ≫ centralRightAction A N := by
  have hf := IsMod_Hom.smul_hom (A := A.1) (f := f.hom)
  change γ[A.1,M.X] ≫ f.hom = (A.1 ◁ f.hom) ≫ γ[A.1,N.X] at hf
  unfold centralRightAction
  rw [Category.assoc, hf,
    ← reassoc_of% (Drinfeld.halfBraiding_inv_naturality A.2 f.hom)]

/-- The actual algebra unit is central for the specified half-braiding. -/
lemma centralUnit_crossing (X : D) :
    η[A.1] ▷ X ≫ (A.2.β X).hom =
      (λ_ X).hom ≫ (ρ_ X).inv ≫ X ◁ η[A.1] := by
  have h := (η[A]).comm X
  simpa only [underlying_unit, Center.tensorUnit_β, Iso.trans_hom, Iso.symm_hom,
    Category.assoc] using h

@[reassoc (attr := simp)]
lemma centralRightAction_one (M : Mod_ D A.1) :
    M.X ◁ η[A.1] ≫ centralRightAction A M = (ρ_ M.X).hom := by
  apply (cancel_epi ((λ_ M.X).hom ≫ (ρ_ M.X).inv)).mp
  have h := centralUnit_crossing A M.X
  dsimp only [centralRightAction]
  simp only [Category.assoc]
  rw [← reassoc_of% h]
  simp only [Iso.hom_inv_id_assoc, InternalModule.one_smul, Iso.inv_hom_id,
    Category.comp_id]

variable [IsCommMonObj A]

/-- Commutativity in the actual center supplies the inverse-crossing
commutativity needed for the underlying bimodule. -/
lemma centralMul_inv_comm : (A.2.β A.1).inv ≫ μ[A.1] = μ[A.1] := by
  have h := congrArg Center.Hom.f (IsCommMonObj.mul_comm (X := A))
  change (A.2.β A.1).hom ≫ (μ[A]).f = (μ[A]).f at h
  rw [underlying_mul]
  apply (cancel_epi (A.2.β A.1).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h.symm

/-- The two actual actions commute, using the specified central algebra
commutativity and its genuine half-braiding hexagon. -/
@[reassoc]
lemma central_middle_assoc (M : Mod_ D A.1) :
    γ[A.1,M.X] ▷ A.1 ≫ centralRightAction A M =
      (α_ A.1 M.X A.1).hom ≫ A.1 ◁ centralRightAction A M ≫ γ[A.1,M.X] := by
  unfold centralRightAction
  rw [reassoc_of% (Drinfeld.halfBraiding_inv_naturality A.2 γ[A.1,M.X])]
  change (A.2.β (A.1 ⊗ M.X)).inv ≫ A.1 ◁ γ[A.1,M.X] ≫ γ[A.1,M.X] = _
  rw [Drinfeld.halfBraiding_inv_monoidal]
  simp only [Category.assoc, whiskerLeft_comp]
  rw [← InternalModule.mul_smul, ← comp_whiskerRight_assoc, centralMul_inv_comm,
    InternalModule.mul_smul]
  simp only [Iso.inv_hom_id_assoc]

/-- The actual central multiplication crosses through any ambient object. -/
@[reassoc]
lemma centralMul_crossing_inv (X : D) :
    X ◁ μ[A.1] ≫ (A.2.β X).inv =
      ((A ⊗ A).2.β X).inv ≫ μ[A.1] ▷ X := by
  have h := (μ[A]).comm X
  change (μ[A]).f ▷ X ≫ (A.2.β X).hom =
    ((A ⊗ A).2.β X).hom ≫ X ◁ (μ[A]).f at h
  rw [← underlying_mul A] at h
  apply (cancel_epi ((A ⊗ A).2.β X).hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← reassoc_of% h]
  simp only [Iso.hom_inv_id, Category.comp_id]

/-- The actual inverse crossing for the tensor of two central algebra factors. -/
lemma centralTensor_crossing_inv (X : D) :
    ((A ⊗ A).2.β X).inv =
      (α_ X A.1 A.1).inv ≫ (A.2.β X).inv ▷ A.1 ≫
        (α_ A.1 X A.1).hom ≫ A.1 ◁ (A.2.β X).inv ≫ (α_ A.1 A.1 X).inv := by
  change ((Center.tensorObj A A).2.β X).inv = _
  simp only [Center.tensorObj_snd_β, Iso.trans_inv, Iso.symm_inv,
    whiskerLeftIso_inv, whiskerRightIso_inv, Category.assoc]

/-- The induced actual right action is associative. -/
@[reassoc]
lemma central_right_assoc (M : Mod_ D A.1) :
    M.X ◁ μ[A.1] ≫ centralRightAction A M =
      (α_ M.X A.1 A.1).inv ≫ centralRightAction A M ▷ A.1 ≫ centralRightAction A M := by
  calc
    _ = (α_ M.X A.1 A.1).inv ≫ (A.2.β M.X).inv ▷ A.1 ≫
        (α_ A.1 M.X A.1).hom ≫ A.1 ◁ centralRightAction A M ≫ γ[A.1,M.X] := by
      unfold centralRightAction
      rw [centralMul_crossing_inv_assoc, centralTensor_crossing_inv]
      simp only [Category.assoc, whiskerLeft_comp]
      rw [InternalModule.mul_smul]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = _ := by
      rw [← central_middle_assoc]
      unfold centralRightAction
      simp only [comp_whiskerRight, Category.assoc]

/-- Each actual left module becomes an actual bimodule using precisely
the chosen central algebra half-braiding. -/
def centralToBimodObj (M : Mod_ D A.1) : Bimod (Mon.mk A.1) (Mon.mk A.1) where
  X := M.X
  actLeft := γ[A.1,M.X]
  one_actLeft := InternalModule.one_smul M
  left_assoc := InternalModule.mul_smul M
  actRight := centralRightAction A M
  actRight_one := centralRightAction_one A M
  right_assoc := central_right_assoc A M
  middle_assoc := central_middle_assoc A M

/-- The actual central right action is a genuine left-module morphism. -/
def centralRightActionHom (M : Mod_ D A.1) : RelativeTensor.ambientTensor M A.1 ⟶ M :=
  Mod_.Hom.mk' (centralRightAction A M) (by
    change ((α_ A.1 M.X A.1).inv ≫ γ[A.1,M.X] ▷ A.1) ≫ centralRightAction A M =
      (A.1 ◁ centralRightAction A M) ≫ γ[A.1,M.X]
    rw [Category.assoc, central_middle_assoc]
    simp)

end Paper18.Category.GraphPicard

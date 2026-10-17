import Paper18.Category.QuasiFusionAssociator
import Paper18.Category.QuasiFusionUnit
import Paper18.Category.GradedQuasiCancellationBasic
import Mathlib.Algebra.Module.TransferInstance

/-! # Actual homogeneous objects and relative half-braidings before pentagon

The tensor product is actual graded convolution. The associator is the
actual cochain-scaled convolution associator, without assuming a cocycle
identity away from the neutral component.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling QuasiFusion
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G] (p : Γ →* G)
local notation "V" => PointedVec (Additive Γ)

/-- The actual vector fibers vanish off one specified quotient coset. -/
def Supported (g : G) (X : V) : Prop :=
  ∀ a : Additive Γ, p a.toMul ≠ g → IsZero (X a)

lemma supported_tensor {g h : G} {X Y : V}
    (hX : Supported p g X) (hY : Supported p h Y) : Supported p (g * h) (X ⊗ Y) := by
  intro k hk
  apply (IsZero.iff_id_eq_zero _).mpr
  apply GradedObject.Monoidal.tensorObj_ext
  intro a b hab
  by_cases ha : p a.toMul = g
  · have hb : p b.toMul ≠ h := by
      intro hb
      apply hk
      have hab' : a.toMul * b.toMul = k.toMul := congrArg Additive.toMul hab
      rw [← hab', map_mul, ha, hb]
    exact ((tensorLeft (X a)).map_isZero (hY b hb)).eq_of_src _ _
  · exact ((tensorRight (Y b)).map_isZero (hX a ha)).eq_of_src _ _

lemma supported_unit : Supported p 1 (𝟙_ V) := by
  intro a ha
  exact (GradedObject.Monoidal.isInitialTensorUnitApply a (by
    intro h
    subst a
    exact ha p.map_one)).isZero

lemma supported_simple (a : Γ) :
    Supported p (p a) (PointedVec.simpleObject (Additive Γ) (Additive.ofMul a)) := by
  intro b hb
  apply PointedVec.simpleFiber_isZero
  intro h
  subst b
  exact hb rfl

/-- Objects in distinct quotient cosets have only the actual zero map. -/
lemma hom_zero_of_supported {g h : G} {X Y : V} (hX : Supported p g X)
    (hY : Supported p h Y) (hgh : g ≠ h) (f : X ⟶ Y) : f = 0 := by
  apply GradedObject.hom_ext
  intro a
  by_cases ha : p a.toMul = g
  · exact (hY a (by simpa only [ha] using hgh)).eq_of_tgt _ _
  · exact (hX a ha).eq_of_src _ _

variable (ψ : ThreeCochain Γ ℂˣ)

/-- The actual cochain-scaled convolution associator. -/
def quasiAssociator (X Y Z : V) : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z) :=
  scalarAssociator (fun a b c => ψ.val a.toMul b.toMul c.toMul) X Y Z

/-- A genuine half-braiding against all actual neutral-coset graded
vector spaces, with the actual cochain-scaled hexagon. -/
structure RelativeHalfBraiding (X : V) where
  β : ∀ U : V, Supported p 1 U → (X ⊗ U ≅ U ⊗ X)
  monoidal : ∀ U W (hU : Supported p 1 U) (hW : Supported p 1 W),
    (β (U ⊗ W) (by simpa only [one_mul] using supported_tensor p hU hW)).hom =
      (quasiAssociator ψ X U W).inv ≫ (β U hU).hom ▷ W ≫
        (quasiAssociator ψ U X W).hom ≫ U ◁ (β W hW).hom ≫
          (quasiAssociator ψ U W X).inv
  naturality : ∀ {U W : V} (hU : Supported p 1 U) (hW : Supported p 1 W) (f : U ⟶ W),
    X ◁ f ≫ (β W hW).hom = (β U hU).hom ≫ f ▷ X

/-- Actual relative-central objects; no full pentagon is assumed. -/
def RelativeObject := Σ X : V, RelativeHalfBraiding p ψ X

namespace RelativeObject
@[ext] structure Hom (X Y : RelativeObject p ψ) where
  f : X.1 ⟶ Y.1
  comm : ∀ (U : V) (hU : Supported p 1 U), f ▷ U ≫ (Y.2.β U hU).hom =
    (X.2.β U hU).hom ≫ U ◁ f

instance : Quiver (RelativeObject p ψ) where Hom := Hom p ψ
@[ext] lemma ext {X Y : RelativeObject p ψ} (f g : X ⟶ Y) (h : f.f = g.f) : f = g := by
  cases f
  cases g
  congr

instance category : Category (RelativeObject p ψ) where
  id X := ⟨𝟙 X.1, by intro U hU; simp⟩
  comp f g := ⟨f.f ≫ g.f, by
    intro U hU
    rw [comp_whiskerRight, assoc, g.comm U hU, ← assoc, f.comm U hU,
      assoc, ← whiskerLeft_comp]⟩

@[simp] lemma id_f (X : RelativeObject p ψ) : Hom.f (𝟙 X) = 𝟙 X.1 := rfl
@[simp] lemma comp_f {X Y Z : RelativeObject p ψ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).f = f.f ≫ g.f := rfl

def forget : RelativeObject p ψ ⥤ V where
  obj X := X.1
  map f := f.f

instance forget_faithful : (forget p ψ).Faithful where
  map_injective h := ext p ψ _ _ h

end RelativeObject
end Paper18.Category.PointedRelativeCenterObstruction

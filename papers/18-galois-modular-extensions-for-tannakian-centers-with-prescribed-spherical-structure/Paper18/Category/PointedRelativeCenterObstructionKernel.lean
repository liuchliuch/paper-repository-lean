import Paper18.Category.PointedRelativeCenterObstructionNeutral
import Mathlib.CategoryTheory.Equivalence

/-! # Actual kernel restriction and extension by zero -/
noncomputable section
set_option quotPrecheck false
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped ZeroObject
namespace Paper18.Category.PointedRelativeCenterObstruction
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G] (p : Γ →* G)
local notation "K" => p.ker
local notation "V" => PointedVec.{0} (Additive Γ)
local notation "W" => PointedVec.{0} (Additive K)

/-- Actual restriction of the vector fibers to actual kernel degrees. -/
def kernelRestriction : NeutralVec p ⥤ W where
  obj X a := X.obj (Additive.ofMul a.toMul.val)
  map f a := f (Additive.ofMul a.toMul.val)

instance kernelRestriction_faithful : (kernelRestriction p).Faithful where
  map_injective {X Y} f g h := by
    apply GradedObject.hom_ext
    intro a
    by_cases ha : p a.toMul = 1
    · exact congrFun h (Additive.ofMul (⟨a.toMul, ha⟩ : K))
    · exact (X.property a ha).eq_of_src _ _

instance kernelRestriction_full : (kernelRestriction p).Full where
  map_surjective {X Y} f := by
    let g : X ⟶ Y := fun a =>
      if ha : p a.toMul = 1 then f (Additive.ofMul (⟨a.toMul, ha⟩ : K)) else 0
    refine ⟨g, ?_⟩
    apply GradedObject.hom_ext
    intro a
    rcases a with ⟨a, ha⟩
    dsimp only [kernelRestriction, g]
    change (if ha' : p a = 1 then f (Additive.ofMul (⟨a, ha'⟩ : K)) else 0) =
      f (Additive.ofMul (⟨a, ha⟩ : K))
    rw [dif_pos (show p a = 1 from ha)]

instance kernelRestriction_additive : (kernelRestriction p).Additive where
  map_add := by intros; rfl
instance kernelRestriction_linear : (kernelRestriction p).Linear ℂ where
  map_smul _ _ := rfl

/-- The actual zero-dimensional vector space. -/
def kernelZeroFiber : FGModuleCat ℂ := FGModuleCat.of ℂ (Fin 0 → ℂ)

lemma kernelZeroFiber_isZero : IsZero kernelZeroFiber := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change x = 0
  funext i
  exact Fin.elim0 i

/-- Actual vector fibers are extended by the actual zero vector space
at every degree outside the kernel. -/
def kernelExtensionObject (X : W) : V := fun a =>
  if ha : p a.toMul = 1 then X (Additive.ofMul (⟨a.toMul, ha⟩ : K)) else kernelZeroFiber

lemma kernelExtensionObject_supported (X : W) : Supported p 1 (kernelExtensionObject p X) := by
  intro a ha
  dsimp only [kernelExtensionObject]
  rw [dif_neg ha]
  exact kernelZeroFiber_isZero

def kernelExtension (X : W) : NeutralVec p :=
  ⟨kernelExtensionObject p X, kernelExtensionObject_supported p X⟩

/-- Restricting actual extension by zero recovers every actual kernel
fiber, giving an actual graded-vector-space isomorphism. -/
def kernelRestrictionExtensionIso (X : W) :
    (kernelRestriction p).obj (kernelExtension p X) ≅ X :=
  GradedObject.isoMk _ _ (fun a => eqToIso (by
    dsimp only [kernelRestriction, kernelExtension, kernelExtensionObject]
    change (if ha : p a.toMul.val = 1 then
      X (Additive.ofMul (⟨a.toMul.val, ha⟩ : K)) else kernelZeroFiber) = X a
    rw [dif_pos (show p a.toMul.val = 1 from a.toMul.property)]
    congr 1))

instance kernelRestriction_essSurj : (kernelRestriction p).EssSurj where
  mem_essImage X := ⟨kernelExtension p X, ⟨kernelRestrictionExtensionIso p X⟩⟩

instance kernelRestriction_isEquivalence : (kernelRestriction p).IsEquivalence :=
  {}

/-- A genuine complex-linear categorical equivalence, before comparison
of the actual twisted tensor structures. -/
def kernelRestrictionEquivalence : NeutralVec p ≌ W :=
  (kernelRestriction p).asEquivalence

end Paper18.Category.PointedRelativeCenterObstruction

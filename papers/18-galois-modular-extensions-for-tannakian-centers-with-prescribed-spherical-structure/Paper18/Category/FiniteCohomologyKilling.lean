import Paper18.Category.FiniteCohomologyKillingTorsion
import Paper18.Category.FiniteCohomologyKillingPrimitive
import Mathlib.Algebra.Module.ZMod

/-! # Actual finite-group trivialization of complex fourth cocycles

The finite group, its surjection, and the normalized trivializing cochain
are constructed explicitly. No spectral sequence or existence certificate
is assumed.
-/
noncomputable section
universe u
namespace Paper18.Category.FiniteCohomologyKilling
open Classical

instance rootsAdditiveModule (n : ℕ) : Module (ZMod n) (Additive (rootsOfUnity n ℂ)) :=
  AddCommGroup.zmodModule (fun z => by
    apply Additive.toMul.injective
    change z.toMul ^ n = 1
    apply Subtype.ext
    exact (mem_rootsOfUnity n (z.toMul : ℂˣ)).mp z.toMul.property)

variable {G : Type u} [Group G] [Fintype G]

/-- An actual finite group sufficient to trivialize every complex fourth
cocycle on `G`. Its underlying module has `(card G - 1)^2` generators. -/
abbrev KillingExtension (G : Type u) [Group G] [Fintype G] :=
  UniversalExtension G (ZMod (Fintype.card G))

instance killingExtensionFintype : Fintype (KillingExtension G) := by
  letI : NeZero (Fintype.card G) := ⟨Fintype.card_ne_zero⟩
  infer_instance

namespace FourCocycle
variable (ω : FourCocycle G ℂˣ)

/-- The actual normalized primitive, including the explicit correction
from the roots-of-unity representative back to the original cocycle. -/
def finitePrimitive : ThreeCochain (KillingExtension G) ℂˣ where
  val x y z :=
    ((extensionPrimitive (R := ZMod (Fintype.card G)) ω.torsionRepresentativeRoots).val x y z : ℂˣ) *
      ω.rootTransferCochain.val x.quotient y.quotient z.quotient
  one₁ y z := by simp only [ThreeCochain.one₁, OneMemClass.coe_one,
    UniversalExtension.one_quotient, one_mul]
  one₂ x z := by simp only [ThreeCochain.one₂, OneMemClass.coe_one,
    UniversalExtension.one_quotient, one_mul]
  one₃ x y := by simp only [ThreeCochain.one₃, OneMemClass.coe_one,
    UniversalExtension.one_quotient, one_mul]

/-- The actual finite-extension primitive has exactly the required
pointwise coboundary, for the original complex-valued fourth cocycle. -/
theorem finitePrimitive_spec (x y z w : KillingExtension G) :
    dThree ω.finitePrimitive.val x y z w =
      ω.val x.quotient y.quotient z.quotient w.quotient := by
  rw [show ω.finitePrimitive.val =
    (fun x y z =>
      ((extensionPrimitive (R := ZMod (Fintype.card G)) ω.torsionRepresentativeRoots).val x y z : ℂˣ) *
        ω.rootTransferCochain.val x.quotient y.quotient z.quotient) from rfl,
    dThree_mul]
  have hp := congrArg (fun a : rootsOfUnity (Fintype.card G) ℂ => (a : ℂˣ))
    (extensionPrimitive_spec (R := ZMod (Fintype.card G)) ω.torsionRepresentativeRoots x y z w)
  change dThree (fun a b c =>
      ((extensionPrimitive (R := ZMod (Fintype.card G)) ω.torsionRepresentativeRoots).val a b c : ℂˣ))
      x y z w = ω.torsionRepresentative.val x.quotient y.quotient z.quotient w.quotient at hp
  rw [hp]
  change ω.torsionRepresentative.val x.quotient y.quotient z.quotient w.quotient *
    dThree ω.rootTransferCochain.val x.quotient y.quotient z.quotient w.quotient = _
  exact ω.torsionRepresentative_recover _ _ _ _

/-- Every actual normalized complex fourth cocycle becomes an actual
third coboundary after pullback along a constructed finite surjection. -/
theorem finite_extension_kills :
    ∃ p : KillingExtension G →* G, Function.Surjective p ∧
      ∃ a : ThreeCochain (KillingExtension G) ℂˣ,
        ∀ x y z w, dThree a.val x y z w = ω.val (p x) (p y) (p z) (p w) := by
  exact ⟨UniversalExtension.projection, UniversalExtension.projection_surjective,
    ω.finitePrimitive, ω.finitePrimitive_spec⟩

end FourCocycle
end Paper18.Category.FiniteCohomologyKilling

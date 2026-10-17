import Paper18.Category.FiniteCohomologyKilling

/-! # The actual associativity cocycle on the finite kernel

Restricting the constructed trivializing cochain to the actual kernel gives
a normalized third cocycle, hence precisely the scalar associativity data
for the kernel's twisted graded-vector-space category.
-/
noncomputable section
universe u
namespace Paper18.Category.QuasiFusion
open Classical
open FiniteCohomologyKilling
variable {G : Type u} [Group G]

/-- The actual normalized scalar associativity cocycle. -/
structure ThreeCocycle (G : Type u) [Group G] extends ThreeCochain G ℂˣ where
  closed : ∀ g h k l, dThree val g h k l = 1

namespace ThreeCocycle
variable (a : ThreeCocycle G)

/-- The actual scalar pentagon equation, derived from the cocycle differential. -/
lemma pentagon (g h k l : G) :
    a.val h k l * a.val g (h * k) l * a.val g h k =
      a.val (g * h) k l * a.val g h (k * l) := by
  calc
    _ = dThree a.val g h k l * (a.val (g * h) k l * a.val g h (k * l)) := by
      apply Additive.ofMul.injective
      simp only [dThree, ofMul_mul, ofMul_inv]
      abel
    _ = _ := by rw [a.closed, one_mul]

/-- The two opposite snake corrections are inverse scalars. -/
lemma inverse_pair (g : G) : a.val g⁻¹ g g⁻¹ * a.val g g⁻¹ g = 1 := by
  have h := a.pentagon g g⁻¹ g g⁻¹
  simpa only [mul_inv_cancel, inv_mul_cancel, ThreeCochain.one₁,
    ThreeCochain.one₂, ThreeCochain.one₃, mul_one] using h

end ThreeCocycle

variable [Fintype G]

/-- The actual finite kernel of the actual finite killing extension. -/
abbrev KillingKernel (G : Type u) [Group G] [Fintype G] :=
  (UniversalExtension.projection (G := G) (R := ZMod (Fintype.card G))).ker

/-- The actual third cocycle on the actual finite kernel, obtained from the
constructed primitive and its proved fourth coboundary equation. -/
def kernelCocycle (ω : FourCocycle G ℂˣ) : ThreeCocycle (KillingKernel G) where
  val x y z := ω.finitePrimitive.val x.val y.val z.val
  one₁ y z := by exact ω.finitePrimitive.one₁ y.val z.val
  one₂ x z := by exact ω.finitePrimitive.one₂ x.val z.val
  one₃ x y := by exact ω.finitePrimitive.one₃ x.val y.val
  closed x y z w := by
    change dThree ω.finitePrimitive.val x.val y.val z.val w.val = 1
    rw [ω.finitePrimitive_spec]
    have hx : x.val.quotient = 1 := x.property
    rw [hx, ω.one₁]

/-- The kernel associator values have finite order, with a bound determined
by the original finite group. -/
lemma kernelCocycle_pow (ω : FourCocycle G ℂˣ) (x y z : KillingKernel G) :
    (kernelCocycle ω).val x y z ^ Fintype.card G = 1 := by
  change (((extensionPrimitive (R := ZMod (Fintype.card G)) ω.torsionRepresentativeRoots).val
      x.val y.val z.val : ℂˣ) *
      ω.rootTransferCochain.val x.val.quotient y.val.quotient z.val.quotient) ^ Fintype.card G = 1
  have hx : x.val.quotient = 1 := x.property
  rw [hx, ω.rootTransferCochain.one₁, mul_one]
  exact (mem_rootsOfUnity _ _).mp
    ((extensionPrimitive (R := ZMod (Fintype.card G)) ω.torsionRepresentativeRoots).val
      x.val y.val z.val).property

end Paper18.Category.QuasiFusion

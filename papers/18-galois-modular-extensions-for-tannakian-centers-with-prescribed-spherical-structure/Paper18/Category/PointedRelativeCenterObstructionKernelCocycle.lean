import Paper18.Category.PointedRelativeCenterObstructionPentagon

/-! # The actual kernel third cocycle derived from the finite primitive -/
noncomputable section
open Classical
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling QuasiFusion
variable {Γ G : Type} [Group Γ] [Group G] (p : Γ →* G)
  (ψ : ThreeCochain Γ ℂˣ) (ω : FourCocycle G ℂˣ)
  (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))

/-- Restriction of the actual primitive to the actual kernel is a genuine
third cocycle, by the normalized actual fourth-cocycle identity. -/
def kernelCocycleOfPrimitive : ThreeCocycle p.ker where
  val a b c := ψ.val a.val b.val c.val
  one₁ a b := ψ.one₁ a.val b.val
  one₂ a b := ψ.one₂ a.val b.val
  one₃ a b := ψ.one₃ a.val b.val
  closed a b c d := by
    change dThree ψ.val a.val b.val c.val d.val = 1
    rw [hψ, show p a.val = 1 from a.property]
    exact ω.one₁ (p b.val) (p c.val) (p d.val)

section FinitePrimitive
variable [Fintype G]

/-- The derived generic kernel cocycle is definitionally the genuine
kernel cocycle used by the already constructed quotient center action. -/
@[simp] lemma kernelCocycleOfPrimitive_finitePrimitive (Ω : FourCocycle G ℂˣ) :
    kernelCocycleOfPrimitive
      (UniversalExtension.projection (G := G) (R := ZMod (Fintype.card G)))
      Ω.finitePrimitive Ω (fun a b c d => Ω.finitePrimitive_spec a b c d) =
        kernelCocycle Ω := rfl
end FinitePrimitive

end Paper18.Category.PointedRelativeCenterObstruction

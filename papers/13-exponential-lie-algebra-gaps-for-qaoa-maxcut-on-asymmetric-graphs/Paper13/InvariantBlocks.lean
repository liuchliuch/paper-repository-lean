import Paper13.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators

/-- Complex subspaces invariant under the real operator algebra L. -/
def InvariantUnder {ι : Type*} [Fintype ι] (L : Set (Matrix ι ι ℂ))
    (W : Submodule ℂ (ι → ℂ)) : Prop :=
  ∀ A ∈ L, ∀ w ∈ W, A.mulVec w ∈ W

/-- Irreducibility means there is no proper nonzero complex invariant subspace. -/
def IrreducibleOn {ι : Type*} [Fintype ι] (L : Set (Matrix ι ι ℂ))
    (W : Submodule ℂ (ι → ℂ)) : Prop :=
  W ≠ ⊥ ∧ InvariantUnder L W ∧
    ∀ U : Submodule ℂ (ι → ℂ), U ≤ W → InvariantUnder L U → U = ⊥ ∨ U = W

/-- A commuting operator has invariant kernel. -/
lemma invariant_ker_of_commute {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Set (Matrix ι ι ℂ)) (R : Matrix ι ι ℂ)
    (hcomm : ∀ A ∈ L, R*A = A*R) : InvariantUnder L (LinearMap.ker (Matrix.toLin' R)) := by
  intro A hA w hw
  change R.mulVec (A.mulVec w) = 0
  change R.mulVec w = 0 at hw
  rw [Matrix.mulVec_mulVec, hcomm A hA, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]

/-- The projection argument in Proposition 5: every irreducible constituent
injects into at least one commuting block. This does not assume that the
constituent itself equals one of the displayed blocks. -/
theorem irreducible_le_one_block {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] (L : Set (Matrix ι ι ℂ)) (W : Submodule ℂ (ι → ℂ))
    (hW : IrreducibleOn L W) (R : β → Matrix ι ι ℂ)
    (hcomm : ∀ b A, A ∈ L → R b * A = A * R b)
    (hsum : ∑ b, R b = 1) :
    ∃ b, Module.finrank ℂ W ≤ Module.finrank ℂ (LinearMap.range (Matrix.toLin' (R b))) := by
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW.1
  have hsome : ∃ b, (R b).mulVec w ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : (∑ b, R b).mulVec w = 0 := by simp [Matrix.sum_mulVec, h]
    rw [hsum, Matrix.one_mulVec] at hz
    exact hw0 hz
  obtain ⟨b, hb⟩ := hsome
  let U := W ⊓ LinearMap.ker (Matrix.toLin' (R b))
  have hU : InvariantUnder L U := by
    intro A hA x hx
    exact ⟨hW.2.1 A hA x hx.1, invariant_ker_of_commute L (R b) (hcomm b) A hA x hx.2⟩
  have hbot : U = ⊥ := by
    rcases hW.2.2 U inf_le_left hU with h | h
    · exact h
    · have hwU : w ∈ U := h.symm ▸ hwW
      exact False.elim (hb hwU.2)
  let f : W →ₗ[ℂ] LinearMap.range (Matrix.toLin' (R b)) :=
    ((Matrix.toLin' (R b)).rangeRestrict).comp W.subtype
  have hf : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm
    · intro x hx
      have hxU : (x : ι → ℂ) ∈ U := ⟨x.property, by
        change (Matrix.toLin' (R b)) x.val = 0
        exact congrArg Subtype.val hx⟩
      rw [hbot] at hxU
      exact Subtype.ext hxU
    · exact bot_le
  exact ⟨b, LinearMap.finrank_le_finrank_of_injective hf⟩
end Paper13

import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

/-! The real-infimum argument in S4.Ex22. This is a supporting order theorem
about arbitrary nonempty mass sets. It does not define spherical volume or
supply the geometric approximation and transfer hypotheses for the paper. -/
set_option autoImplicit false
namespace Paper28

/-- Arbitrarily accurate joint competitors imply the required lower bound
for the infimum over all competitors. -/
theorem infimum_joint_lower_bound (A B C : Set ℝ)
    (hA : BddBelow A) (hB : BddBelow B) (hC : C.Nonempty)
    (hjoint : ∀ c ∈ C, ∀ ε : ℝ, 0 < ε →
      ∃ a ∈ A, ∃ b ∈ B, a + b ≤ c + ε) :
    sInf A + sInf B ≤ sInf C := by
  apply le_csInf hC
  intro c hc
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a, ha, b, hb, hab⟩ := hjoint c hc ε hε
  exact (add_le_add (csInf_le hA ha) (csInf_le hB hb)).trans hab

/-- Complete numerical additivity from gluing and joint approximation.
The substantive geometric input needed to instantiate this theorem remains
Lemma 3.1 and Proposition 3.2, with recovery of the factor homology classes. -/
theorem infimum_additivity_of_joint_approximation (A B C : Set ℝ)
    (hA : BddBelow A) (hB : BddBelow B) (hC : BddBelow C)
    (hneA : A.Nonempty) (hneB : B.Nonempty) (hneC : C.Nonempty)
    (hglue : ∀ a ∈ A, ∀ b ∈ B, ∃ c ∈ C, c ≤ a + b)
    (hjoint : ∀ c ∈ C, ∀ ε : ℝ, 0 < ε →
      ∃ a ∈ A, ∃ b ∈ B, a + b ≤ c + ε) :
    sInf C = sInf A + sInf B := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨a, ha, haε⟩ := exists_lt_of_csInf_lt hneA
      (show sInf A < sInf A + ε / 2 by linarith)
    obtain ⟨b, hb, hbε⟩ := exists_lt_of_csInf_lt hneB
      (show sInf B < sInf B + ε / 2 by linarith)
    obtain ⟨c, hc, hcab⟩ := hglue a ha b hb
    have hcinf := csInf_le hC hc
    linarith
  · exact infimum_joint_lower_bound A B C hA hB hneC hjoint

end Paper28

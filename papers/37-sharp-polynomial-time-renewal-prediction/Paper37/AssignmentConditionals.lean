import Paper37.EnvelopeBridge
import Paper37.RenewalCompression

namespace Paper37.AssignmentConditionals

open Finset Renewal Prediction EnvelopeBridge RenewalCompression Compression Compression.Distribution

lemma prefixMass_step (N : ℕ) (z : List Bool) (hz : z.length < N) :
    prefixMass N z = prefixMass N (z ++ [false]) + prefixMass N (z ++ [true]) := by
  unfold prefixMass
  have hrem : N-z.length = (N-(z.length+1))+1 := by omega
  rw [hrem, sum_words_step]
  simp [List.append_assoc]

lemma prefixMass_pos (N : ℕ) (z : List Bool) : 0 < prefixMass N z := by
  apply Finset.sum_pos'
  · intro v hv
    exact (blockAssignment_pos _).le
  · refine ⟨List.replicate (N-z.length) false, ?_, blockAssignment_pos _⟩
    exact List.mem_toFinset.mpr ((mem_words _ _).mpr (by simp))

@[simp] theorem prefixMass_nil (N : ℕ) : prefixMass N [] = 1 := by
  simpa [prefixMass] using blockAssignment_sum N

lemma prefixMass_full (N : ℕ) (x : List Bool) (hx : x.length = N) :
    prefixMass N x = blockAssignment x := by
  simp [prefixMass, hx, words]

/-- Every queried conditional before its horizon is a genuine interior probability. -/
theorem blockConditional_interior (N : ℕ) (z : List Bool) (hz : z.length < N) :
    0 < blockConditional N z ∧ blockConditional N z < 1 := by
  have hp := prefixMass_pos N z
  have ht := prefixMass_pos N (z ++ [true])
  have hf := prefixMass_pos N (z ++ [false])
  constructor
  · exact div_pos ht hp
  · unfold blockConditional
    apply (div_lt_one hp).mpr
    rw [prefixMass_step N z hz]
    linarith

/-- A horizon-specific source conditional, extended by fair coins after the horizon. -/
noncomputable def kernel (N : ℕ) (z : List Bool) : Distribution Bool :=
  if hz : z.length < N then
    binary (blockConditional N z : ℝ)
      (by exact_mod_cast (blockConditional_interior N z hz).1.le)
      (by exact_mod_cast (blockConditional_interior N z hz).2.le)
  else binary (1/2) (by norm_num) (by norm_num)

lemma kernel_pos (N : ℕ) (z : List Bool) (b : Bool) : 0 < kernel N z b := by
  unfold kernel
  split_ifs with hz
  · have h := blockConditional_interior N z hz
    cases b
    · simp only [binary_false]
      have : (blockConditional N z : ℝ) < 1 := by exact_mod_cast h.2
      linarith
    · simp only [binary_true]
      exact_mod_cast h.1
  · cases b <;> norm_num

lemma kernel_true (N : ℕ) (z : List Bool) (hz : z.length < N) :
    kernel N z true = (blockConditional N z : ℝ) := by
  simp [kernel, hz]

/-- The prefix kernel recovers each true prefix probability exactly. -/
theorem prefixMass_weighted_kernel (N : ℕ) (z : List Bool) (hz : z.length < N) (b : Bool) :
    (prefixMass N z : ℝ) * kernel N z b = (prefixMass N (z ++ [b]) : ℝ) := by
  have hp : (prefixMass N z : ℝ) ≠ 0 := by exact_mod_cast (prefixMass_pos N z).ne'
  have ht : (prefixMass N z : ℝ) * (blockConditional N z : ℝ) =
      (prefixMass N (z ++ [true]) : ℝ) := by
    push_cast [blockConditional]
    exact mul_div_cancel₀ _ hp
  cases b
  · simp only [kernel, hz, ↓reduceDIte, binary_false]
    have hs := prefixMass_step N z hz
    have hs' : (prefixMass N z : ℝ) = (prefixMass N (z ++ [false]) : ℝ) +
      (prefixMass N (z ++ [true]) : ℝ) := by exact_mod_cast hs
    nlinarith
  · rw [kernel_true N z hz]
    exact ht

end Paper37.AssignmentConditionals

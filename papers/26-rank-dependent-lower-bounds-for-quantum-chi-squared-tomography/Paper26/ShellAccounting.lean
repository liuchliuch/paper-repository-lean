import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega


/-!
# P26, Lemma 5.1: finite shell accounting

`freezeTime i` is the first stage at which coordinate `i` is frozen. The final
active coordinates have freeze time `L`. An ordered matrix entry is charged to
the minimum of its two freeze times. This models both cross blocks as ordered
entries, so that no off-diagonal factor is silently discarded.
-/

open scoped BigOperators Matrix

noncomputable section

namespace Paper26.ShellAccounting

variable {ι : Type*} [Fintype ι]

/-- Ordered entries assigned to stage `j`. -/
def shellEntries (freezeTime : ι → ℕ) (j : ℕ) : Finset (ι × ι) :=
  Finset.univ.filter fun p => min (freezeTime p.1) (freezeTime p.2) = j

/-- Ordered entries of the block still active at the start of stage `j`. -/
def activeEntries (freezeTime : ι → ℕ) (j : ℕ) : Finset (ι × ι) :=
  Finset.univ.filter fun p => j ≤ freezeTime p.1 ∧ j ≤ freezeTime p.2

/-- Entries outside the final active block. -/
def frozenEntries (freezeTime : ι → ℕ) (L : ℕ) : Finset (ι × ι) :=
  Finset.univ.filter fun p => min (freezeTime p.1) (freezeTime p.2) < L

@[simp] theorem mem_shellEntries {freezeTime : ι → ℕ} {j : ℕ} {p : ι × ι} :
    p ∈ shellEntries freezeTime j ↔ min (freezeTime p.1) (freezeTime p.2) = j := by
  simp [shellEntries]

/-- The minimum convention is exactly “both indices active, one newly frozen”. -/
theorem mem_shellEntries_iff {freezeTime : ι → ℕ} {j : ℕ} {p : ι × ι} :
    p ∈ shellEntries freezeTime j ↔
      j ≤ freezeTime p.1 ∧ j ≤ freezeTime p.2 ∧
        (freezeTime p.1 = j ∨ freezeTime p.2 = j) := by
  rw [mem_shellEntries]
  omega

theorem shellEntries_subset_activeEntries (freezeTime : ι → ℕ) (j : ℕ) :
    shellEntries freezeTime j ⊆ activeEntries freezeTime j := by
  intro p hp
  obtain ⟨h₁, h₂, _⟩ := mem_shellEntries_iff.mp hp
  simpa [activeEntries] using And.intro h₁ h₂

/-- Every entry outside the final active block is charged at exactly one stage. -/
theorem assigned_exactly_once (freezeTime : ι → ℕ) (L : ℕ) (p : ι × ι) :
    p ∈ frozenEntries freezeTime L ↔
      ∃! j, j < L ∧ p ∈ shellEntries freezeTime j := by
  simp only [frozenEntries, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_shellEntries]
  constructor
  · intro h
    exact ⟨min (freezeTime p.1) (freezeTime p.2), ⟨h, rfl⟩,
      fun j hj => hj.2.symm⟩
  · rintro ⟨j, ⟨hj, hp⟩, _⟩
    omega

/-- Under the standard final-time bound, these are precisely entries with at
least one coordinate outside the final active subspace. -/
theorem mem_frozenEntries_iff (freezeTime : ι → ℕ) (L : ℕ)
    (hbound : ∀ i, freezeTime i ≤ L) (p : ι × ι) :
    p ∈ frozenEntries freezeTime L ↔ ¬(freezeTime p.1 = L ∧ freezeTime p.2 = L) := by
  simp only [frozenEntries, Finset.mem_filter, Finset.mem_univ, true_and]
  have := hbound p.1
  have := hbound p.2
  omega

/-- Exact accounting for any real-valued ordered-entry quantity. -/
theorem sum_shells (freezeTime : ι → ℕ) (L : ℕ) (f : ι × ι → ℝ) :
    (∑ j ∈ Finset.range L, ∑ p ∈ shellEntries freezeTime j, f p) =
      ∑ p ∈ frozenEntries freezeTime L, f p := by
  simpa [shellEntries, frozenEntries] using
    (Finset.sum_fiberwise_eq_sum_filter Finset.univ (Finset.range L)
      (fun p : ι × ι => min (freezeTime p.1) (freezeTime p.2)) f)

/-- The exact Frobenius-square summand for a complex matrix. -/
def entryError (E : Matrix ι ι ℂ) (p : ι × ι) : ℝ := ‖E p.1 p.2‖ ^ 2

omit [Fintype ι] in
@[simp] theorem entryError_nonneg (E : Matrix ι ι ℂ) (p : ι × ι) :
    0 ≤ entryError E p := sq_nonneg _

/-- Restricting a local Frobenius estimate to its newly frozen shell can only
reduce its squared error. -/
theorem shell_error_le_active (freezeTime : ι → ℕ) (j : ℕ) (E : Matrix ι ι ℂ) :
    (∑ p ∈ shellEntries freezeTime j, entryError E p) ≤
      ∑ p ∈ activeEntries freezeTime j, entryError E p := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (shellEntries_subset_activeEntries freezeTime j)
    (fun p _ _ => entryError_nonneg E p)

/-- A single frozen output eigenvalue controls the Bures denominator. -/
theorem bures_weight_bound {a b lower x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hlower : 0 < lower) (hfrozen : lower ≤ a ∨ lower ≤ b) (hx : 0 ≤ x) :
    2 * x / (a + b) ≤ (2 / lower) * x := by
  have hden : lower ≤ a + b := by rcases hfrozen with h | h <;> linarith
  calc
    2 * x / (a + b) ≤ 2 * x / lower :=
      div_le_div_of_nonneg_left (by positivity) hlower hden
    _ = (2 / lower) * x := by ring

/-- The spectral lower bound needed in one shell follows from its frozen index. -/
theorem shell_bures_bound (freezeTime : ι → ℕ) (j : ℕ)
    (E : Matrix ι ι ℂ) (a : ι → ℝ) (lower η : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hlower : 0 < lower)
    (hfrozen : ∀ i, freezeTime i = j → lower ≤ a i)
    (herror : (∑ p ∈ activeEntries freezeTime j, entryError E p) ≤ η) :
    (∑ p ∈ shellEntries freezeTime j,
      2 * entryError E p / (a p.1 + a p.2)) ≤ 2 * η / lower := by
  calc
    (∑ p ∈ shellEntries freezeTime j,
        2 * entryError E p / (a p.1 + a p.2)) ≤
        ∑ p ∈ shellEntries freezeTime j, (2 / lower) * entryError E p := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨_, _, hp⟩ := mem_shellEntries_iff.mp hp
      apply bures_weight_bound (ha p.1) (ha p.2) hlower
      · exact hp.imp (hfrozen p.1) (hfrozen p.2)
      · exact entryError_nonneg E p
    _ = (2 / lower) * ∑ p ∈ shellEntries freezeTime j, entryError E p := by
      rw [Finset.mul_sum]
    _ ≤ (2 / lower) * η := by
      apply mul_le_mul_of_nonneg_left
      · exact (shell_error_le_active freezeTime j E).trans herror
      · positivity
    _ = 2 * η / lower := by ring


/-- Frobenius norm squared, with the entrywise sum made explicit. -/
def frobeniusSq {m n : Type*} [Fintype m] [Fintype n]
    (E : Matrix m n ℂ) : ℝ := ∑ i, ∑ k, ‖E i k‖ ^ 2

theorem frobeniusSq_nonneg {m n : Type*} [Fintype m] [Fintype n]
    (E : Matrix m n ℂ) : 0 ≤ frobeniusSq E := by
  unfold frobeniusSq
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _

/-- The entrywise Frobenius square equals the trace formula. -/
theorem frobeniusSq_eq_trace {m n : Type*} [Fintype m] [Fintype n]
    (E : Matrix m n ℂ) : frobeniusSq E = (Matrix.trace (E * Eᴴ)).re := by
  simp [frobeniusSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.mul_conj']
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]

/-- The other trace formula is useful for rotations on the row index. -/
theorem frobeniusSq_eq_trace' {m n : Type*} [Fintype m] [Fintype n]
    (E : Matrix m n ℂ) : frobeniusSq E = (Matrix.trace (Eᴴ * E)).re := by
  rw [Matrix.trace_mul_comm]
  exact frobeniusSq_eq_trace E

/-- Rotating the remaining column coordinates preserves every true cross-block
Frobenius norm; the only premise is the actual matrix unitary identity. -/
theorem frobeniusSq_mul_unitary {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (E : Matrix m n ℂ) (U : Matrix n n ℂ)
    (hU : U * Uᴴ = 1) : frobeniusSq (E * U) = frobeniusSq E := by
  rw [frobeniusSq_eq_trace, frobeniusSq_eq_trace, Matrix.conjTranspose_mul]
  have h : E * U * (Uᴴ * Eᴴ) = E * Eᴴ := by
    calc
      E * U * (Uᴴ * Eᴴ) = E * (U * Uᴴ) * Eᴴ := by
        simp only [Matrix.mul_assoc]
      _ = E * Eᴴ := by rw [hU, Matrix.mul_one]
  rw [h]

/-- The companion invariance for the other ordered cross block. -/
theorem frobeniusSq_unitary_mul {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (E : Matrix m n ℂ) (U : Matrix m m ℂ)
    (hU : Uᴴ * U = 1) : frobeniusSq (U * E) = frobeniusSq E := by
  rw [frobeniusSq_eq_trace', frobeniusSq_eq_trace', Matrix.conjTranspose_mul]
  have h : Eᴴ * Uᴴ * (U * E) = Eᴴ * E := by
    calc
      Eᴴ * Uᴴ * (U * E) = Eᴴ * (Uᴴ * U) * E := by
        simp only [Matrix.mul_assoc]
      _ = Eᴴ * E := by rw [hU, Matrix.mul_one]
  rw [h]


/-- Frobenius-square accounting for an actual four-block matrix. -/
theorem frobeniusSq_fromBlocks
    {f r : Type*} [Fintype f] [Fintype r]
    (F : Matrix f f ℂ) (B : Matrix f r ℂ) (C : Matrix r f ℂ)
    (D : Matrix r r ℂ) :
    frobeniusSq (Matrix.fromBlocks F B C D) =
      frobeniusSq F + frobeniusSq B + frobeniusSq C + frobeniusSq D := by
  simp [frobeniusSq, Fintype.sum_sum_type, Finset.sum_add_distrib]
  ring

/-- The local shell consists of its frozen diagonal block and both ordered
cross blocks. Subsequent unitaries on the remaining coordinates preserve all
three squared-error contributions. The remaining diagonal block is nonnegative
and hence can be dropped from the local Frobenius error budget. -/
theorem shell_error_after_remaining_rotation
    {f r : Type*} [Fintype f] [Fintype r] [DecidableEq r]
    (F : Matrix f f ℂ) (B : Matrix f r ℂ) (C : Matrix r f ℂ)
    (D : Matrix r r ℂ) (U : Matrix r r ℂ) (η : ℝ)
    (hU : U * Uᴴ = 1)
    (hlocal : frobeniusSq (Matrix.fromBlocks F B C D) ≤ η) :
    frobeniusSq F + frobeniusSq (B * U) + frobeniusSq (Uᴴ * C) ≤ η := by
  rw [frobeniusSq_mul_unitary B U hU,
    frobeniusSq_unitary_mul C Uᴴ (by simpa using hU)]
  rw [frobeniusSq_fromBlocks] at hlocal
  have := frobeniusSq_nonneg D
  linarith


/-- Rectangular weighted squared error, needed for each of the two ordered
cross blocks separately. -/
def weightedError {m n : Type*} [Fintype m] [Fintype n]
    (E : Matrix m n ℂ) (a : m → ℝ) (b : n → ℝ) : ℝ :=
  ∑ i, ∑ k, 2 * ‖E i k‖ ^ 2 / (a i + b k)

theorem weightedError_le
    {m n : Type*} [Fintype m] [Fintype n]
    (E : Matrix m n ℂ) (a : m → ℝ) (b : n → ℝ) (lower : ℝ)
    (hlower : 0 < lower) (hden : ∀ i k, lower ≤ a i + b k) :
    weightedError E a b ≤ (2 / lower) * frobeniusSq E := by
  unfold weightedError frobeniusSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  calc
    2 * ‖E i k‖ ^ 2 / (a i + b k) ≤ 2 * ‖E i k‖ ^ 2 / lower :=
      div_le_div_of_nonneg_left (by positivity) hlower (hden i k)
    _ = (2 / lower) * ‖E i k‖ ^ 2 := by ring

/-- The full per-shell conclusion of Lemma 5.1 in frozen/remaining block
coordinates. The local Frobenius error concerns the actual four-block error
matrix. Later refinement acts by a genuine unitary matrix on the remaining
coordinates. The frozen eigenvalue threshold alone bounds all three Bures
contributions, including both ordered cross blocks. -/
theorem block_shell_bures_bound
    {f r : Type*} [Fintype f] [Fintype r] [DecidableEq r]
    (F : Matrix f f ℂ) (B : Matrix f r ℂ) (C : Matrix r f ℂ)
    (D : Matrix r r ℂ) (U : Matrix r r ℂ)
    (a : f → ℝ) (b : r → ℝ) (lower η : ℝ)
    (hU : U * Uᴴ = 1) (hlower : 0 < lower)
    (ha : ∀ i, lower ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hlocal : frobeniusSq (Matrix.fromBlocks F B C D) ≤ η) :
    weightedError F a a + weightedError (B * U) a b +
      weightedError (Uᴴ * C) b a ≤ 2 * η / lower := by
  have hF := weightedError_le F a a lower hlower (fun i k => by
    have := ha i
    have := ha k
    linarith)
  have hB := weightedError_le (B * U) a b lower hlower (fun i k => by
    have := ha i
    have := hb k
    linarith)
  have hC := weightedError_le (Uᴴ * C) b a lower hlower (fun i k => by
    have := hb i
    have := ha k
    linarith)
  have hshell := shell_error_after_remaining_rotation F B C D U η hU hlocal
  have hmult := mul_le_mul_of_nonneg_left hshell (show 0 ≤ 2 / lower by positivity)
  calc
    weightedError F a a + weightedError (B * U) a b +
        weightedError (Uᴴ * C) b a ≤
        (2 / lower) * frobeniusSq F + (2 / lower) * frobeniusSq (B * U) +
          (2 / lower) * frobeniusSq (Uᴴ * C) := by linarith
    _ = (2 / lower) * (frobeniusSq F + frobeniusSq (B * U) +
        frobeniusSq (Uᴴ * C)) := by ring
    _ ≤ (2 / lower) * η := hmult
    _ = 2 * η / lower := by ring

end Paper26.ShellAccounting

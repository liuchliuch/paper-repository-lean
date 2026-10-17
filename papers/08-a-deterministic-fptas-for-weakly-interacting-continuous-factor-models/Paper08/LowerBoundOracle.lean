import Paper08.LowerBound

/-! Exact-value deterministic adaptive oracle machines and their transcript invariance.
The decision at any point depends only on the finite history of earlier queries and answers.
No computability, termination, or query-budget assumption is imposed on the policy. -/
noncomputable section
open scoped Real BigOperators
namespace Paper08.LowerBound

/-- A deterministic adaptive machine chooses another query or returns a number. -/
def ValuePolicy (Q : Type*) := List (Q × ℝ) → Q ⊕ ℝ

/-- The history after `n` transitions. A halted machine leaves its history fixed. -/
def valueTranscript {Q : Type*} (A : ValuePolicy Q) (ψ : Q → ℝ) : ℕ → List (Q × ℝ)
  | 0 => []
  | n + 1 =>
    let h := valueTranscript A ψ n
    match A h with
    | .inl q => h ++ [(q, ψ q)]
    | .inr _ => h

/-- The set of queries made in the first `n` transitions on the all-one oracle. -/
def allOneQueries {Q : Type*} (A : ValuePolicy Q) (n : ℕ) : Finset Q := by
  classical
  exact ((valueTranscript A (fun _ => 1) n).map Prod.fst).toFinset

lemma valueTranscript_sublist_succ {Q : Type*} (A : ValuePolicy Q) (ψ : Q → ℝ) (n : ℕ) :
    List.Sublist (valueTranscript A ψ n) (valueTranscript A ψ (n + 1)) := by
  simp only [valueTranscript]
  split
  · exact List.sublist_append_left _ _
  · exact List.Sublist.refl _

lemma valueTranscript_sublist {Q : Type*} (A : ValuePolicy Q) (ψ : Q → ℝ)
    {i n : ℕ} (h : i ≤ n) : List.Sublist (valueTranscript A ψ i) (valueTranscript A ψ n) := by
  induction h with
  | refl => exact List.Sublist.refl _
  | step h ih => exact ih.trans (valueTranscript_sublist_succ A ψ _)

lemma query_mem_allOneQueries {Q : Type*} (A : ValuePolicy Q) {t n : ℕ}
    (ht : t < n) {q : Q}
    (hq : A (valueTranscript A (fun _ => 1) t) = .inl q) :
    q ∈ allOneQueries A n := by
  classical
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨(q, (1 : ℝ)), ?_, rfl⟩
  have hin : (q, (1 : ℝ)) ∈ valueTranscript A (fun _ => 1) (t + 1) := by
    simp only [valueTranscript, hq]
    exact List.mem_append_right _ (by simp)
  exact (valueTranscript_sublist A (fun _ => 1) (Nat.succ_le_of_lt ht)).subset hin

/-- An oracle agreeing at the finitely many actual baseline queries has the same
entire adaptive history. The induction also covers policies that halt early. -/
theorem valueTranscript_eq_of_allOneQueries {Q : Type*} (A : ValuePolicy Q) (n : ℕ)
    (ψ : Q → ℝ) (hψ : ∀ q ∈ allOneQueries A n, ψ q = 1) :
    valueTranscript A ψ n = valueTranscript A (fun _ => 1) n := by
  have hgen : ∀ i ≤ n, valueTranscript A ψ i = valueTranscript A (fun _ => 1) i := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have heq := ih (by omega)
      simp only [valueTranscript, heq]
      split
      next q hq =>
        rw [hψ q (query_mem_allOneQueries A (by omega) hq)]
      next _ _ => rfl
  exact hgen n le_rfl

/-- In particular the same output is returned on the two instances. -/
theorem same_output_of_allOneQueries {Q : Type*} (A : ValuePolicy Q) (n : ℕ)
    (ψ : Q → ℝ) (hψ : ∀ q ∈ allOneQueries A n, ψ q = 1) {z : ℝ}
    (hz : A (valueTranscript A (fun _ => 1) n) = .inr z) :
    A (valueTranscript A ψ n) = .inr z := by
  rw [valueTranscript_eq_of_allOneQueries A n ψ hψ]
  exact hz

/-- The number of queries made by time `n` is at most `n`. -/
lemma valueTranscript_length_le {Q : Type*} (A : ValuePolicy Q) (ψ : Q → ℝ) (n : ℕ) :
    (valueTranscript A ψ n).length ≤ n := by
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
    simp only [valueTranscript]
    split
    · simpa only [List.length_append, List.length_singleton] using Nat.succ_le_succ ih
    · exact ih.trans (Nat.le_succ _)

/-- At most one distinct query can be introduced by one transition. -/
lemma allOneQueries_card_le {Q : Type*} (A : ValuePolicy Q) (n : ℕ) :
    (allOneQueries A n).card ≤ n := by
  classical
  calc
    _ ≤ ((valueTranscript A (fun _ => 1) n).map Prod.fst).length := List.toFinset_card_le _
    _ = (valueTranscript A (fun _ => 1) n).length := List.length_map _
    _ ≤ n := valueTranscript_length_le A (fun _ => 1) n

/-- One common positive output cannot approximate two positive partition functions
whose logarithms are separated by more than twice the required error. -/
theorem common_output_forces_log_gap {z Z₀ Z₁ ε : ℝ}
    (hz : 0 < z) (hZ₀ : 0 < Z₀) (hZ₁ : 0 < Z₁)
    (h₀ : |Real.log (z / Z₀)| ≤ ε) (h₁ : |Real.log (z / Z₁)| ≤ ε) :
    |Real.log Z₁ - Real.log Z₀| ≤ 2 * ε := by
  rw [Real.log_div hz.ne' hZ₀.ne'] at h₀
  rw [Real.log_div hz.ne' hZ₁.ne'] at h₁
  calc
    |Real.log Z₁ - Real.log Z₀| =
        |(Real.log z - Real.log Z₀) - (Real.log z - Real.log Z₁)| := by congr 1; ring
    _ ≤ |Real.log z - Real.log Z₀| + |Real.log z - Real.log Z₁| := abs_sub _ _
    _ ≤ 2 * ε := by linarith

end Paper08.LowerBound

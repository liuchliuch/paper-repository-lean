import Paper25.SourceChannels
import Paper25.History

/-! # History bounds for actual source channels

The history-matrix hypotheses are discharged from finite Kraus completeness.
Every consecutive product, including the length-zero identity, is an actual
channel; the source's reachable states play no role in its Frobenius bound.
-/
noncomputable section
namespace Paper25
namespace KrausChannel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Channel of a consecutive time interval, in temporal order. -/
def sequence (C : ℕ → KrausChannel ι) (start : ℕ) : ℕ → KrausChannel ι
  | 0 => identity
  | len + 1 => (C (start + len)).comp (sequence C start len)

@[simp] theorem liouville_identity :
    (identity : KrausChannel ι).liouville = 1 := by
  ext ⟨a, b⟩ ⟨i, j⟩
  by_cases ha : a = i <;> by_cases hb : b = j <;>
    simp [liouville, identity, Matrix.one_apply, ha, hb, Prod.ext_iff]

/-- The source channel semantics produce exactly the history-matrix product. -/
theorem liouville_sequence (C : ℕ → KrausChannel ι) (start len : ℕ) :
    (sequence C start len).liouville =
      chainProd (fun t => (C t).liouville) start len := by
  induction len with
  | zero => simp [sequence, chainProd_zero]
  | succ len ih => rw [sequence, liouville_comp, ih, chainProd_succ]

/-- Kraus Choi reshuffling preserves the entrywise Frobenius norm for any
finite register type. -/
theorem entryNormSq_choi (C : KrausChannel ι) :
    entryNormSq C.choi = entryNormSq C.liouville := by
  classical
  rw [entryNormSq_eq_sum_prod, entryNormSq_eq_sum_prod]
  let e : ((ι × ι) × (ι × ι)) ≃ ((ι × ι) × (ι × ι)) := reshuffleEquiv
  have h : (fun p : (ι × ι) × (ι × ι) => Complex.normSq (C.choi p.1 p.2)) =
      (fun p : (ι × ι) × (ι × ι) => Complex.normSq (C.liouville p.1 p.2)) ∘ e := by
    funext p
    rfl
  rw [h, ← e.sum_comp]
  rfl

/-- Lemma 3 for a genuine source channel on an arbitrary finite register. -/
theorem liouville_frob_bound_card (C : KrausChannel ι) :
    entryNormSq C.liouville ≤ (Fintype.card ι : ℝ)^2 := by
  rw [← C.entryNormSq_choi]
  apply psd_trace_frob_bound C.choi C.choi_posSemidef
  simpa using C.choi_trace

/-- Reindexing Liouville coordinates does not change the Frobenius norm. -/
theorem reindex_liouville_frob_bound {κ : Type*} [Fintype κ]
    (C : KrausChannel ι) (e : κ ≃ (ι × ι)) :
    entryNormSq (C.liouville.submatrix e e) ≤ (Fintype.card ι : ℝ)^2 := by
  rw [entryNormSq_submatrix_equiv]
  exact C.liouville_frob_bound_card

/-- Arbitrary finite coordinate reindexing commutes with temporal products. -/
theorem liouville_sequence_reindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (C : ℕ → KrausChannel ι) (e : κ ≃ (ι × ι)) (start len : ℕ) :
    (sequence C start len).liouville.submatrix e e =
      chainProd (fun t => (C t).liouville.submatrix e e) start len := by
  induction len with
  | zero => simp [sequence, chainProd_zero]
  | succ len ih =>
    rw [sequence, liouville_comp, ← Matrix.submatrix_mul_equiv _ _ e e e,
      ih, chainProd_succ]

/-- Every consecutive product of reindexed source channels has the genuine
CPTP Frobenius bound, with no additional channel hypothesis. -/
theorem cptpFrobBound_reindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (C : ℕ → KrausChannel ι) (e : κ ≃ (ι × ι)) (T : ℕ) :
    CPTPFrobBound (fun t => (C t).liouville.submatrix e e) T (Fintype.card ι) where
  chain_bound := by
    intro start len _
    change entryNormSq
      (chainProd (fun t => (C t).liouville.submatrix e e) start len) ≤ _
    rw [← liouville_sequence_reindex]
    exact (sequence C start len).reindex_liouville_frob_bound e

/-- All history-block Frobenius hypotheses follow from genuine source channels. -/
theorem cptpFrobBound {d : ℕ} (C : ℕ → KrausChannel (Fin d)) (T : ℕ) :
    CPTPFrobBound (fun t => (C t).liouville) T d where
  chain_bound := by
    intro start len _
    change entryNormSq (chainProd (fun t => (C t).liouville) start len) ≤ (d : ℝ)^2
    rw [← liouville_sequence]
    exact (sequence C start len).liouville_frob_bound

/-- Equation (6) with its mathematical CPTP hypotheses fully discharged. -/
theorem history_frob_bound_of_channels {d T J : ℕ} (C : ℕ → KrausChannel (Fin d)) :
    frobNormSq' ((1 - historyShift T J (fun t => (C t).liouville))⁻¹) ≤
      (J : ℝ)^2 * (d : ℝ)^2 :=
  history_frob_bound _ d (cptpFrobBound C T)

end KrausChannel
end Paper25

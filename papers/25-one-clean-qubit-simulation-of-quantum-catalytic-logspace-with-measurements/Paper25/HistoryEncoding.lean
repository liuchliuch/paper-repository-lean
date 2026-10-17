import Paper25.SelectorLCU
import Paper25.SourceControl
import Paper25.History
import Mathlib.Logic.Equiv.Fin.Rotate

/-! The actual history multiplexer: select a three-ancilla channel encoding,
then cyclically increment the clock. Inactive clock labels encode zero, so
there is no unwanted transition or clock wraparound in its selected block. -/
noncomputable section
open scoped ComplexConjugate
namespace Paper25.HistoryEncoding
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Data order is clock, selector, Liouville register. -/
def clockSelected {T J : ℕ} (K : ℕ → Fin 8 → Matrix ι ι ℂ) (r : Fin J) :
    Matrix (Selector3 × ι) (Selector3 × ι) ℂ :=
  if r.val < T then eightLCU (K r.val) else eightLCU inactiveTerms

lemma clockSelected_unitary {T J : ℕ} (K : ℕ → Fin 8 → Matrix ι ι ℂ)
    (hK : ∀ t < T, ∀ a, K t a ∈ Matrix.unitaryGroup ι ℂ) (r : Fin J) :
    clockSelected (T := T) K r ∈ Matrix.unitaryGroup (Selector3 × ι) ℂ := by
  unfold clockSelected
  split_ifs with h
  · exact eightLCU_unitary _ (hK r.val h)
  · exact eightLCU_unitary _ inactiveTerms_unitary

lemma clockSelected_block {T J : ℕ} (K : ℕ → Fin 8 → Matrix ι ι ℂ)
    (S : ℕ → Matrix ι ι ℂ)
    (havg : ∀ t < T, (1/8:ℂ) • ∑ a, K t a = (1/2:ℂ) • S t)
    (r : Fin J) :
    (clockSelected (T := T) K r).submatrix
      (fun i => (zeroSelector3,i)) (fun i => (zeroSelector3,i)) =
        if r.val < T then (1/2:ℂ) • S r.val else 0 := by
  unfold clockSelected
  split_ifs with h
  · rw [eightLCU_block, havg r.val h]
  · rw [eightLCU_block, inactiveTerms_average]

/-- The physical clock increment, extended by the identity on other registers. -/
def clockAdvance (J : ℕ) :
    (Fin J × (Selector3 × ι)) ≃ (Fin J × (Selector3 × ι)) :=
  (finRotate J).prodCongr (Equiv.refl _)

/-- Select the current source-step encoding, then advance the clock. -/
def rawHistoryUnitary (T J : ℕ) (K : ℕ → Fin 8 → Matrix ι ι ℂ) :
    Matrix (Fin J × (Selector3 × ι)) (Fin J × (Selector3 × ι)) ℂ :=
  KrausChannel.reversibleGate (clockAdvance J) * selectMatrix (clockSelected (T := T) K)

lemma rawHistoryUnitary_unitary {T J : ℕ} (K : ℕ → Fin 8 → Matrix ι ι ℂ)
    (hK : ∀ t < T, ∀ a, K t a ∈ Matrix.unitaryGroup ι ℂ) :
    rawHistoryUnitary T J K ∈ Matrix.unitaryGroup (Fin J × (Selector3 × ι)) ℂ := by
  apply (Matrix.unitaryGroup _ ℂ).mul_mem
  · rw [Matrix.mem_unitaryGroup_iff']
    exact KrausChannel.reversibleGate_unitary _
  · exact selectMatrix_unitary _ (clockSelected_unitary K hK)

lemma rawHistoryUnitary_apply {T J : ℕ} (K : ℕ → Fin 8 → Matrix ι ι ℂ)
    (r q : Fin J) (s t : Selector3) (i j : ι) :
    rawHistoryUnitary T J K (r,(s,i)) (q,(t,j)) =
      if r = finRotate J q then clockSelected (T := T) K q (s,i) (t,j) else 0 := by
  classical
  unfold rawHistoryUnitary
  simp only [KrausChannel.reversibleGate, Matrix.mul_apply, Matrix.submatrix_apply,
    Matrix.one_apply, Fintype.sum_prod_type, clockAdvance, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Equiv.refl_symm, Equiv.refl_apply]
  by_cases hr : r = finRotate J q
  · have hq : (finRotate J).symm r = q := (Equiv.symm_apply_eq _).2 hr
    rcases s with ⟨s₁,s₂,s₃⟩
    fin_cases s₁ <;> fin_cases s₂ <;> fin_cases s₃ <;> simp [selectMatrix, hq, hr]
  · have hq : (finRotate J).symm r ≠ q := by
      intro h
      exact hr ((Equiv.symm_apply_eq _).1 h)
    simp [selectMatrix, hq, hr]

/-- Put the three block ancillas first, leaving clock and data unrestricted. -/
def selectorClockOrder (J : ℕ) :
    (Selector3 × (Fin J × ι)) ≃ (Fin J × (Selector3 × ι)) where
  toFun p := (p.2.1,(p.1,p.2.2))
  invFun p := (p.2.1,(p.1,p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def historyUnitary (T J : ℕ) (K : ℕ → Fin 8 → Matrix ι ι ℂ) :
    Matrix (Selector3 × (Fin J × ι)) (Selector3 × (Fin J × ι)) ℂ :=
  (rawHistoryUnitary T J K).submatrix (selectorClockOrder J) (selectorClockOrder J)

lemma historyUnitary_unitary {T J : ℕ} (K : ℕ → Fin 8 → Matrix ι ι ℂ)
    (hK : ∀ t < T, ∀ a, K t a ∈ Matrix.unitaryGroup ι ℂ) :
    historyUnitary T J K ∈ Matrix.unitaryGroup (Selector3 × (Fin J × ι)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (historyUnitary T J K).conjTranspose * historyUnitary T J K = 1
  have h := (rawHistoryUnitary_unitary (J := J) K hK).1
  change (rawHistoryUnitary T J K).conjTranspose * rawHistoryUnitary T J K = 1 at h
  simpa only [historyUnitary, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_one_equiv] using
      congrArg (fun M => M.submatrix (selectorClockOrder J) (selectorClockOrder J)) h

lemma finRotate_val_of_lt {J T : ℕ} (hJ : T+1≤J) (r : Fin J) (hr : r.val<T) :
    (finRotate J r).val = r.val+1 := by
  cases J with
  | zero => exact Fin.elim0 r
  | succ J =>
    have h : r.val < J := by omega
    have hp := finRotate_of_lt h
    have he : (⟨r.val, by omega⟩ : Fin (J+1)) = r := by ext; rfl
    rw [he] at hp
    exact congrArg Fin.val hp

/-- The actual multiplexer has the desired `L/2` block on all clock values. -/
theorem historyUnitary_block {T J : ℕ} (K : ℕ → Fin 8 → Matrix ι ι ℂ)
    (S : ℕ → Matrix ι ι ℂ) (hJ : T+1≤J)
    (havg : ∀ t < T, (1/8:ℂ) • ∑ a, K t a = (1/2:ℂ) • S t) :
    (historyUnitary T J K).submatrix
      (fun i => (zeroSelector3,i)) (fun i => (zeroSelector3,i)) =
        (1/2:ℂ) • historyShift T J S := by
  ext ⟨r,i⟩ ⟨q,j⟩
  change rawHistoryUnitary T J K (r,(zeroSelector3,i)) (q,(zeroSelector3,j)) = _
  rw [rawHistoryUnitary_apply]
  have hb := congrFun (congrFun (clockSelected_block K S havg q) i) j
  simp only [Matrix.submatrix_apply] at hb
  by_cases hq : q.val < T
  · rw [if_pos hq] at hb
    rw [hb]
    have he : r = finRotate J q ↔ r.val = q.val+1 := by
      rw [← finRotate_val_of_lt hJ q hq]
      exact Fin.ext_iff
    simp [historyShift, he, hq, Matrix.smul_apply]
  · rw [if_neg hq] at hb
    rw [hb]
    simp [historyShift, hq, Matrix.smul_apply]

/-- The additional √1/3,√2/3 selector and its original four block ancillas. -/
def historyAEncoding (T J : ℕ) (K : ℕ → Fin 8 → Matrix ι ι ℂ) :=
  lcuMatrix prepareThird ![1, -(historyUnitary T J K)]

lemma historyAEncoding_unitary {T J : ℕ} (K : ℕ → Fin 8 → Matrix ι ι ℂ)
    (hK : ∀ t < T, ∀ a, K t a ∈ Matrix.unitaryGroup ι ℂ) :
    historyAEncoding T J K ∈ Matrix.unitaryGroup (Fin 2 × (Selector3 × (Fin J × ι))) ℂ := by
  apply lcuMatrix_unitary _ _ prepareThird_unitary
  intro j
  fin_cases j
  · exact (Matrix.unitaryGroup _ ℂ).one_mem
  · change -(historyUnitary T J K) ∈ Matrix.unitaryGroup _ ℂ
    simpa only [neg_one_smul] using
      phase_unitary (-1) (historyUnitary T J K) (by norm_num)
        (historyUnitary_unitary K hK)

theorem historyAEncoding_block {T J : ℕ} (K : ℕ → Fin 8 → Matrix ι ι ℂ)
    (S : ℕ → Matrix ι ι ℂ) (hJ : T+1≤J)
    (havg : ∀ t < T, (1/8:ℂ) • ∑ a, K t a = (1/2:ℂ) • S t) :
    (historyAEncoding T J K).submatrix
      (fun i => (0,(zeroSelector3,i))) (fun i => (0,(zeroSelector3,i))) =
        (1/3:ℂ) • (1 - historyShift T J S) :=
  history_lcu_block zeroSelector3 _ _ (historyUnitary_block K S hJ havg)

abbrev BlockAncilla := Fin 2 × Selector3

/-- The four original block ancillas followed by the enumerated clock/data
register, in the interface used by the compression walk. -/
def encodingIndex (J : ℕ) :
    (BlockAncilla × Fin (Fintype.card (Fin J × ι))) ≃
      (Fin 2 × (Selector3 × (Fin J × ι))) where
  toFun p := (p.1.1, (p.1.2, (Fintype.equivFin (Fin J × ι)).symm p.2))
  invFun p := ((p.1,p.2.1), Fintype.equivFin (Fin J × ι) p.2.2)
  left_inv p := by rcases p with ⟨⟨b,s⟩,i⟩; simp
  right_inv p := by rcases p with ⟨b,s,i⟩; simp

def enumeratedAEncoding (T J : ℕ) (K : ℕ → Fin 8 → Matrix ι ι ℂ) :
    Matrix (BlockAncilla × Fin (Fintype.card (Fin J × ι)))
      (BlockAncilla × Fin (Fintype.card (Fin J × ι))) ℂ :=
  (historyAEncoding T J K).submatrix (encodingIndex J) (encodingIndex J)

lemma enumeratedAEncoding_unitary {T J : ℕ} (K : ℕ → Fin 8 → Matrix ι ι ℂ)
    (hK : ∀ t < T, ∀ a, K t a ∈ Matrix.unitaryGroup ι ℂ) :
    enumeratedAEncoding T J K ∈ Matrix.unitaryGroup
      (BlockAncilla × Fin (Fintype.card (Fin J × ι))) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (enumeratedAEncoding T J K).conjTranspose * enumeratedAEncoding T J K = 1
  unfold enumeratedAEncoding
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  have h : (historyAEncoding T J K).conjTranspose * historyAEncoding T J K = 1 :=
    (historyAEncoding_unitary K hK).1
  rw [h, Matrix.submatrix_one_equiv]

/-- The actual source-channel multiplexer discharges the full `hA` premise
of the coherent-filter compression theorem. -/
theorem enumeratedAEncoding_block {T J : ℕ} (K : ℕ → Fin 8 → Matrix ι ι ℂ)
    (S : ℕ → Matrix ι ι ℂ) (hJ : T+1≤J)
    (havg : ∀ t < T, (1/8:ℂ) • ∑ a, K t a = (1/2:ℂ) • S t) :
    (enumeratedAEncoding T J K).submatrix
      (fun i => ((0,zeroSelector3),i)) (fun i => ((0,zeroSelector3),i)) =
        (1/3:ℂ) • Matrix.reindex (Fintype.equivFin (Fin J × ι))
          (Fintype.equivFin (Fin J × ι)) (1 - historyShift T J S) := by
  ext i j
  have h := congrArg (fun M : Matrix (Fin J × ι) (Fin J × ι) ℂ =>
    M ((Fintype.equivFin (Fin J × ι)).symm i)
      ((Fintype.equivFin (Fin J × ι)).symm j)) (historyAEncoding_block K S hJ havg)
  exact h

end Paper25.HistoryEncoding

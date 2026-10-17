import Paper22.TensorPetzMoment

/-! Product input laws and the actual iid Petz moment bound. -/
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace Paper22
variable {n d n' d' : ℕ}

theorem petzPowerMixture_relabel (V : CQChannel n d) (q : Fin n → ℝ)
    (en : Fin n' ≃ Fin n) (ed : Fin d' ≃ Fin d) {α : ℝ} (hα : 0 ≤ α) :
    petzPowerMixture (V.relabel en ed) (q ∘ en) α =
      (petzPowerMixture V q α).submatrix ed ed := by
  unfold petzPowerMixture
  have hterm (x : Fin n') : CFC.rpow ((V.relabel en ed).states x) α =
      (CFC.rpow (V.states (en x)) α).submatrix ed ed :=
    matrix_rpow_reindex ed.symm (V.isDensity (en x)).nonneg hα
  simp_rw [hterm]
  ext i j
  simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.submatrix_apply,Function.comp_apply]
  exact en.sum_comp (fun x => q x • CFC.rpow (V.states x) α (ed i) (ed j))

theorem petzPowerMoment_relabel (V : CQChannel n d) {q : Fin n → ℝ}
    (hq : ∀ x, 0 ≤ q x) (en : Fin n' ≃ Fin n) (ed : Fin d' ≃ Fin d)
    {α : ℝ} (hα : 0 < α) :
    (CFC.rpow (petzPowerMixture (V.relabel en ed) (q ∘ en) α) (1/α)).trace.re =
      (CFC.rpow (petzPowerMixture V q α) (1/α)).trace.re := by
  rw [petzPowerMixture_relabel V q en ed hα.le]
  have he := matrix_rpow_reindex ed.symm (petzPowerMixture_nonneg V hq α)
    (one_div_nonneg.mpr hα.le)
  simp only [Equiv.symm_symm] at he
  rw [he,trace_submatrix_equiv]

/-- The actual product input distribution in the same reindexing convention as
tensorPowerFamily. Nat.rec keeps the definition total in the Lean kernel. -/
def tensorPowerWeights (q : Fin n → ℝ) (k : ℕ) : Fin (n^k) → ℝ :=
  Nat.rec (motive := fun k => Fin (n^k) → ℝ) (fun _ => 1)
    (fun k previous => productWeights previous q ∘ finCongr (Nat.pow_succ n k)) k

theorem tensorPowerWeights_probability {q : Fin n → ℝ}
    (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x=1) (k : ℕ) :
    (∀ a, 0 ≤ tensorPowerWeights q k a) ∧ ∑ a, tensorPowerWeights q k a=1 := by
  induction k with
  | zero => simp [tensorPowerWeights]
  | succ k ih =>
    have hprod := productWeights_probability ih.1 ih.2 hq0 hq1
    constructor
    · exact fun a => hprod.1 _
    · change (∑ a, productWeights (tensorPowerWeights q k) q (finCongr (Nat.pow_succ n k) a))=1
      rw [(finCongr (Nat.pow_succ n k)).sum_comp]
      exact hprod.2

/-- The Petz power moment of an actual tensor block is the single-letter
moment raised to the block length. -/
theorem petzPowerMoment_tensorPower (V : CQChannel n d) {q : Fin n → ℝ}
    (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x=1) {α : ℝ} (hα : 0 < α) (k : ℕ) :
    (CFC.rpow (petzPowerMixture (tensorPowerFamily V k) (tensorPowerWeights q k) α) (1/α)).trace.re =
      (CFC.rpow (petzPowerMixture V q α) (1/α)).trace.re ^ k := by
  induction k with
  | zero =>
    change (CFC.rpow (petzPowerMixture tensorUnitChannel (fun _ : Fin 1 => 1) α) (1/α)).trace.re = _
    simp [petzPowerMixture,tensorUnitChannel,CFC.rpow_eq_pow,CFC.one_rpow]
  | succ k ih =>
    change (CFC.rpow (petzPowerMixture
      (((tensorPowerFamily V k).tensor V).relabel
        (finCongr (Nat.pow_succ n k)) (finCongr (Nat.pow_succ d k)))
      (productWeights (tensorPowerWeights q k) q ∘ finCongr (Nat.pow_succ n k)) α) (1/α)).trace.re = _
    rw [petzPowerMoment_relabel _ (productWeights_probability
      (tensorPowerWeights_probability hq0 hq1 k).1
      (tensorPowerWeights_probability hq0 hq1 k).2 hq0 hq1).1 _ _ hα,
      petzPowerMoment_tensor _ _ (tensorPowerWeights_probability hq0 hq1 k).1 hq0 hα,
      ih,pow_succ]

/-- A finite-length iid MC achievability bound with no external exponent input. -/
theorem epsMC_tensorPower_le_petz_moment (V : CQChannel n d)
    {q : Fin n → ℝ} (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x=1)
    {L α : ℝ} (hL : 0 < L) (hα : α ∈ Set.Ioo 0 1) (k : ℕ) :
    epsMC (tensorPowerFamily V k) L ≤
      (L ^ (1-α) * (((CFC.rpow (petzPowerMixture V q α) (1/α)).trace.re ^ k) ^ α)) ^ (1/α) := by
  have h := epsMC_le_petz_moment (tensorPowerFamily V k)
    (tensorPowerWeights_probability hq0 hq1 k).1 (tensorPowerWeights_probability hq0 hq1 k).2 hL hα
  rwa [petzPowerMoment_tensorPower V hq0 hq1 hα.1] at h

end Paper22
end

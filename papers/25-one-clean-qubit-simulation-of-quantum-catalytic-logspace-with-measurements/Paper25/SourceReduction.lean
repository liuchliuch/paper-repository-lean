import Paper25.RestorationLiouville
import Paper25.Reduction

/-! The catalytic trace and dimension-independent regularization bounds for
actual source channels. The caller supplies only exact catalyst marginal
restoration on density operators; all Liouville, normalization and channel
history hypotheses are discharged here. -/
noncomputable section
namespace Paper25.SourceReduction
open SourceBias
open scoped ComplexOrder

variable {α V : Type*} [Fintype α] [Fintype V] [DecidableEq α] [DecidableEq V]

/-- The reordered and enumerated Liouville matrices of the real source steps. -/
def coordinates (C : ℕ → KrausChannel (Work α × V)) :
    ℕ → Matrix (Fin ((Fintype.card (Work α))^2) × Fin ((Fintype.card V)^2))
      (Fin ((Fintype.card (Work α))^2) × Fin ((Fintype.card V)^2)) ℂ :=
  fun t => (sourceLiouville (C t)).submatrix
    ((operatorIndex (Work α)).prodCongr (operatorIndex V))
    ((operatorIndex (Work α)).prodCongr (operatorIndex V))

lemma cleanWork_eq_single {ι : Type*} [DecidableEq ι] (w : ι) :
    cleanWork w = Matrix.single w w (1 : ℂ) := by
  ext i j
  by_cases hij : i = j <;> by_cases hi : i = w <;>
    simp [cleanWork, Matrix.diagonal_apply, Matrix.single, hij, hi, eq_comm] <;> aesop

/-- The actual acceptance Born probability, reading work output bit one and
tracing all other work and catalyst registers. -/
def sourceAccept (ρ : Matrix (Work α × V) (Work α × V) ℂ) : ℝ :=
  (∑ a : α, ∑ v : V, ρ ((1,a),v) ((1,a),v)).re

lemma sourceAccept_product (η : Matrix (Work α) (Work α) ℂ)
    (σ : Matrix V V ℂ) (ht : Matrix.trace σ = 1) :
    sourceAccept (Matrix.kronecker η σ) = SourceBias.accept η := by
  unfold sourceAccept SourceBias.accept
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]
  simp_rw [← Finset.mul_sum]
  have hs : (∑ v : V, σ v v) = 1 := ht
  rw [hs]
  simp [Complex.re_sum]

/-- Equations (3), (4), (9), and (10), with the concrete signed source
observable and the exponential catalyst normalization. -/
theorem source_history_reduction [Nonempty α] (C : ℕ → KrausChannel (Work α × V))
    (w0 : Work α) (v0 : V) (T J : ℕ) (hJ : T + 1 ≤ J)
    (hrestore : ∀ ρ, IsDensity ρ →
      workPartialTrace ((KrausChannel.sequence C 0 T).act
        (Matrix.kronecker (Matrix.single w0 w0 1) ρ)) = ρ) :
    ∃ η : Matrix (Work α) (Work α) ℂ, IsDensity η ∧
      (∀ σ : Matrix V V ℂ, Matrix.trace σ = 1 →
        sourceAccept ((KrausChannel.sequence C 0 T).act
          (Matrix.kronecker (Matrix.single w0 w0 1) σ)) = SourceBias.accept η) ∧
      (let S := coordinates C
       let ω := historyOmega w0
       let z := (historyZ : Fin ((Fintype.card (Work α))^2) → ℂ)
       let A := 1 - historyShift T J S
       let Q := historySelector (⟨0, by omega⟩ : Fin J) ⟨T, by omega⟩
         (kronRankOneId (n := (Fintype.card V)^2) ω z)
       Matrix.trace (Q * A⁻¹) / ((Fintype.card V)^2 : ℕ) =
         ((2 * SourceBias.accept η - 1 : ℝ) : ℂ) /
           (Real.sqrt (Fintype.card (Work α)) : ℂ) ∧
       ∀ lam : ℝ, 0 < lam →
         ‖Matrix.trace (Q * matrixRegInv A lam) / ((Fintype.card V)^2 : ℕ) -
           ((2 * SourceBias.accept η - 1 : ℝ) : ℂ) /
             (Real.sqrt (Fintype.card (Work α)) : ℂ)‖ ≤
           (lam / 2) * (J : ℝ)^2 * (Fintype.card (Work α) : ℝ)^2) := by
  classical
  let eW := operatorIndex (Work α)
  let eV := operatorIndex V
  obtain ⟨η,hη,hproduct,hcol⟩ := lemma_2_source_exactRestoration
    (KrausChannel.sequence C 0 T) w0 v0 hrestore eW eV
  refine ⟨η,hη,?_,?_⟩
  · intro σ hσ
    rw [hproduct]
    exact sourceAccept_product η σ hσ
  · dsimp only
    have hrest : ExactRestoration (chainProd (coordinates C) 0 T)
        (historyOmega w0) (historyEta η) := by
      rw [sourceLiouville_sequence, ← chainProd_submatrix_equiv] at hcol
      simpa only [coordinates, historyOmega, historyEta, cleanWork_eq_single,
        vecOp, operatorVec, eW, eV] using hcol
    have hdim : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v0⟩
    have hn : (((Fintype.card V)^2 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast pow_ne_zero 2 hdim.ne'
    have hinner := history_z_eta_bias η hη.1.isHermitian hη.2
    constructor
    · rw [eq9_history_trace (coordinates C) hJ _ _ _ hrest hn, hinner]
    · intro lam hlam
      have hb := sourceLiouville_cptpFrobBound C (eW.prodCongr eV) T
      have hr := history_normalized_regularization (coordinates C) hJ hdim hb
        (historyOmega w0) (historyEta η) historyZ
        (historyOmega_normalized w0) historyZ_normalized hrest lam hlam
      simpa only [hinner] using hr

end Paper25.SourceReduction

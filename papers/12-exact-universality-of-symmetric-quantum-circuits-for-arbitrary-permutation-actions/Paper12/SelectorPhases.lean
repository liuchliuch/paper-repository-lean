import Paper12.SelectionStages
import Paper12.BlockEncoding

noncomputable section
namespace Paper12
open Matrix Classical
variable {Q X : Type*} [Fintype Q] [Fintype X]
local instance selectorDecidable (α : Coeffs X) : DecidableEq (SelectorWire α) := Classical.decEq _

def selectorDiagonal (z : ℂ) : QMat := Matrix.diagonal (fun v : Fin 2 => if v = 0 then 1 else z)

theorem selectorDiagonal_unitary (z : ℂ) (hz : star z * z = 1) :
    (selectorDiagonal z)ᴴ * selectorDiagonal z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [selectorDiagonal, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  exact hz

def selectorPhaseCircuit (ω : Q → ℂ) (hω : ∀ q, star (ω q) * ω q = 1) : Circuit Q :=
  parallelCircuit (fun q => selectorDiagonal (ω q)) (fun q => selectorDiagonal_unitary _ (hω q))

theorem tensor_diagonal (m : Q → Fin 2 → ℂ) :
    tensorOp (fun q => Matrix.diagonal (m q)) = Matrix.diagonal (fun b : Basis Q => ∏ q, m q (b q)) := by
  ext i j
  by_cases h : i = j
  · subst j; simp [tensorOp]
  · obtain ⟨q, hq⟩ := Function.ne_iff.mp h
    rw [Matrix.diagonal_apply_ne _ h]
    exact Finset.prod_eq_zero (Finset.mem_univ q) (by simp [Matrix.diagonal_apply_ne _ hq])

theorem selectorPhaseCircuit_oneHot (ω : Q → ℂ) (hω : ∀ q, star (ω q) * ω q = 1) (q : Q) :
    applyOp (selectorPhaseCircuit ω hω).unitary (eBasis (oneHot q)) = ω q • eBasis (oneHot q) := by
  funext b
  simp only [selectorPhaseCircuit, parallelCircuit_unitary, selectorDiagonal]
  rw [tensor_diagonal, applyOp_eBasis]
  have hp : (∏ r : Q, if oneHot q r = 0 then (1 : ℂ) else ω r) = ω q := by
    rw [Finset.prod_eq_single q]
    · simp [oneHot]
    · intro r _ hr
      simp [oneHot, hr]
    · simp
  by_cases hb : b = oneHot q
  · subst b
    simp [Matrix.diagonal_apply, hp, eBasis]
  · simp [Matrix.diagonal_apply_ne _ hb, eBasis, hb]

theorem selectorPhaseCircuit_preserved (ω : Q → ℂ) (hω : ∀ q, star (ω q) * ω q = 1)
    (τ : Q ≃ Q) (hw : ∀ q, ω (τ q) = ω q) :
    (selectorPhaseCircuit ω hω).Preserved τ := by
  intro L hL
  simp only [selectorPhaseCircuit, parallelCircuit, List.mem_singleton] at hL
  subst L
  exact parallelLayer_map _ _ τ (fun q => congrArg selectorDiagonal (hw q))

theorem selectorPhase_unit (α : Coeffs X) (q : SelectorWire α) :
    star (selectorPhase α q.val) * selectorPhase α q.val = 1 := by
  have hn : α q.val ≠ 0 := by
    have hq := q.property
    simpa only [coeffSupport, Finset.mem_filter, Finset.mem_univ, true_and] using hq
  have ha : (Complex.abs (α q.val) : ℂ) ≠ 0 := by
    exact_mod_cast abs_ne_zero_of_mem_support α q.property
  have hsq : ((Complex.abs (α q.val) : ℝ) : ℂ) ^ 2 =
      star (α q.val) * α q.val := by
    rw [← _root_.Complex.ofReal_pow, Complex.abs_sq]
    exact _root_.Complex.normSq_eq_conj_mul_self
  simp only [selectorPhase, if_neg hn, star_div₀, _root_.Complex.star_def, _root_.Complex.conj_ofReal]
  rw [div_mul_div_comm]
  change (star (α q.val) * α q.val) /
    ((Complex.abs (α q.val) : ℂ) * (Complex.abs (α q.val) : ℂ)) = 1
  rw [← pow_two, ← hsq]
  exact div_self (pow_ne_zero _ ha)

def fullSelection (α : Coeffs X) : Circuit (X ⊕ SelectorWire α) :=
  ((selectorPhaseCircuit (fun q : SelectorWire α => selectorPhase α q.val)
    (selectorPhase_unit α)).onRight (J := X)).mul (pauliSelection (fun q => q.val))

theorem fullSelection_sector (α : Coeffs X) (q : SelectorWire α) (ψ : Vec X) :
    applyOp (fullSelection α).unitary (registerVec ψ (eBasis (oneHot q))) =
      selectorPhase α q.val • registerVec (applyOp (pop X q.val) ψ) (eBasis (oneHot q)) := by
  rw [fullSelection, Circuit.mul_unitary, applyOp_mul, pauliSelection_sector (fun q : SelectorWire α => q.val) q ψ,
    Circuit.onRight_unitary, registerTensor_apply, applyOp_one, selectorPhaseCircuit_oneHot]
  funext b
  simp only [registerVec, Pi.smul_apply, smul_eq_mul]
  ring

theorem fullSelection_size (α : Coeffs X) :
    (fullSelection α).size ≤ 3 * coeffCard α * Fintype.card X +
      6 * Fintype.card X + coeffCard α := by
  simp only [fullSelection, Circuit.mul_size, Circuit.onRight_size, selectorPhaseCircuit,
    parallelCircuit_size, selectorWire_card]
  have h := pauliSelection_size (fun q : SelectorWire α => q.val)
  rw [selectorWire_card] at h
  omega
end Paper12

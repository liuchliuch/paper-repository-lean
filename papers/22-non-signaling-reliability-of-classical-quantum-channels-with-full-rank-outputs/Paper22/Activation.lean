import Paper22.BitBlocks
import Paper22.ProgramsSDP
import Paper22.OneShot

/-! Constructive one-bit activation for the actual matrix semidefinite programs. -/
open scoped MatrixOrder ComplexOrder
open Matrix
noncomputable section
namespace Paper22
set_option maxHeartbeats 600000
variable {n d : ℕ}

/-- Split each input probability equally between the two classical labels. -/
def activationWeights (q : Fin n → ℝ) (a : Fin (n * 2)) : ℝ :=
  q (finProdFinEquiv.symm a).1 / 2

/-- The unused output block receives the positive normalization defect. -/
def activationOperators (q : Fin n → ℝ) (S : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (H : Matrix (Fin d) (Fin d) ℂ) (a : Fin (n * 2)) :
    Matrix (Fin (d * 2)) (Fin (d * 2)) ℂ :=
  (1 / 2 : ℝ) • bitDiagonal (fun c => if c = (finProdFinEquiv.symm a).2
    then S (finProdFinEquiv.symm a).1 else q (finProdFinEquiv.symm a).1 • H)

@[simp] theorem activationWeights_prod (q : Fin n → ℝ) (x : Fin n) (b : Fin 2) :
    activationWeights q (finProdFinEquiv (x,b)) = q x / 2 := by simp [activationWeights]

@[simp] theorem activationOperators_prod (q : Fin n → ℝ)
    (S : Fin n → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ)
    (x : Fin n) (b : Fin 2) :
    activationOperators q S H (finProdFinEquiv (x,b)) =
      (1 / 2 : ℝ) • bitDiagonal (fun c => if c = b then S x else q x • H) := by
  simp [activationOperators]

theorem activationWeights_probability {q : Fin n → ℝ}
    (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1) :
    (∀ a, 0 ≤ activationWeights q a) ∧ ∑ a, activationWeights q a = 1 := by
  refine ⟨fun a => div_nonneg (hq0 _) (by norm_num), ?_⟩
  rw [sum_bit_indices]
  simp only [activationWeights_prod, Fin.sum_univ_two]
  simp_rw [add_halves]
  exact hq1

/-- Complete a relaxed source SDP using the unused classical output blocks. -/
theorem MCSDPFeasible.activation {m : ℕ} (hm : 1 ≤ m) {q : Fin n → ℝ}
    {S : Fin n → Matrix (Fin d) (Fin d) ℂ} (h : MCSDPFeasible (m : ℝ) q S) :
    NSSDPFeasible (2 * m) (activationWeights q)
      (activationOperators q S ((1 / (m : ℝ)) • 1 - ∑ x, S x)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let A := ∑ x, S x
  let H := (1 / (m : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ) - A
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun x _ => (h.2.2.1 x).1
  have hH0 : 0 ≤ H := sub_nonneg.mpr h.2.2.2
  have hH1 : H ≤ 1 := by
    apply (sub_le_self _ hA0).trans
    have hf : (1 : ℝ) / m ≤ 1 := by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hm1
    simpa only [one_smul] using (matrix_scalar_mono (d := d) hf)
  have hprob := activationWeights_probability h.1 h.2.1
  refine ⟨hprob.1, hprob.2, ?_, ?_⟩
  · intro a
    let x := (finProdFinEquiv.symm a).1
    let b := (finProdFinEquiv.symm a).2
    change 0 ≤ (1 / 2 : ℝ) • bitDiagonal (fun c => if c = b then S x else q x • H) ∧
      (1 / 2 : ℝ) • bitDiagonal (fun c => if c = b then S x else q x • H) ≤
        (q x / 2) • 1
    have hB0 : ∀ c : Fin 2, 0 ≤ (if c = b then S x else q x • H) := by
      intro c; split_ifs
      · exact (h.2.2.1 x).1
      · exact smul_nonneg (h.1 x) hH0
    have hB1 : ∀ c : Fin 2, (if c = b then S x else q x • H) ≤ q x • 1 := by
      intro c; split_ifs
      · exact (h.2.2.1 x).2
      · exact matrix_smul_mono (h.1 x) hH1
    refine ⟨smul_nonneg (by norm_num) (bitDiagonal_nonneg hB0), ?_⟩
    calc _ ≤ (1 / 2 : ℝ) • bitDiagonal (fun _ : Fin 2 => q x • (1 : Matrix (Fin d) (Fin d) ℂ)) :=
        matrix_smul_mono (by norm_num) (bitDiagonal_mono hB1)
      _ = (q x / 2) • 1 := by rw [bitDiagonal_smul, bitDiagonal_one, smul_smul]; congr 1; ring
  · change (∑ a, activationOperators q S H a) = _
    rw [sum_bit_indices]
    simp only [activationOperators_prod, ← Finset.smul_sum, bitDiagonal_swap_sum]
    rw [← bitDiagonal_sum]
    simp only [Finset.sum_add_distrib, ← Finset.sum_smul, h.2.1, one_smul]
    have hAH : (∑ x, S x) + H = (1 / (m : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      dsimp [H, A]; abel
    rw [hAH, bitDiagonal_smul, bitDiagonal_one, smul_smul]
    congr 1
    push_cast
    field_simp

/-- The added blocks carry no probability of a correct classical-bit output. -/
theorem activationOperators_objective (V : CQChannel n d) (q : Fin n → ℝ)
    (S : Fin n → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ) :
    sdpObjective (activationFamily V) (activationOperators q S H) = sdpObjective V S := by
  unfold sdpObjective
  rw [sum_bit_indices]
  simp only [activationOperators_prod, activationFamily_trace, bitCompression_smul,
    bitCompression_diagonal, if_pos rfl, ↓reduceIte, Matrix.mul_smul, Matrix.trace_smul,
    Complex.smul_re, smul_eq_mul, Fin.sum_univ_two]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Sum the weights of the two transmitted classical labels. -/
def compressionWeights (q : Fin (n * 2) → ℝ) (x : Fin n) : ℝ :=
  ∑ b : Fin 2, q (finProdFinEquiv (x,b))

/-- Retain the diagonal block that matches each transmitted bit. -/
def compressionOperators (S : Fin (n * 2) → Matrix (Fin (d * 2)) (Fin (d * 2)) ℂ)
    (x : Fin n) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ b : Fin 2, bitCompression (S (finProdFinEquiv (x,b))) b

/-- Every exactly normalized activated decoder compresses to a relaxed decoder. -/
theorem NSSDPFeasible.compression {N : ℕ} (hN : 1 ≤ N) {q : Fin (n * 2) → ℝ}
    {S : Fin (n * 2) → Matrix (Fin (d * 2)) (Fin (d * 2)) ℂ}
    (h : NSSDPFeasible N q S) :
    MCSDPFeasible ((N : ℝ) / 2) (compressionWeights q) (compressionOperators S) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact Finset.sum_nonneg fun b _ => h.1 _
  · exact (sum_bit_indices q).symm.trans h.2.1
  · intro x
    constructor
    · exact Finset.sum_nonneg fun b _ => bitCompression_nonneg (h.2.2.1 _).1 b
    · change (∑ b : Fin 2, bitCompression (S (finProdFinEquiv (x,b))) b) ≤ _
      calc _ ≤ ∑ b : Fin 2, q (finProdFinEquiv (x,b)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
            apply Finset.sum_le_sum
            intro b _
            simpa only [bitCompression_smul, bitCompression_one] using
              bitCompression_mono (h.2.2.1 (finProdFinEquiv (x,b))).2 b
        _ = _ := Finset.sum_smul.symm
  · have hb (b : Fin 2) : (∑ x : Fin n, bitCompression (S (finProdFinEquiv (x,b))) b) ≤
        (1 / (N : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      calc _ ≤ ∑ x : Fin n, ∑ c : Fin 2, bitCompression (S (finProdFinEquiv (x,c))) b := by
              apply Finset.sum_le_sum
              intro x _
              exact Finset.single_le_sum (s := Finset.univ)
                (f := fun c : Fin 2 => bitCompression (d := d) (S (finProdFinEquiv (x,c))) b)
                (fun c _ => bitCompression_nonneg (h.2.2.1 _).1 b) (Finset.mem_univ b)
          _ = ∑ a, bitCompression (S a) b := (sum_bit_indices (n := n) (fun a => bitCompression (S a) b)).symm
          _ = bitCompression (∑ a, S a) b := (bitCompression_sum S b).symm
          _ = _ := by rw [h.2.2.2, bitCompression_smul, bitCompression_one]
    change (∑ x, ∑ b : Fin 2, bitCompression (S (finProdFinEquiv (x,b))) b) ≤ _
    rw [Finset.sum_comm]
    calc _ ≤ ∑ _b : Fin 2, (1 / (N : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ) :=
            Finset.sum_le_sum fun b _ => hb b
        _ = (1 / ((N : ℝ) / 2)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
          rw [Fin.sum_univ_two, ← add_smul]
          congr 1
          field_simp
          <;> ring

/-- Matching block compression preserves the success objective exactly. -/
theorem compressionOperators_objective (V : CQChannel n d)
    (S : Fin (n * 2) → Matrix (Fin (d * 2)) (Fin (d * 2)) ℂ) :
    sdpObjective V (compressionOperators S) = sdpObjective (activationFamily V) S := by
  unfold sdpObjective
  rw [sum_bit_indices]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  simp only [compressionOperators, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro b _
  exact (activationFamily_trace V x b _).symm

/-- An SDP feasible point bounds the true MC optimum. -/
theorem MCSDPFeasible.error_ge (V : CQChannel n d) {L : ℝ} {q : Fin n → ℝ}
    {S : Fin n → Matrix (Fin d) (Fin d) ℂ} (h : MCSDPFeasible L q S) :
    epsMC V L ≤ sdpObjective V S := by
  obtain ⟨hT, hrec⟩ := h.toEffects
  have ho := programObjective_eq_sdp V h.2.1 (sdpDecoder q S)
  rw [show (fun x => q x • sdpDecoder q S x) = S from funext hrec] at ho
  rw [← ho]
  exact epsMC_le_objective V hT

/-- An SDP feasible point bounds the true NS optimum. -/
theorem NSSDPFeasible.error_ge (V : CQChannel n d) {M : ℕ} {q : Fin n → ℝ}
    {S : Fin n → Matrix (Fin d) (Fin d) ℂ} (h : NSSDPFeasible M q S) :
    epsNS V M ≤ sdpObjective V S := by
  obtain ⟨hT, hrec⟩ := h.toEffects
  have ho := programObjective_eq_sdp V h.2.1 (sdpDecoder q S)
  rw [show (fun x => q x • sdpDecoder q S x) = S from funext hrec] at ho
  rw [← ho]
  exact epsNS_le_objective V hT

/-- One-bit activation, equation (26), proved from the actual matrix programs. -/
theorem activation_identity (V : CQChannel n d) (m : ℕ) (hm : 1 ≤ m) :
    epsNS (activationFamily V) (2 * m) = epsMC V m := by
  by_cases hn : n = 0
  · subst n
    simp
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have h2m : 1 ≤ 2 * m := by omega
  apply le_antisymm
  · obtain ⟨q, T, h⟩ := mc_feasible_nonempty (d := d) hn0 hm0
    apply le_csInf (show ({e | ∃ q T, MCFEasable (m : ℝ) q T ∧
      e = programObjective V.states q T} : Set ℝ).Nonempty from ⟨_, q, T, h, rfl⟩)
    rintro e ⟨q, T, h, rfl⟩
    have ha := (h.toSDP.activation hm).error_ge (activationFamily V)
    rw [activationOperators_objective, ← programObjective_eq_sdp V h.2.1 T] at ha
    exact ha
  · obtain ⟨q, T, h⟩ := ns_feasible_nonempty (d := d * 2) (by omega : 0 < n * 2) h2m
    apply le_csInf (show ({e | ∃ q T, NSFeasible (2 * m) q T ∧
      e = programObjective (activationFamily V).states q T} : Set ℝ).Nonempty from
      ⟨_, q, T, h, rfl⟩)
    rintro e ⟨q, T, h, rfl⟩
    have ha := (h.toSDP.compression h2m).error_ge V
    have hreal : (((2 * m : ℕ) : ℝ) / 2) = m := by push_cast; ring
    rw [hreal, compressionOperators_objective,
      ← programObjective_eq_sdp (activationFamily V) h.2.1 T] at ha
    exact ha


end Paper22
end

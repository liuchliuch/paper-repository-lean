import Paper22.Basic
import Paper22.Programs
import Paper22.EffectCompletion

/-!
# One-shot comparison (Theorem 1)

`ε_MC(M, V) ≤ ε_NS(M, V) ≤ ε_MC(M+6, V)` for every finite cq channel `V` and `M ≥ 2`.
-/

open scoped MatrixOrder ComplexOrder
open Matrix

noncomputable section

namespace Paper22

/-- Increasing an effect towards the identity remains an effect. -/
theorem effect_raise {d : ℕ} {T : Matrix (Fin d) (Fin d) ℂ}
    (hT : IsEffect T) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsEffect (T + t • (1 - T)) ∧ T ≤ T + t • (1 - T) := by
  have hinc : 0 ≤ t • (1 - T) :=
    (hT.one_sub_posSemidef.smul ht0).nonneg
  refine ⟨⟨add_nonneg hT.nonneg hinc, ?_⟩, le_add_of_nonneg_right hinc⟩
  apply le_iff.mpr
  have heq : 1 - (T + t • (1 - T)) = (1 - t) • (1 - T) := by
    simp only [sub_smul, one_smul]
    abel
  rw [heq]
  exact hT.one_sub_posSemidef.smul (sub_nonneg.mpr ht1)

/-- Averaging the explicitly raised effects preserves their affine formula. -/
theorem average_effect_raise {n d : ℕ} (q : Fin n → ℝ)
    (T : Fin n → Matrix (Fin d) (Fin d) ℂ) (hq : ∑ x, q x = 1) (t : ℝ) :
    (∑ x, q x • (T x + t • (1 - T x))) =
      (∑ x, q x • T x) + t • (1 - ∑ x, q x • T x) := by
  simp_rw [smul_add, smul_sub, smul_comm (q _) t]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.smul_sum, ← Finset.smul_sum, ← Finset.sum_smul, hq, one_smul]

/-- Explicit feasibility conversion used in NS monotonicity. -/
theorem NSFeasible.lower {n d : ℕ} {L N : ℕ} {q : Fin n → ℝ}
    {T : Fin n → Matrix (Fin d) (Fin d) ℂ} (h : NSFeasible N q T)
    (hL : 1 ≤ L) (hLN : L ≤ N) :
    ∃ Q, NSFeasible L q Q ∧ ∀ x, T x ≤ Q x := by
  by_cases he : L = N
  · subst L
    exact ⟨T, h, fun _ => le_refl _⟩
  have hN : 1 < N := by omega
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hLNr : (L : ℝ) ≤ N := by exact_mod_cast hLN
  have hLi : (1 / L : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hLr
  have hNi : (1 / N : ℝ) < 1 := (div_lt_one (by linarith)).mpr hNr
  have hinv : (1 / N : ℝ) ≤ 1 / L := one_div_le_one_div_of_le (by linarith) hLNr
  let t : ℝ := (1 / L - 1 / N) / (1 - 1 / N)
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hinv) (by linarith)
  have ht1 : t ≤ 1 := (div_le_one (by linarith : (0 : ℝ) < 1 - 1 / N)).mpr
    (by linarith)
  refine ⟨fun x => T x + t • (1 - T x), ?_,
    fun x => (effect_raise (h.2.2.1 x) ht0 ht1).2⟩
  refine ⟨h.1, h.2.1, fun x => (effect_raise (h.2.2.1 x) ht0 ht1).1, ?_⟩
  rw [average_effect_raise q T h.2.1, h.2.2.2]
  have hcoef : (1 / N : ℝ) + t * (1 - 1 / N) = 1 / L := by
    dsimp [t]
    rw [div_mul_cancel₀ _ (by linarith : (1 : ℝ) - 1 / N ≠ 0)]
    ring
  calc
    _ = ((1 / N : ℝ) + t * (1 - 1 / N)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      rw [add_smul, MulAction.mul_smul, sub_smul, one_smul]
    _ = _ := by rw [hcoef]

/-- Meta-converse error is nondecreasing in the message parameter. -/
theorem epsMC_mono {n d : ℕ} (V : CQChannel n d) {L₁ L₂ : ℝ}
    (h1 : 1 ≤ L₁) (h2 : L₁ ≤ L₂) : epsMC V L₁ ≤ epsMC V L₂ := by
  by_cases he : n = 0
  · subst n; simp
  obtain ⟨q, T, h⟩ := mc_feasible_nonempty (d := d) (Nat.pos_of_ne_zero he)
    (show 0 ≤ L₂ by linarith)
  apply le_csInf (show ({e | ∃ q T, MCFEasable L₂ q T ∧
      e = programObjective V.states q T} : Set ℝ).Nonempty from ⟨_, q, T, h, rfl⟩)
  rintro e ⟨q, T, h, rfl⟩
  exact epsMC_le_objective V (h.mono (by linarith) h2)

/-- Non-signaling error is nondecreasing in the integer message count. -/
theorem epsNS_mono {n d : ℕ} (V : CQChannel n d) {L N : ℕ}
    (hL : 1 ≤ L) (hLN : L ≤ N) : epsNS V L ≤ epsNS V N := by
  by_cases he : n = 0
  · subst n; simp
  obtain ⟨q, T, h⟩ := ns_feasible_nonempty (d := d) (Nat.pos_of_ne_zero he)
    (hL.trans hLN)
  apply le_csInf (show ({e | ∃ q T, NSFeasible N q T ∧
      e = programObjective V.states q T} : Set ℝ).Nonempty from ⟨_, q, T, h, rfl⟩)
  rintro e ⟨q, T, h, rfl⟩
  obtain ⟨Q, hQ, hTQ⟩ := h.lower hL hLN
  exact (epsNS_le_objective V hQ).trans (programObjective_antitone V h.1 hTQ)

/-- Relaxing the exact normalization gives the meta-converse lower bound. -/
theorem epsMC_le_epsNS {n d : ℕ} (V : CQChannel n d) {M : ℕ} (hM : 1 ≤ M) :
    epsMC V M ≤ epsNS V M := by
  by_cases he : n = 0
  · subst n; simp
  obtain ⟨q, T, h⟩ := ns_feasible_nonempty (d := d) (Nat.pos_of_ne_zero he) hM
  apply le_csInf (show ({e | ∃ q T, NSFeasible M q T ∧
      e = programObjective V.states q T} : Set ℝ).Nonempty from ⟨_, q, T, h, rfl⟩)
  rintro e ⟨q, T, h, rfl⟩
  exact epsMC_le_objective V h.toMC

/-- **Theorem 1 (One-shot comparison).**
The proof completes every feasible MC family, so it also proves the comparison
of infima without an additional existence-of-minimizers hypothesis. -/
theorem theorem_one_shot {n d : ℕ} (V : CQChannel n d) (M : ℕ) (hM : 2 ≤ M) :
    epsMC V M ≤ epsNS V M ∧ epsNS V M ≤ epsMC V (M + 6) := by
  refine ⟨epsMC_le_epsNS V (by omega), ?_⟩
  by_cases he : n = 0
  · subst n; simp
  obtain ⟨q, T, h⟩ := mc_feasible_nonempty (d := d) (Nat.pos_of_ne_zero he)
    (show (0 : ℝ) ≤ M + 6 by positivity)
  apply le_csInf (show ({e | ∃ q T, MCFEasable ((M : ℝ) + 6) q T ∧
      e = programObjective V.states q T} : Set ℝ).Nonempty from ⟨_, q, T, h, rfl⟩)
  rintro e ⟨q, T, h, rfl⟩
  obtain ⟨Q, hQ, hTQ, hsum⟩ := lemma_effect_completion M hM (M + 6) rfl
    q h.1 h.2.1 T h.2.2.1 (by simpa only [Nat.cast_add, Nat.cast_ofNat] using h.2.2.2)
  exact (epsNS_le_objective V ⟨h.1, h.2.1, hQ, hsum⟩).trans
    (programObjective_antitone V h.1 hTQ)

end Paper22

end

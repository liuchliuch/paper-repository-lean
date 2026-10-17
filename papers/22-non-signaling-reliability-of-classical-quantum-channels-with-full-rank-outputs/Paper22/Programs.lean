import Paper22.Basic

/-!
# Meta-converse and non-signaling cq coding programs

For a finite cq channel `V : CQChannel n d` and a real message parameter `L ≥ 1`,
the meta-converse program minimizes the average error over effects whose
`q`-average is at most `(1/L) • I`.  The non-signaling program (integer `M ≥ 1`)
replaces that inequality by the equality `∑ qₓ Tₓ = (1/M) • I`.
-/

open scoped MatrixOrder ComplexOrder
open Matrix

noncomputable section

namespace Paper22

variable {n d : ℕ}

/-- Feasible pairs `(q, T)` for the meta-converse program at real parameter `L ≥ 1`. -/
def MCFEasable {n d : ℕ} (L : ℝ) (q : Fin n → ℝ) (T : Fin n → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1)
    ∧ (∀ x, IsEffect (T x))
    ∧ ((∑ x, q x • T x) ≤ (1 / L : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ))

/-- Feasible pairs `(q, T)` for the non-signaling program at integer message count `M`. -/
def NSFeasible {n d : ℕ} (M : ℕ) (q : Fin n → ℝ) (T : Fin n → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1)
    ∧ (∀ x, IsEffect (T x))
    ∧ ((∑ x, q x • T x) = (1 / M : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ))

/-- The meta-converse error `ε_MC(L, V)`. -/
def epsMC {n d : ℕ} (V : CQChannel n d) (L : ℝ) : ℝ :=
  sInf {e | ∃ (q : Fin n → ℝ) (T : Fin n → Matrix (Fin d) (Fin d) ℂ),
    MCFEasable L q T ∧ e = programObjective V.states q T}

/-- The non-signaling error `ε_NS(M, V)` for integer `M`. -/
def epsNS {n d : ℕ} (V : CQChannel n d) (M : ℕ) : ℝ :=
  sInf {e | ∃ (q : Fin n → ℝ) (T : Fin n → Matrix (Fin d) (Fin d) ℂ),
    NSFeasible M q T ∧ e = programObjective V.states q T}

/-- The real trace of a product of positive semidefinite matrices is nonnegative.
The factors need not commute. -/
theorem trace_mul_nonneg_re {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  let C := CFC.sqrt A
  have hC : C.IsHermitian := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have hCC : C * C = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hp := (hB.mul_mul_conjTranspose_same C).trace_nonneg
  rw [hC.eq] at hp
  have ht : (C * B * C).trace = (A * B).trace := by
    rw [Matrix.trace_mul_cycle, hCC]
  rw [ht] at hp
  exact hp.1

/-- Testing a PSD inequality against a PSD state preserves the real trace order. -/
theorem trace_mul_mono_re {A B C : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosSemidef) (hBC : B ≤ C) :
    (A * B).trace.re ≤ (A * C).trace.re := by
  have h := trace_mul_nonneg_re hA (le_iff.mp hBC)
  simpa only [mul_sub, trace_sub, Complex.sub_re, sub_nonneg] using h

/-- The coding objective is nonnegative on effects and nonnegative weights. -/
theorem programObjective_nonneg {n d : ℕ} (V : CQChannel n d)
    {q : Fin n → ℝ} {T : Fin n → Matrix (Fin d) (Fin d) ℂ}
    (hq : ∀ x, 0 ≤ q x) (hT : ∀ x, IsEffect (T x)) :
    0 ≤ programObjective V.states q T := by
  exact Finset.sum_nonneg fun x _ =>
    mul_nonneg (hq x) (trace_mul_nonneg_re (V.isDensity x).posSemidef
      (hT x).one_sub_posSemidef)

/-- Increasing each decoding effect decreases average error. -/
theorem programObjective_antitone {n d : ℕ} (V : CQChannel n d)
    {q : Fin n → ℝ} {T Q : Fin n → Matrix (Fin d) (Fin d) ℂ}
    (hq : ∀ x, 0 ≤ q x) (hTQ : ∀ x, T x ≤ Q x) :
    programObjective V.states q Q ≤ programObjective V.states q T := by
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (hq x)
  apply trace_mul_mono_re (V.isDensity x).posSemidef
  exact sub_le_sub_left (hTQ x) 1

/-- The all-zero decoding family has error one. -/
theorem programObjective_zero {n d : ℕ} (V : CQChannel n d)
    {q : Fin n → ℝ} (hq : ∑ x, q x = 1) :
    programObjective V.states q (fun _ => 0) = 1 := by
  simpa [programObjective, (V.isDensity _).trace_one] using hq

/-- The all-identity decoding family has zero error. -/
@[simp] theorem programObjective_one {n d : ℕ} (V : CQChannel n d)
    (q : Fin n → ℝ) : programObjective V.states q (fun _ => 1) = 0 := by
  simp [programObjective]

/-- Average error is at most one for effects and probability weights. -/
theorem programObjective_le_one {n d : ℕ} (V : CQChannel n d)
    {q : Fin n → ℝ} {T : Fin n → Matrix (Fin d) (Fin d) ℂ}
    (hq : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1)
    (hT : ∀ x, IsEffect (T x)) : programObjective V.states q T ≤ 1 := by
  calc
    _ ≤ programObjective V.states q (fun _ => 0) :=
      programObjective_antitone V hq (fun x => (hT x).nonneg)
    _ = 1 := programObjective_zero V hq1

/-- A PSD inequality can be multiplied by a nonnegative real scalar. -/
theorem matrix_smul_mono {A B : Matrix (Fin d) (Fin d) ℂ} {t : ℝ}
    (ht : 0 ≤ t) (hAB : A ≤ B) : t • A ≤ t • B := by
  apply le_iff.mpr
  simpa only [← smul_sub] using (le_iff.mp hAB).smul ht

/-- Scalar multiples of the identity respect the scalar order. -/
theorem matrix_scalar_mono {a b : ℝ} (hab : a ≤ b) :
    a • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ b • 1 := by
  apply le_iff.mpr
  simpa only [← sub_smul] using
    (PosSemidef.one (n := Fin d) (R := ℂ)).smul (sub_nonneg.mpr hab)

namespace MCFEasable

theorem nonneg {L : ℝ} {q : Fin n → ℝ}
    {T : Fin n → Matrix (Fin d) (Fin d) ℂ} (h : MCFEasable L q T) :
    ∀ x, 0 ≤ q x := h.1

theorem sum_eq_one {L : ℝ} {q : Fin n → ℝ}
    {T : Fin n → Matrix (Fin d) (Fin d) ℂ} (h : MCFEasable L q T) :
    ∑ x, q x = 1 := h.2.1

theorem effects {L : ℝ} {q : Fin n → ℝ}
    {T : Fin n → Matrix (Fin d) (Fin d) ℂ} (h : MCFEasable L q T) :
    ∀ x, IsEffect (T x) := h.2.2.1

/-- Tightening the message parameter shrinks the MC feasible set. -/
theorem mono {L₁ L₂ : ℝ} {q : Fin n → ℝ}
    {T : Fin n → Matrix (Fin d) (Fin d) ℂ}
    (h : MCFEasable L₂ q T) (hL : 0 < L₁) (hLN : L₁ ≤ L₂) :
    MCFEasable L₁ q T := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans ?_⟩
  exact matrix_scalar_mono (one_div_le_one_div_of_le hL hLN)

end MCFEasable

namespace NSFeasible

theorem toMC {M : ℕ} {q : Fin n → ℝ}
    {T : Fin n → Matrix (Fin d) (Fin d) ℂ} (h : NSFeasible M q T) :
    MCFEasable M q T := ⟨h.1, h.2.1, h.2.2.1, le_of_eq h.2.2.2⟩

end NSFeasible

/-- There are no feasible probability weights on an empty input alphabet. -/
theorem not_MCFEasable_zero {d : ℕ} (L : ℝ) (q : Fin 0 → ℝ)
    (T : Fin 0 → Matrix (Fin d) (Fin d) ℂ) : ¬ MCFEasable L q T := by
  intro h
  simpa using h.2.1

@[simp] theorem epsMC_empty {d : ℕ} (V : CQChannel 0 d) (L : ℝ) : epsMC V L = 0 := by
  unfold epsMC
  have he : {e | ∃ (q : Fin 0 → ℝ) (T : Fin 0 → Matrix (Fin d) (Fin d) ℂ),
      MCFEasable L q T ∧ e = programObjective V.states q T} = ∅ := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
    intro q T h
    exact not_MCFEasable_zero L q T h.1
  rw [he, Real.sInf_empty]

@[simp] theorem epsNS_empty {d : ℕ} (V : CQChannel 0 d) (M : ℕ) : epsNS V M = 0 := by
  unfold epsNS
  have he : {e | ∃ (q : Fin 0 → ℝ) (T : Fin 0 → Matrix (Fin d) (Fin d) ℂ),
      NSFeasible M q T ∧ e = programObjective V.states q T} = ∅ := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
    intro q T h
    exact not_MCFEasable_zero M q T h.1.toMC
  rw [he, Real.sInf_empty]

/-- MC feasibility is nonempty for a nonempty input alphabet and positive parameter. -/
theorem mc_feasible_nonempty (hn : 0 < n) {L : ℝ} (hL : 0 ≤ L) :
    ∃ q T, @MCFEasable n d L q T := by
  let p := ProbDist.uniform n hn
  refine ⟨p.q, fun _ => 0, p.nonneg, p.sum_eq_one, fun _ => IsEffect.zero, ?_⟩
  simp only [smul_zero, Finset.sum_const_zero]
  exact ((PosSemidef.one (n := Fin d) (R := ℂ)).smul (by positivity :
    0 ≤ (1 / L : ℝ))).nonneg

/-- The constant effect I/M witnesses NS feasibility. -/
theorem ns_feasible_nonempty (hn : 0 < n) {M : ℕ} (hM : 1 ≤ M) :
    ∃ q T, @NSFeasible n d M q T := by
  let p := ProbDist.uniform n hn
  have ht0 : 0 ≤ (1 / M : ℝ) := by positivity
  have ht1 : (1 / M : ℝ) ≤ 1 := by
    apply (div_le_one (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM))).mpr
    exact_mod_cast hM
  refine ⟨p.q, fun _ => (1 / M : ℝ) • 1, p.nonneg, p.sum_eq_one,
    fun _ => ⟨((PosSemidef.one (n := Fin d) (R := ℂ)).smul ht0).nonneg, ?_⟩, ?_⟩
  · simpa only [one_smul] using (matrix_scalar_mono (d := d) ht1)
  · rw [← Finset.sum_smul, p.sum_eq_one, one_smul]

/-- Objective values are bounded below, including when the feasible set is empty. -/
theorem mc_values_bddBelow (V : CQChannel n d) (L : ℝ) :
    BddBelow {e | ∃ q T, MCFEasable L q T ∧ e = programObjective V.states q T} := by
  refine ⟨0, ?_⟩
  rintro e ⟨q, T, h, rfl⟩
  exact programObjective_nonneg V h.1 h.2.2.1

theorem ns_values_bddBelow (V : CQChannel n d) (M : ℕ) :
    BddBelow {e | ∃ q T, NSFeasible M q T ∧ e = programObjective V.states q T} := by
  refine ⟨0, ?_⟩
  rintro e ⟨q, T, h, rfl⟩
  exact programObjective_nonneg V h.1 h.2.2.1

theorem epsMC_le_objective (V : CQChannel n d) {L : ℝ} {q : Fin n → ℝ}
    {T : Fin n → Matrix (Fin d) (Fin d) ℂ} (h : MCFEasable L q T) :
    epsMC V L ≤ programObjective V.states q T :=
  csInf_le (mc_values_bddBelow V L) ⟨q, T, h, rfl⟩

theorem epsNS_le_objective (V : CQChannel n d) {M : ℕ} {q : Fin n → ℝ}
    {T : Fin n → Matrix (Fin d) (Fin d) ℂ} (h : NSFeasible M q T) :
    epsNS V M ≤ programObjective V.states q T :=
  csInf_le (ns_values_bddBelow V M) ⟨q, T, h, rfl⟩

theorem epsMC_nonneg (V : CQChannel n d) (L : ℝ) : 0 ≤ epsMC V L := by
  by_cases he : n = 0
  · subst n; simp
  by_cases hS : ({e | ∃ q T, MCFEasable L q T ∧
      e = programObjective V.states q T} : Set ℝ).Nonempty
  · exact le_csInf hS fun e ⟨q, T, h, he⟩ =>
      he ▸ programObjective_nonneg V h.1 h.2.2.1
  · rw [epsMC, Set.not_nonempty_iff_eq_empty.mp hS, Real.sInf_empty]

theorem epsNS_nonneg (V : CQChannel n d) (M : ℕ) : 0 ≤ epsNS V M := by
  by_cases hS : ({e | ∃ q T, NSFeasible M q T ∧
      e = programObjective V.states q T} : Set ℝ).Nonempty
  · exact le_csInf hS fun e ⟨q, T, h, he⟩ =>
      he ▸ programObjective_nonneg V h.1 h.2.2.1
  · rw [epsNS, Set.not_nonempty_iff_eq_empty.mp hS, Real.sInf_empty]

theorem epsMC_le_one (V : CQChannel n d) {L : ℝ} (hL : 0 ≤ L) : epsMC V L ≤ 1 := by
  by_cases he : n = 0
  · subst n; simp
  obtain ⟨q, T, h⟩ := mc_feasible_nonempty (d := d) (Nat.pos_of_ne_zero he) hL
  exact (epsMC_le_objective V h).trans (programObjective_le_one V h.1 h.2.1 h.2.2.1)

theorem epsNS_le_one (V : CQChannel n d) {M : ℕ} (hM : 1 ≤ M) : epsNS V M ≤ 1 := by
  by_cases he : n = 0
  · subst n; simp
  obtain ⟨q, T, h⟩ := ns_feasible_nonempty (d := d) (Nat.pos_of_ne_zero he) hM
  exact (epsNS_le_objective V h).trans (programObjective_le_one V h.1 h.2.1 h.2.2.1)

/-- A probability distribution with the identity family is feasible at one message. -/
theorem ns_feasible_one (hn : 0 < n) :
    ∃ q : Fin n → ℝ, NSFeasible (d := d) 1 q (fun _ => 1) := by
  let p := ProbDist.uniform n hn
  refine ⟨p.q, p.nonneg, p.sum_eq_one, fun _ => IsEffect.one, ?_⟩
  rw [← Finset.sum_smul, p.sum_eq_one]
  simp

@[simp] theorem epsNS_one (V : CQChannel n d) : epsNS V 1 = 0 := by
  apply le_antisymm _ (epsNS_nonneg V 1)
  by_cases he : n = 0
  · subst n; simp
  obtain ⟨q, hq⟩ := ns_feasible_one (d := d) (Nat.pos_of_ne_zero he)
  simpa using epsNS_le_objective V hq

@[simp] theorem epsMC_one (V : CQChannel n d) : epsMC V 1 = 0 := by
  apply le_antisymm _ (epsMC_nonneg V 1)
  by_cases he : n = 0
  · subst n; simp
  obtain ⟨q, hq⟩ := ns_feasible_one (d := d) (Nat.pos_of_ne_zero he)
  simpa using epsMC_le_objective V hq.toMC

end Paper22

end

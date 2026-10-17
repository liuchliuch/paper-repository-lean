import Paper22.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Continuous

/-!
# Reliability-function analytics: Petz Rényi divergence, Holevo capacity, sphere packing

Formalizes the divergences and capacity quantities of paper §3, together with
the key bounds (21)–(22) and convexity of the sphere-packing function.

Main definitions:
* `log2` — base-2 logarithm.
* `petzTrace` — Petz α-trace `Tr(ρ^α σ^{1-α})`.
* `petzRenyi` / `petzRenyiRe` — Petz Rényi divergence `D_α(ρ‖σ)`.
* `vonNeumannEntropy` — `S(ρ) = -Tr ρ log2 ρ` via eigenvalues.
* `holevoCapacity` — `C(W)`.
* `orderAlphaCapacity` — `C_α(W)`.
* `spherePacking` — `E_sp(R)`.

Key bounds for full-rank `W` with `lam = min_x lam_min(rho_x) > 0`:
* (21) `C_α(W) ≤ -α/(1-α) · log2 (d·lam)` for `0 < α < 1`.
* (22) `0 ≤ E_sp(r) ≤ -log2 (d·lam)` for `r > 0`.
* `E_sp` is convex, hence continuous on `(0, ∞)`.
-/

open scoped MatrixOrder ComplexOrder
open Matrix

noncomputable section

namespace Paper22

variable {n d m : ℕ}

/-! ## Base-2 logarithm -/

/-- Base-2 logarithm `log2 x = log x / log 2` (Mathlib convention: `log2 0 = 0`). -/
def log2 (x : ℝ) : ℝ := Real.logb 2 x

lemma log2_eq_div_log (x : ℝ) : log2 x = Real.log x / Real.log 2 := rfl

lemma log2_one : log2 1 = 0 := Real.logb_one

lemma log2_pos {x : ℝ} (hx : 1 < x) : 0 < log2 x :=
  Real.logb_pos (by norm_num : (1:ℝ) < 2) hx

lemma log2_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ log2 x :=
  Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hx

lemma log2_nonpos {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) : log2 x ≤ 0 :=
  Real.logb_nonpos (by norm_num : (1:ℝ) < 2) hx₀ hx₁

lemma log2_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    log2 (x * y) = log2 x + log2 y :=
  Real.logb_mul hx hy

lemma log2_rpow {x y : ℝ} (hx : 0 < x) : log2 (x ^ y) = y * log2 x :=
  Real.logb_rpow_eq_mul_logb_of_pos hx

lemma log2_le_log2 {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log2 x ≤ log2 y :=
  Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) hx hxy

lemma log2_lt_log2 {x y : ℝ} (hx : 0 < x) (hxy : x < y) : log2 x < log2 y :=
  Real.logb_lt_logb (by norm_num : (1:ℝ) < 2) hx hxy

lemma log2_monotoneOn : MonotoneOn log2 (Set.Ioi 0) :=
  fun _ hx _ _ hxy => log2_le_log2 hx hxy

/-! ## Petz α-trace and Petz Rényi divergence -/

section Petz

variable {m : ℕ}

/-- The Petz α-trace `Tr(ρ^α σ^{1-α})` as a real number
(the imaginary part vanishes for positive-semidefinite inputs). -/
def petzTrace (α : ℝ) (ρ σ : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  ((CFC.rpow ρ α * CFC.rpow σ (1 - α)).trace).re

/-- Real-valued Petz Rényi formula `(1/(α-1)) · log2 Tr(ρ^α σ^{1-α})`.
Correct whenever `0 < petzTrace α ρ σ`; see `petzRenyi` for the extended-real
version that is `+∞` when the Petz trace vanishes. -/
def petzRenyiRe (α : ℝ) (ρ σ : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  (1 / (α - 1)) * log2 (petzTrace α ρ σ)

/-- Petz Rényi divergence `D_α(ρ‖σ)` as an extended real: `+∞` when the Petz
trace vanishes (for `0 < α < 1`), and `0` outside `Set.Ioo 0 1`
(the `α = 1` term of the sphere-packing formula is *defined* to be `0` in any case). -/
def petzRenyi (α : ℝ) (ρ σ : Matrix (Fin m) (Fin m) ℂ) : EReal :=
  if 0 < α ∧ α < 1 then
    if 0 < petzTrace α ρ σ then (petzRenyiRe α ρ σ : EReal)
    else ⊤
  else 0

lemma petzRenyi_of_mem_Ioo {α : ℝ} (hα : α ∈ Set.Ioo 0 1)
    {ρ σ : Matrix (Fin m) (Fin m) ℂ} (ht : 0 < petzTrace α ρ σ) :
    petzRenyi α ρ σ = (petzRenyiRe α ρ σ : EReal) := by
  simp only [petzRenyi, hα.1, hα.2, true_and, if_pos, ht]

lemma petzRenyi_top_of_trace_le_zero {α : ℝ} (hα : α ∈ Set.Ioo 0 1)
    {ρ σ : Matrix (Fin m) (Fin m) ℂ} (ht : petzTrace α ρ σ ≤ 0) :
    petzRenyi α ρ σ = ⊤ := by
  have hα' : 0 < α ∧ α < 1 := ⟨hα.1, hα.2⟩
  simp only [petzRenyi, hα'.1, hα'.2, true_and, if_pos]
  have : ¬(0 < petzTrace α ρ σ) := by linarith
  simp [this]

lemma petzRenyi_of_not_mem_Ioo {α : ℝ} (hα : α ∉ Set.Ioo 0 1)
    {ρ σ : Matrix (Fin m) (Fin m) ℂ} :
    petzRenyi α ρ σ = 0 := by
  unfold petzRenyi
  by_cases h : 0 < α ∧ α < 1
  · exact absurd h hα
  · simp only [h, if_false]

lemma petzRenyi_eq_top_iff {α : ℝ} (hα : α ∈ Set.Ioo 0 1)
    {ρ σ : Matrix (Fin m) (Fin m) ℂ} :
    petzRenyi α ρ σ = ⊤ ↔ petzTrace α ρ σ ≤ 0 := by
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    rw [petzRenyi_of_mem_Ioo hα hlt] at h
    exact absurd h (EReal.coe_ne_top (petzRenyiRe α ρ σ))
  · exact petzRenyi_top_of_trace_le_zero hα

end Petz

/-! ## Spectral identities for matrix powers -/

section Spectral

variable {m : ℕ}

/-- Spectral form of the continuous functional calculus of a Hermitian matrix. -/
theorem cfc_eq_spectral {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A =
      (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) *
        diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) *
        (star (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)) :=
  hA.cfc_eq f

/-- The trace of `cfc f A` for Hermitian `A` is the sum of `f` applied to the eigenvalues. -/
theorem trace_cfc_eq_sum_eigenvalues {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, (f (hA.eigenvalues i) : ℂ) := by
  classical
  rw [hA.cfc_eq f, Matrix.IsHermitian.cfc]
  have hUU : (star (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)) *
      (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) = 1 :=
    unitary.star_mul_self_of_mem (hA.eigenvectorUnitary).2
  rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul, Matrix.trace_diagonal]
  simp only [Function.comp_apply]
  rfl

/-- For a positive-semidefinite matrix, `Tr(ρ^α) = ∑_i λ_i^α`. -/
theorem trace_rpow_eq_sum_eigenvalues {ρ : Matrix (Fin m) (Fin m) ℂ}
    (hρ : ρ.PosSemidef) (α : ℝ) :
    (CFC.rpow ρ α).trace = ∑ i, (((hρ.1.eigenvalues i : ℝ) ^ α : ℝ) : ℂ) := by
  classical
  have hnn : (0 : Matrix (Fin m) (Fin m) ℂ) ≤ ρ := hρ.nonneg
  have hre : CFC.rpow ρ α = cfc (fun x : ℝ => ((x.toNNReal : ℝ) ^ α)) ρ := by
    rw [CFC.rpow_eq_pow, CFC.rpow_def]
    exact cfc_nnreal_eq_real (fun x => x ^ (α : ℝ)) ρ hnn
  rw [hre, trace_cfc_eq_sum_eigenvalues hρ.1]
  push_cast
  congr 1
  funext i
  have hpos : 0 ≤ hρ.1.eigenvalues i := hρ.eigenvalues_nonneg i
  rw [Real.coe_toNNReal _ hpos]

/-- If every eigenvalue of a PSD matrix is at least `lam ≥ 0`, then
`Re Tr(ρ^α) ≥ m · lam^α` for `α > 0`. -/
theorem trace_rpow_re_ge {ρ : Matrix (Fin m) (Fin m) ℂ} (hρ : ρ.PosSemidef)
    {lam : ℝ} (hlam : ∀ i, lam ≤ hρ.1.eigenvalues i) (hlam0 : 0 ≤ lam) {α : ℝ} (hα : 0 < α) :
    (m : ℝ) * lam ^ α ≤ ((CFC.rpow ρ α).trace).re := by
  classical
  rw [trace_rpow_eq_sum_eigenvalues hρ α]
  have hre : ((∑ i, (((hρ.1.eigenvalues i : ℝ) ^ α : ℝ) : ℂ)).re)
      = ∑ i, (hρ.1.eigenvalues i : ℝ) ^ α := by
    exact_mod_cast rfl
  rw [hre]
  have : ∀ i : Fin m, lam ^ α ≤ (hρ.1.eigenvalues i : ℝ) ^ α := by
    intro i
    exact Real.rpow_le_rpow hlam0 (hlam i) hα.le
  calc (m : ℝ) * lam ^ α
      = ∑ _i : Fin m, lam ^ α := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    _ ≤ ∑ i : Fin m, (hρ.1.eigenvalues i : ℝ) ^ α := Finset.sum_le_sum fun i _ => this i

theorem isHermitian_smul_one (c : ℝ) :
    (c • (1 : Matrix (Fin m) (Fin m) ℂ)).IsHermitian := by
  show (c • 1)ᴴ = c • 1
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp [star_trivial]

theorem isHermitian_smul_real {c : ℝ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) :
    (c • A).IsHermitian := by
  show (c • A)ᴴ = c • A
  rw [Matrix.conjTranspose_smul, hA.eq]
  simp [star_trivial]

theorem spectrum_smul_one [NeZero m] (c : ℝ) :
    spectrum ℝ (c • (1 : Matrix (Fin m) (Fin m) ℂ)) = {c} := by
  have h1 : (c • (1 : Matrix (Fin m) (Fin m) ℂ))
      = algebraMap ℝ (Matrix (Fin m) (Fin m) ℂ) c :=
    (Algebra.algebraMap_eq_smul_one c).symm
  rw [h1]
  exact CFC.spectrum_algebraMap_eq c

theorem cfc_const_smul_one [NeZero m] (c : ℝ) (f : ℝ → ℝ) :
    cfc f (c • (1 : Matrix (Fin m) (Fin m) ℂ)) = f c • 1 := by
  have hAherm : (c • (1 : Matrix (Fin m) (Fin m) ℂ)).IsHermitian :=
    isHermitian_smul_one c
  have hsa : IsSelfAdjoint (c • (1 : Matrix (Fin m) (Fin m) ℂ)) :=
    hAherm.isSelfAdjoint
  have hspec : spectrum ℝ (c • (1 : Matrix (Fin m) (Fin m) ℂ)) = {c} :=
    spectrum_smul_one c
  have hEqOn : (spectrum ℝ (c • (1 : Matrix (Fin m) (Fin m) ℂ))).EqOn f (fun _ => f c) := by
    intro x hx
    rw [hspec] at hx
    simp at hx
    rw [hx]
  rw [cfc_congr hEqOn]
  rw [cfc_const (R := ℝ) (a := c • (1 : Matrix (Fin m) (Fin m) ℂ)) (ha := hsa)]
  rw [Algebra.algebraMap_eq_smul_one]

/-- `CFC.rpow` of a nonnegative scalar multiple of the identity. -/
theorem cfc_rpow_smul_one [NeZero m] {c : ℝ} (hc : 0 ≤ c) (α : ℝ) :
    CFC.rpow (c • (1 : Matrix (Fin m) (Fin m) ℂ)) α
      = (c ^ α) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
  have hnn : (0 : Matrix (Fin m) (Fin m) ℂ) ≤ c • 1 :=
    nonneg_iff_posSemidef.mpr (Matrix.PosSemidef.one.smul hc)
  have hre : CFC.rpow (c • (1 : Matrix (Fin m) (Fin m) ℂ)) α
      = cfc (fun x : ℝ => ((x.toNNReal : ℝ) ^ α)) (c • (1 : Matrix (Fin m) (Fin m) ℂ)) := by
    rw [CFC.rpow_eq_pow, CFC.rpow_def]
    exact cfc_nnreal_eq_real (fun x => x ^ (α : ℝ)) _ hnn
  rw [hre, cfc_const_smul_one]
  show ((c.toNNReal : ℝ) ^ α) • 1 = c ^ α • 1
  rw [Real.coe_toNNReal c hc]

/-- The Petz α-trace at the maximally mixed state `I/d`:
`Tr(ρ^α (I/d)^{1-α}) = d^{α-1} · Re Tr(ρ^α)`. -/
theorem petzTrace_smul_inv_one [NeZero d] {ρ : Matrix (Fin d) (Fin d) ℂ} (_hρ : ρ.PosSemidef)
    (hd : 0 < d) (α : ℝ) :
    petzTrace α ρ ((1 / (d : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ))
      = (d : ℝ) ^ (α - 1) * ((CFC.rpow ρ α).trace).re := by
  classical
  have hc : 0 ≤ (1 / (d : ℝ)) := by positivity
  have hre : CFC.rpow ((1 / (d : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) (1 - α)
      = ((1 / (d : ℝ)) ^ (1 - α)) • (1 : Matrix (Fin d) (Fin d) ℂ) :=
    cfc_rpow_smul_one hc (1 - α)
  have hsmul : ((1 / (d : ℝ)) ^ (1 - α) : ℝ) = (d : ℝ) ^ (α - 1) := by
    have hd0 : 0 < (d : ℝ) := by exact_mod_cast hd
    have h1 : (1 / (d : ℝ)) = (d : ℝ)⁻¹ := one_div _
    rw [h1, Real.inv_rpow hd0.le, ← Real.rpow_neg hd0.le]
    congr 1
    ring
  unfold petzTrace
  rw [hre, hsmul]
  have hmul : CFC.rpow ρ α * (((d : ℝ) ^ (α - 1)) • (1 : Matrix (Fin d) (Fin d) ℂ))
      = ((d : ℝ) ^ (α - 1)) • (CFC.rpow ρ α) := by
    rw [Matrix.mul_smul, Matrix.mul_one]
  rw [hmul, Matrix.trace_smul]
  exact RCLike.re_ofReal_mul (K := ℂ) _ _

/-- **Key Petz-trace lower bound (core of (21)).**
For PSD `ρ` with `λ_min(ρ) ≥ lam > 0` and output dimension `d > 0`,
`Tr(ρ^α (I/d)^{1-α}) ≥ (d·lam)^α` for `0 < α`. -/
theorem petzTrace_uniform_lower_bound [NeZero d] {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosSemidef) (hd : 0 < d)
    {lam : ℝ} (hlam : ∀ i, lam ≤ hρ.1.eigenvalues i) (hlam0 : 0 < lam)
    {α : ℝ} (hα : 0 < α) :
    ((d : ℝ) * lam) ^ α ≤
      petzTrace α ρ ((1 / (d : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  classical
  have hpt : petzTrace α ρ ((1 / (d : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ))
      = (d : ℝ) ^ (α - 1) * ((CFC.rpow ρ α).trace).re :=
    petzTrace_smul_inv_one hρ hd α
  have htr : (d : ℝ) * lam ^ α ≤ ((CFC.rpow ρ α).trace).re :=
    trace_rpow_re_ge hρ hlam hlam0.le hα
  have hdpos : 0 < (d : ℝ) ^ (α - 1) := by positivity
  rw [hpt]
  have hcalc : (d : ℝ) ^ (α - 1) * ((d : ℝ) * lam ^ α) = ((d : ℝ) * lam) ^ α := by
    have hd0 : 0 < (d : ℝ) := by exact_mod_cast hd
    have h1 : (d : ℝ) ^ (α - 1) * (d : ℝ) = (d : ℝ) ^ α := by
      have h2 : (d : ℝ) ^ (α - 1) * (d : ℝ) ^ (1 : ℝ) = (d : ℝ) ^ ((α - 1) + 1) :=
        (Real.rpow_add hd0 (α - 1) 1).symm
      simpa [Real.rpow_one] using h2
    calc (d : ℝ) ^ (α - 1) * ((d : ℝ) * lam ^ α)
        = ((d : ℝ) ^ (α - 1) * (d : ℝ)) * lam ^ α := by ring
      _ = (d : ℝ) ^ α * lam ^ α := by rw [h1]
      _ = ((d : ℝ) * lam) ^ α := (Real.mul_rpow hd0.le hlam0.le).symm
  rw [← hcalc]
  exact mul_le_mul_of_nonneg_left htr hdpos.le

end Spectral

/-! ## Von Neumann entropy -/

section Entropy

variable {m : ℕ}

/-- Von Neumann entropy `S(ρ) = -Tr ρ log2 ρ = -∑_i λ_i log2 λ_i`,
with the convention `0 · log 0 = 0` (automatic for Mathlib's `Real.log`). -/
def vonNeumannEntropy {ρ : Matrix (Fin m) (Fin m) ℂ} (hρ : ρ.IsHermitian) : ℝ :=
  -∑ i, (hρ.eigenvalues i) * log2 (hρ.eigenvalues i)

lemma mul_log2_nonpos_of_mem_Icc {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    x * log2 x ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos hx₀ (log2_nonpos hx₀ hx₁)

lemma IsDensity.eigenvalues_mem_Icc {ρ : Matrix (Fin m) (Fin m) ℂ} (h : IsDensity ρ)
    (i : Fin m) : h.isHermitian.eigenvalues i ∈ Set.Icc 0 1 := by
  classical
  have hs : ∑ j, h.isHermitian.eigenvalues j = 1 := by
    have ht := h.isHermitian.trace_eq_sum_eigenvalues
    rw [h.trace_one] at ht
    have hr := congrArg Complex.re ht
    simpa using hr.symm
  refine ⟨h.posSemidef.eigenvalues_nonneg i, ?_⟩
  calc h.isHermitian.eigenvalues i
      ≤ ∑ j, h.isHermitian.eigenvalues j :=
        Finset.single_le_sum (fun j _ => h.posSemidef.eigenvalues_nonneg j) (Finset.mem_univ i)
    _ = 1 := hs

/-- Von Neumann entropy of a density operator is nonnegative. -/
lemma vonNeumannEntropy_nonneg {ρ : Matrix (Fin m) (Fin m) ℂ} (h : IsDensity ρ) :
    0 ≤ vonNeumannEntropy h.isHermitian := by
  classical
  unfold vonNeumannEntropy
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro i _
  exact mul_log2_nonpos_of_mem_Icc (h.eigenvalues_mem_Icc i).1 (h.eigenvalues_mem_Icc i).2

lemma vonNeumannEntropy_eq_negMulLog {ρ : Matrix (Fin m) (Fin m) ℂ} (hρ : ρ.IsHermitian) :
    vonNeumannEntropy hρ =
      (1 / Real.log 2) * ∑ i, Real.negMulLog (hρ.eigenvalues i) := by
  classical
  simp only [vonNeumannEntropy, log2_eq_div_log, Real.negMulLog_def,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Entropy

/-! ## Positivity and finite-valued formulas -/

/-- Trace of a product of two positive matrices is nonnegative. -/
lemma divergence_trace_mul_nonneg {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ (A * B).trace.re := by
  let S := CFC.sqrt B
  have hS : S.IsHermitian := (CFC.sqrt_nonneg B).posSemidef.isHermitian
  have hp := (hA.posSemidef.mul_mul_conjTranspose_same S).trace_nonneg
  have ht : (S * A * Sᴴ).trace = (A * B).trace := by
    rw [hS.eq, Matrix.trace_mul_cycle]
    simp only [← Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self B hB, S]
    exact Matrix.trace_mul_comm B A
  rw [ht] at hp
  exact (RCLike.nonneg_iff.mp hp).1

/-- Multiplication by a positive matrix preserves the trace order. -/
lemma divergence_trace_mul_mono {A B C : Matrix (Fin d) (Fin d) ℂ}
    (hAB : A ≤ B) (hC : 0 ≤ C) : (A * C).trace.re ≤ (B * C).trace.re := by
  have h := divergence_trace_mul_nonneg (sub_nonneg.mpr hAB) hC
  simpa only [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, sub_nonneg] using h

lemma density_rpow_le_one {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : IsDensity ρ)
    {α : ℝ} (hα : 0 ≤ α) : CFC.rpow ρ α ≤ 1 := by
  rw [CFC.rpow, cfc_nnreal_eq_real (fun x => x ^ α) ρ hρ.nonneg]
  apply cfc_le_one
  intro x hx
  rw [hρ.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  rw [NNReal.coe_rpow, Real.coe_toNNReal _ (hρ.eigenvalues_mem_Icc i).1]
  exact Real.rpow_le_one (hρ.eigenvalues_mem_Icc i).1 (hρ.eigenvalues_mem_Icc i).2 hα

/-- A coarse trace bound suffices for conditional completeness of the real infimum.
The sharp trace bound one (Petz nonnegativity) is not needed here. -/
lemma petzTrace_le_dim {ρ σ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    petzTrace α ρ σ ≤ (d : ℝ) := by
  have h₁ := divergence_trace_mul_mono (density_rpow_le_one hρ hα.1.le)
    (CFC.rpow_nonneg (a := σ) (y := 1 - α))
  have h₂ := divergence_trace_mul_mono (density_rpow_le_one hσ (by linarith [hα.2] : 0 ≤ 1 - α))
    (zero_le_one_matrix d)
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.trace_one, Fintype.card_fin,
    Complex.natCast_re] at h₁ h₂
  exact h₁.trans h₂

lemma petzTrace_nonneg {ρ σ : Matrix (Fin d) (Fin d) ℂ} (α : ℝ) :
    0 ≤ petzTrace α ρ σ :=
  divergence_trace_mul_nonneg CFC.rpow_nonneg CFC.rpow_nonneg

/-- Every finite family of strictly positive reals has a positive common lower bound. -/
lemma divergence_exists_uniform_pos {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ c > 0, ∀ i, c ≤ f i := by
  classical
  by_cases h : Nonempty ι
  · letI := h
    let s : Finset ℝ := Finset.univ.image f
    have hs : s.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
    refine ⟨s.min' hs, ?_, ?_⟩
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem s hs)
      rw [← hi]
      exact hf i
    · intro i
      exact Finset.min'_le s (f i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  · exact ⟨1, by norm_num, fun i => (h ⟨i⟩).elim⟩

lemma CQChannel.exists_uniform_spectral_lower_bound (V : CQChannel n d) (hV : V.FullRank) :
    ∃ lam > 0, ∀ x i, lam ≤ (V.density x).isHermitian.eigenvalues i := by
  obtain ⟨lam, hpos, hle⟩ := divergence_exists_uniform_pos
    (fun p : Fin n × Fin d => (V.density p.1).isHermitian.eigenvalues p.2)
    (fun p => (hV p.1).eigenvalues_pos p.2)
  exact ⟨lam, hpos, fun x i => hle (x, i)⟩

lemma density_trace_rpow_pos {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensity σ)
    {β : ℝ} (hβ : 0 < β) : 0 < (CFC.rpow σ β).trace.re := by
  classical
  have hs : ∑ i, hσ.isHermitian.eigenvalues i = 1 := by
    have ht := hσ.isHermitian.trace_eq_sum_eigenvalues
    rw [hσ.trace_one] at ht
    have hr := congrArg Complex.re ht
    simpa using hr.symm
  have hex : ∃ i, 0 < hσ.isHermitian.eigenvalues i := by
    by_contra hn
    push_neg at hn
    have hz : ∑ i, hσ.isHermitian.eigenvalues i ≤ 0 :=
      Finset.sum_nonpos fun i _ => hn i
    linarith
  obtain ⟨i, hi⟩ := hex
  rw [trace_rpow_eq_sum_eigenvalues hσ.posSemidef]
  simp only [Complex.re_sum, Complex.ofReal_re]
  exact (Finset.single_le_sum (fun j _ => Real.rpow_nonneg
    (hσ.posSemidef.eigenvalues_nonneg j) β) (Finset.mem_univ i)).trans_lt'
      (Real.rpow_pos_of_pos hi β)

/-- Positive definiteness of the first argument makes every density reference admissible. -/
lemma petzTrace_pos_of_posDef {ρ σ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosDef) (hσ : IsDensity σ) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    0 < petzTrace α ρ σ := by
  obtain ⟨lam, hlam0, hlam⟩ := divergence_exists_uniform_pos
    hρ.isHermitian.eigenvalues hρ.eigenvalues_pos
  have hpow : lam ^ α • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ CFC.rpow ρ α := by
    rw [CFC.rpow, cfc_nnreal_eq_real (fun x => x ^ α) ρ hρ.posSemidef.nonneg]
    rw [← Algebra.algebraMap_eq_smul_one]
    apply algebraMap_le_cfc
    · intro x hx
      rw [hρ.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      rw [NNReal.coe_rpow, Real.coe_toNNReal _ (hρ.posSemidef.eigenvalues_nonneg i)]
      exact Real.rpow_le_rpow hlam0.le (hlam i) hα.1.le
    · exact (Matrix.finite_real_spectrum (A := ρ)).continuousOn _
    · exact hρ.isHermitian.isSelfAdjoint
  have hle := divergence_trace_mul_mono hpow
    (CFC.rpow_nonneg (a := σ) (y := 1 - α))
  have ht : (lam ^ α • (1 : Matrix (Fin d) (Fin d) ℂ) * CFC.rpow σ (1 - α)).trace.re
      = lam ^ α * (CFC.rpow σ (1 - α)).trace.re := by
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul]
    exact RCLike.re_ofReal_mul (K := ℂ) _ _
  change (lam ^ α • (1 : Matrix (Fin d) (Fin d) ℂ) * CFC.rpow σ (1 - α)).trace.re
    ≤ (CFC.rpow ρ α * CFC.rpow σ (1 - α)).trace.re at hle
  rw [ht] at hle
  exact (mul_pos (Real.rpow_pos_of_pos hlam0 α)
    (density_trace_rpow_pos hσ (by linarith [hα.2]))).trans_le hle

lemma petzRenyi_eq_coe_of_fullRank {ρ σ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosDef) (hσ : IsDensity σ) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    petzRenyi α ρ σ = (petzRenyiRe α ρ σ : EReal) :=
  petzRenyi_of_mem_Ioo hα (petzTrace_pos_of_posDef hρ hσ hα)

/-! ## Holevo capacity -/

section Holevo

variable {n d : ℕ}

/-- The mixture `∑_x q_x ρ_x` of channel outputs under input law `q`. -/
def mixture (V : CQChannel n d) (q : Fin n → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ x, q x • V.states x

lemma mixture_isHermitian (V : CQChannel n d) (q : Fin n → ℝ) (_hq : ∀ i, 0 ≤ q i) :
    (mixture V q).IsHermitian := by
  classical
  unfold mixture
  show (∑ x, q x • V.states x)ᴴ = ∑ x, q x • V.states x
  rw [Matrix.conjTranspose_sum]
  congr 1
  funext x
  rw [Matrix.conjTranspose_smul, star_trivial]
  rw [(V.isDensity x).isHermitian.eq]

lemma mixture_posSemidef (V : CQChannel n d) (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i) :
    (mixture V q).PosSemidef := by
  unfold mixture
  exact (Finset.sum_nonneg fun x _ => smul_nonneg (hq x) (V.nonneg x)).posSemidef

lemma mixture_trace (V : CQChannel n d) (q : Fin n → ℝ) (_hq : ∀ i, 0 ≤ q i)
    (hq1 : ∑ i, q i = 1) : (mixture V q).trace = 1 := by
  classical
  unfold mixture
  rw [Matrix.trace_sum]
  have hterm : ∀ x, (q x • V.states x).trace = q x := by
    intro x
    have h1 : (V.states x).trace = (1 : ℂ) := by
      simpa using V.trace_one x
    rw [Matrix.trace_smul, h1, Algebra.smul_def, mul_one]
    rfl
  simp_rw [hterm]
  push_cast
  exact_mod_cast hq1

lemma mixture_isDensity (V : CQChannel n d) (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hq1 : ∑ i, q i = 1) : IsDensity (mixture V q) :=
  ⟨mixture_posSemidef V q hq, mixture_trace V q hq hq1⟩

/-- The Holevo objective `S(∑ p_x ρ_x) - ∑ p_x S(ρ_x)` at input law `q`. -/
def holevoObjective (V : CQChannel n d) (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i) : ℝ :=
  vonNeumannEntropy (mixture_isHermitian V q hq) -
    ∑ x, q x * vonNeumannEntropy (V.density x |>.isHermitian)

/-- **Holevo capacity** `C(W) = max_p [S(∑ p_x ρ_x) - ∑ p_x S(ρ_x)]`. -/
def holevoCapacity (V : CQChannel n d) : ℝ :=
  sSup {s | ∃ q : Fin n → ℝ, ∃ (hq : ∀ i, 0 ≤ q i), ∑ i, q i = 1 ∧
    s = holevoObjective V q hq}

lemma holevoCapacity_zero_input (V : CQChannel 0 d) : holevoCapacity V = 0 := by
  unfold holevoCapacity
  simp

end Holevo

/-! ## Order-α capacity -/

section OrderAlpha

variable {n d : ℕ}

/-- The order-α objective `∑_x p_x D_α(ρ_x ‖ σ)` at input law `q` and reference state `σ`,
using the real-valued Petz formula. -/
def orderAlphaObj (α : ℝ) (V : CQChannel n d) (q : Fin n → ℝ)
    (σ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ x, q x * petzRenyiRe α (V.states x) σ

/-- The inner infimum of the order-α objective over density operators `σ`. -/
def orderAlphaInf (α : ℝ) (V : CQChannel n d) (q : Fin n → ℝ) : ℝ :=
  sInf {s | ∃ σ : Matrix (Fin d) (Fin d) ℂ, IsDensity σ ∧ s = orderAlphaObj α V q σ}

/-- **Order-α capacity** `C_α(W) = max_p inf_σ ∑_{x: p_x>0} p_x D_α(ρ_x‖σ)`. -/
def orderAlphaCapacity (V : CQChannel n d) (α : ℝ) : ℝ :=
  sSup {t | ∃ q : Fin n → ℝ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧
    t = orderAlphaInf α V q}

/-- The maximally mixed state `I/d` as a matrix. -/
def maximallyMixed (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  (((1 : ℝ) / (d : ℝ)) : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ)

lemma maximallyMixed_isDensity {d : ℕ} (hd : 0 < d) :
    IsDensity (maximallyMixed d) := by
  classical
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  refine ⟨?_, ?_⟩
  · unfold maximallyMixed
    have hc : (0 : ℝ) ≤ (1 : ℝ) / (d : ℝ) := by positivity
    have hone : (0 : Matrix (Fin d) (Fin d) ℂ) ≤ 1 := zero_le_one_matrix _
    exact nonneg_iff_posSemidef.mp (smul_nonneg hc hone)
  · unfold maximallyMixed
    have hcard : Fintype.card (Fin d) = d := Fintype.card_fin d
    have htr : ((1 : Matrix (Fin d) (Fin d) ℂ)).trace = (d : ℂ) := by
      rw [Matrix.trace_one, hcard]
    rw [Matrix.trace_smul, htr]
    -- goal: ((1:ℝ)/(d:ℝ)) • (d:ℂ) = 1
    rw [Algebra.smul_def]
    have hcast : (algebraMap ℝ ℂ) ((1 : ℝ) / (d : ℝ)) = (1 : ℂ) / (d : ℂ) := by
      rw [map_div₀, map_one, map_natCast]
    rw [hcast]
    field_simp [hd0]

end OrderAlpha

/-! ## Sphere-packing function -/

section SpherePacking

variable {n d : ℕ}

/-- The single-α term `(1-α)/α · (C_α(W) - R)` of the sphere-packing supremum,
with the `α = 1` term *defined* to be `0`. -/
def spherePackingTerm (V : CQChannel n d) (α : ℝ) (R : ℝ) : ℝ :=
  if α = 1 then 0
  else if 0 < α ∧ α < 1 then (1 - α) / α * (orderAlphaCapacity V α - R)
  else 0

/-- **Sphere-packing function** `E_sp(R) = sup_{0<α≤1} (1-α)/α · (C_α(W) - R)`,
where the `α = 1` term is defined to be `0`. -/
def spherePacking (V : CQChannel n d) (R : ℝ) : ℝ :=
  sSup ((fun α => spherePackingTerm V α R) '' Set.Ioc 0 1)

lemma spherePackingTerm_one (V : CQChannel n d) (R : ℝ) :
    spherePackingTerm V 1 R = 0 := by
  simp [spherePackingTerm]

lemma spherePackingTerm_of_Ioo (V : CQChannel n d) {α : ℝ}
    (hα : α ∈ Set.Ioo 0 1) (R : ℝ) :
    spherePackingTerm V α R = (1 - α) / α * (orderAlphaCapacity V α - R) := by
  have hne : ¬(α = 1) := by
    intro heq
    rw [heq] at hα
    exact absurd hα.2 (by norm_num)
  unfold spherePackingTerm
  rw [if_neg hne, if_pos ⟨hα.1, hα.2⟩]

/-- Each sphere-packing term is an affine function of the rate `R`. -/
lemma spherePackingTerm_eq_affine (V : CQChannel n d) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) (R : ℝ) :
    spherePackingTerm V α R =
      (1 - α) / α * orderAlphaCapacity V α - (1 - α) / α * R := by
  rw [spherePackingTerm_of_Ioo V hα R]
  ring

lemma spherePackingTerm_one_mem (V : CQChannel n d) (R : ℝ) :
    (0 : ℝ) ∈ (fun α => spherePackingTerm V α R) '' Set.Ioc 0 1 := by
  refine ⟨1, ⟨by norm_num, le_refl 1⟩, ?_⟩
  show (fun α => spherePackingTerm V α R) 1 = 0
  exact spherePackingTerm_one V R

end SpherePacking

/-! ## Key bounds (21)–(22) -/

section KeyBounds

variable {n d : ℕ}

/-- **Bound (21), core inequality.**
For `0 < α < 1`, PSD `ρ` with eigenvalues ≥ `lam > 0`, output dimension `d > 0`,
the real-valued Petz divergence at the maximally mixed state satisfies
`D_α(ρ ‖ I/d) ≤ -α/(1-α) · log2 (d·lam)`. -/
theorem petzRenyiRe_uniform_upper_bound [NeZero d] {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosSemidef) (hd : 0 < d)
    {lam : ℝ} (hlam : ∀ i, lam ≤ hρ.1.eigenvalues i) (hlam0 : 0 < lam)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    petzRenyiRe α ρ ((1 / (d : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ))
      ≤ -α / (1 - α) * log2 ((d : ℝ) * lam) := by
  classical
  -- petzTrace ≥ (d·lam)^α
  have hpt := petzTrace_uniform_lower_bound hρ hd hlam hlam0 hα0
  set t := petzTrace α ρ ((1 / (d : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) with htdef
  have ht0 : 0 < t := by
    have : (0 : ℝ) < ((d : ℝ) * lam) ^ α := by positivity
    linarith
  -- log2 t ≥ α · log2 (d·lam)
  have hlog : log2 t ≥ log2 (((d : ℝ) * lam) ^ α) := log2_le_log2 (by positivity) hpt
  have hlog2 : log2 (((d : ℝ) * lam) ^ α) = α * log2 ((d : ℝ) * lam) := by
    have hdpos : 0 < (d : ℝ) * lam := by positivity
    exact log2_rpow hdpos
  have hlog' : log2 t ≥ α * log2 ((d : ℝ) * lam) := by linarith
  -- petzRenyiRe = 1/(α-1) * log2 t, and 1/(α-1) < 0
  have hden : α - 1 < 0 := by linarith
  have hdiv : 1 / (α - 1) < 0 := by
    rw [one_div]
    exact (inv_lt_zero).2 hden
  -- flip inequality
  have hmul : (1 / (α - 1)) * log2 t ≤ (1 / (α - 1)) * (α * log2 ((d : ℝ) * lam)) :=
    mul_le_mul_of_nonpos_left hlog' hdiv.le
  -- simplify RHS: (1/(α-1)) * α * log2 (dλ) = -α/(1-α) * log2 (dλ)
  have hsimp : (1 / (α - 1)) * (α * log2 ((d : ℝ) * lam))
      = -α / (1 - α) * log2 ((d : ℝ) * lam) := by
    have h1 : α - 1 = -(1 - α) := by ring
    rw [h1]
    field_simp [sub_ne_zero.mpr (by linarith : α ≠ 1)]
  rw [hsimp] at hmul
  unfold petzRenyiRe
  rw [← htdef]
  exact hmul

/-- A uniform finite lower bound for the real formula on density operators.
This coarse bound also covers the convention `Real.log 0 = 0`; agreement with
Petz divergence is asserted separately under full rank. -/
lemma petzRenyiRe_lower_bound [NeZero d] {ρ σ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    (1 / (α - 1)) * log2 (d : ℝ) ≤ petzRenyiRe α ρ σ := by
  have hlog : log2 (petzTrace α ρ σ) ≤ log2 (d : ℝ) := by
    by_cases ht : 0 < petzTrace α ρ σ
    · exact log2_le_log2 ht (petzTrace_le_dim hρ hσ hα)
    · have hz : petzTrace α ρ σ = 0 := le_antisymm (le_of_not_gt ht) (petzTrace_nonneg α)
      rw [hz]
      simp only [log2, Real.logb_zero]
      apply log2_nonneg
      exact_mod_cast (NeZero.one_le (n := d))
  exact mul_le_mul_of_nonpos_left hlog (one_div_nonpos.mpr (sub_nonpos.mpr hα.2.le))

lemma orderAlpha_values_bddBelow [NeZero d] (V : CQChannel n d)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) {q : Fin n → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1) :
    BddBelow {s | ∃ σ, IsDensity σ ∧ s = orderAlphaObj α V q σ} := by
  refine ⟨(1 / (α - 1)) * log2 (d : ℝ), ?_⟩
  intro s hs
  obtain ⟨σ, hσ, rfl⟩ := hs
  unfold orderAlphaObj
  calc (1 / (α - 1)) * log2 (d : ℝ)
      = ∑ x, q x * ((1 / (α - 1)) * log2 (d : ℝ)) := by
        rw [← Finset.sum_mul, hq1, one_mul]
    _ ≤ ∑ x, q x * petzRenyiRe α (V.states x) σ :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
        (petzRenyiRe_lower_bound (V.isDensity x) hσ hα) (hq0 x)

lemma orderAlpha_values_nonempty [NeZero d] (V : CQChannel n d) (α : ℝ) (q : Fin n → ℝ) :
    Set.Nonempty {s | ∃ σ, IsDensity σ ∧ s = orderAlphaObj α V q σ} :=
  ⟨_, maximallyMixed d, maximallyMixed_isDensity (NeZero.pos d), rfl⟩

/-- **Bound (21)** from the actual matrix Petz trace. -/
theorem orderAlphaCapacity_le [NeZero n] [NeZero d] (V : CQChannel n d)
    (hd : 0 < d) (_hV : V.FullRank)
    {lam : ℝ} (hlam : ∀ x i, lam ≤ (V.density x).isHermitian.eigenvalues i) (hlam0 : 0 < lam)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    orderAlphaCapacity V α ≤ -α / (1 - α) * log2 ((d : ℝ) * lam) := by
  classical
  let K := -α / (1 - α) * log2 ((d : ℝ) * lam)
  have hobj : ∀ q : Fin n → ℝ, (∀ i, 0 ≤ q i) → (∑ i, q i = 1) →
      orderAlphaInf α V q ≤ K := by
    intro q hq0 hq1
    have hinf : orderAlphaInf α V q ≤ orderAlphaObj α V q (maximallyMixed d) :=
      csInf_le (orderAlpha_values_bddBelow V ⟨hα0, hα1⟩ hq0 hq1)
        ⟨maximallyMixed d, maximallyMixed_isDensity hd, rfl⟩
    apply hinf.trans
    unfold orderAlphaObj
    calc ∑ x, q x * petzRenyiRe α (V.states x) (maximallyMixed d)
        ≤ ∑ x, q x * K := Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left
            (petzRenyiRe_uniform_upper_bound (V.isDensity x).posSemidef hd
              (hlam x) hlam0 hα0 hα1) (hq0 x)
      _ = K := by rw [← Finset.sum_mul, hq1, one_mul]
  apply csSup_le
  · let q := ProbDist.uniform n (NeZero.pos n)
    exact ⟨_, q.q, q.nonneg, q.sum_eq_one, rfl⟩
  · rintro z ⟨q, hq0, hq1, rfl⟩
    exact hobj q hq0 hq1

lemma dimension_mul_spectral_lower_le_one [NeZero n] (V : CQChannel n d)
    {lam : ℝ} (hlam : ∀ x i, lam ≤ (V.density x).isHermitian.eigenvalues i) :
    (d : ℝ) * lam ≤ 1 := by
  classical
  let x : Fin n := ⟨0, NeZero.pos n⟩
  have hs : ∑ i, (V.density x).isHermitian.eigenvalues i = 1 := by
    have ht := (V.density x).isHermitian.trace_eq_sum_eigenvalues
    rw [(V.density x).trace_one] at ht
    have hr := congrArg Complex.re ht
    simpa using hr.symm
  calc (d : ℝ) * lam = ∑ _i : Fin d, lam := by simp
    _ ≤ ∑ i, (V.density x).isHermitian.eigenvalues i :=
      Finset.sum_le_sum fun i _ => hlam x i
    _ = 1 := hs

lemma spherePackingTerm_le_bound [NeZero n] [NeZero d] (V : CQChannel n d)
    (hV : V.FullRank) {lam : ℝ}
    (hlam : ∀ x i, lam ≤ (V.density x).isHermitian.eigenvalues i) (hlam0 : 0 < lam)
    {R : ℝ} (hR : 0 ≤ R) {α : ℝ} (hα : α ∈ Set.Ioc 0 1) :
    spherePackingTerm V α R ≤ -log2 ((d : ℝ) * lam) := by
  have hK : 0 ≤ -log2 ((d : ℝ) * lam) := neg_nonneg.mpr
    (log2_nonpos (by positivity) (dimension_mul_spectral_lower_le_one V hlam))
  by_cases h1 : α = 1
  · subst α
    rw [spherePackingTerm_one]
    exact hK
  have hα1 : α < 1 := lt_of_le_of_ne hα.2 h1
  rw [spherePackingTerm_of_Ioo V ⟨hα.1, hα1⟩]
  have hc := orderAlphaCapacity_le V (NeZero.pos d) hV hlam hlam0 hα.1 hα1
  have hs : 0 ≤ (1 - α) / α := div_nonneg (by linarith) hα.1.le
  calc (1 - α) / α * (orderAlphaCapacity V α - R)
      ≤ (1 - α) / α * (-α / (1 - α) * log2 ((d : ℝ) * lam)) :=
        mul_le_mul_of_nonneg_left (by linarith) hs
    _ = -log2 ((d : ℝ) * lam) := by
      field_simp [hα.1.ne', sub_ne_zero.mpr hα1.ne']
      <;> ring

/-- The term set is bounded above for full-rank outputs and nonnegative rates. -/
theorem spherePacking_bddAbove [NeZero n] [NeZero d] (V : CQChannel n d)
    (hV : V.FullRank) {R : ℝ} (hR : 0 ≤ R) :
    BddAbove ((fun α => spherePackingTerm V α R) '' Set.Ioc 0 1) := by
  obtain ⟨lam, hlam0, hlam⟩ := V.exists_uniform_spectral_lower_bound hV
  exact ⟨-log2 ((d : ℝ) * lam), fun _ hz => by
    obtain ⟨α, hα, rfl⟩ := hz
    exact spherePackingTerm_le_bound V hV hlam hlam0 hR hα⟩

/-- **Bound (22)**, lower half; the endpoint `α = 1` contributes zero. -/
theorem spherePacking_nonneg [NeZero n] [NeZero d] (V : CQChannel n d)
    (hV : V.FullRank) {R : ℝ} (hR : 0 ≤ R) : 0 ≤ spherePacking V R :=
  le_csSup (spherePacking_bddAbove V hV hR) (spherePackingTerm_one_mem V R)

/-- **Bound (22)**, upper half, with its necessary rate hypothesis. -/
theorem spherePacking_le_bound [NeZero n] [NeZero d] (V : CQChannel n d)
    (hd : 0 < d) (hV : V.FullRank)
    {lam : ℝ} (hlam : ∀ x i, lam ≤ (V.density x).isHermitian.eigenvalues i) (hlam0 : 0 < lam)
    (R : ℝ) (hR : 0 ≤ R) :
    spherePacking V R ≤ -log2 ((d : ℝ) * lam) := by
  apply csSup_le ⟨0, spherePackingTerm_one_mem V R⟩
  rintro z ⟨α, hα, rfl⟩
  exact spherePackingTerm_le_bound V hV hlam hlam0 hR hα

/-- A full-rank channel has a convex real sphere-packing function on positive rates. -/
theorem spherePacking_convex_on [NeZero n] [NeZero d] (V : CQChannel n d)
    (hV : V.FullRank) : ConvexOn ℝ (Set.Ioi 0) (spherePacking V) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  apply csSup_le ⟨0, spherePackingTerm_one_mem V _⟩
  rintro z ⟨α, hα, rfl⟩
  have hxle : spherePackingTerm V α x ≤ spherePacking V x :=
    le_csSup (spherePacking_bddAbove V hV (le_of_lt hx)) ⟨α, hα, rfl⟩
  have hyle : spherePackingTerm V α y ≤ spherePacking V y :=
    le_csSup (spherePacking_bddAbove V hV (le_of_lt hy)) ⟨α, hα, rfl⟩
  have heq : spherePackingTerm V α (a * x + b * y)
      = a * spherePackingTerm V α x + b * spherePackingTerm V α y := by
    by_cases h1 : α = 1
    · subst α
      simp only [spherePackingTerm_one, mul_zero, add_zero]
    · have hα1 : α < 1 := lt_of_le_of_ne hα.2 h1
      simp only [spherePackingTerm_of_Ioo V ⟨hα.1, hα1⟩]
      have ha' : a = 1 - b := by linarith
      rw [ha']
      ring
  change spherePackingTerm V α (a * x + b * y) ≤ _
  rw [heq]
  exact add_le_add (mul_le_mul_of_nonneg_left hxle ha) (mul_le_mul_of_nonneg_left hyle hb)

/-- Convexity and finiteness give the continuity used in Theorem 2. -/
theorem spherePacking_continuousOn [NeZero n] [NeZero d] (V : CQChannel n d)
    (hV : V.FullRank) : ContinuousOn (spherePacking V) (Set.Ioi 0) := by
  simpa only [interior_Ioi] using (spherePacking_convex_on V hV).continuousOn_interior

end KeyBounds

end Paper22

end

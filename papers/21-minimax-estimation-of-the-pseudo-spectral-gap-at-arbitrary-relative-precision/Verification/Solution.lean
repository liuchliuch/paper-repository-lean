import Paper21

/-!
# P21 paper-facing contracts (solution)

Namespace `P21Contract` states the five numbered results of
*Minimax estimation of the pseudo-spectral gap at arbitrary relative precision*
(Theorem 1, Theorem 2, Lemma 1, Proposition 1, Lemma 2), together with the
main intermediate contracts discharged by `PsgEst` (estimator contractivity,
hard-pair spectrum `γ = s(2-s)`, gaps of powers, KL lower-bound pieces, and the
deterministic core of Proposition 1).

Statements are written independently of the proof bodies and use only
definitions exported by `PsgEst`.  Proofs discharge the contracts from the
library. Unfinished source results retain explicit proof gaps; they cannot be
accepted by the transitive-axiom check.
-/

open Matrix BigOperators Real PsgEst
open Classical

namespace P21Contract

variable {d : ℕ}

private theorem stationary_ext_mu {S : Stoch d} (x y : Stationary S)
    (h : x.mu = y.mu) : x = y := by
  cases x with
  | mk μ hpos hsum hstation =>
    cases y with
    | mk ν hpos' hsum' hstation' =>
      dsimp only at h
      cases h
      rfl

private theorem stoch_ext_matrix (x y : Stoch d) (h : x.P = y.P) : x = y := by
  cases x with
  | mk P hn hr =>
    cases y with
    | mk Q hn' hr' =>
      dsimp only at h
      cases h
      rfl


/-! ## Theorem 1: uniform upper bound -/

/-- **Theorem 1** (Uniform upper bound).
There is a statistic `γ̂_n` (namely `gammaHat`) such that for every ergodic `P`,
every initial distribution, `0 < ε < 1/2`, `0 < δ < 1`,
`n ≥ C / (π_⋆ γ ε²) · log(8d / (δ π_⋆ γ))` implies
`P(|γ̂_n - γ| > ε γ) ≤ δ`, with `C = 73728` (any larger `C` also works).
The statistic uses only the trajectory and the known state space. -/
theorem theorem_1_spectral_package (E : Ergodic d) (n : ℕ) (ε δ C : ℝ) [NeZero d]
    (hε : 0 < ε) (hε' : ε < 1 / 2) (hδ : 0 < δ) (hδ' : δ < 1)
    (hC : 73728 ≤ C)
    (mu0 : Fin d → ℝ) (hmu : ∀ i, 0 ≤ mu0 i) (hsum : ∑ i, mu0 i = 1)
    (hn : (n : ℝ) ≥
        C / (Stationary.star E.st * gammaPS E.S E.st * ε ^ 2)
          * log (8 * (d : ℝ) / (δ * Stationary.star E.st * gammaPS E.S E.st))) :
    pathMeasure E.S.P mu0
      (Finset.univ.filter fun X : Fin (n + 1) → Fin d =>
        ε * gammaPS E.S E.st < |gammaHat X - gammaPS E.S E.st|)
      ≤ δ := by
  have hpγ : 0 < Stationary.star E.st * gammaPS E.S E.st :=
    mul_pos E.st.star_pos E.gap_pos
  have hpγ1 : Stationary.star E.st * gammaPS E.S E.st ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul (stationary_star_le_one E.S E.st) E.gap_le_one
        E.gap_pos.le (by norm_num)
      _ = 1 := by ring
  have hden : 0 < δ * Stationary.star E.st * gammaPS E.S E.st := by
    simpa only [mul_assoc] using mul_pos hδ hpγ
  have hlog : 0 ≤ log (8 * (d : ℝ) /
      (δ * Stationary.star E.st * gammaPS E.S E.st)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hden]
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
    have hdlt : δ * (Stationary.star E.st * gammaPS E.S E.st) ≤ 1 := by
      calc
        _ ≤ 1 * 1 := mul_le_mul hδ'.le hpγ1 hpγ.le (by norm_num)
        _ = 1 := by ring
    nlinarith
  have hreq : 73728 / (Stationary.star E.st * gammaPS E.S E.st * ε ^ 2) *
      log (8 * (d : ℝ) / (δ * Stationary.star E.st * gammaPS E.S E.st)) ≤ n :=
    (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hC (mul_nonneg hpγ.le (sq_nonneg ε))) hlog).trans hn
  exact PsgEst.Paper.theorem_1 E n ε δ hε hε' hδ hδ' mu0 hmu hsum hreq

/-- The uniform source theorem with the paper's actual structural ergodicity assumptions. -/
theorem theorem_1 (S : Stoch d) (st : Stationary S)
    (hirr : MatrixIrreducible S) (haper : MatrixAperiodic S)
    (n : ℕ) (ε δ C : ℝ) [NeZero d]
    (hε : 0 < ε) (hε' : ε < 1 / 2) (hδ : 0 < δ) (hδ' : δ < 1)
    (hC : 73728 ≤ C)
    (mu0 : Fin d → ℝ) (hmu : ∀ i, 0 ≤ mu0 i) (hsum : ∑ i, mu0 i = 1)
    (hn : (n : ℝ) ≥ C / (Stationary.star st * gammaPS S st * ε ^ 2) *
      log (8 * (d : ℝ) / (δ * Stationary.star st * gammaPS S st))) :
    pathMeasure S.P mu0 (Finset.univ.filter fun X : Fin (n + 1) → Fin d =>
      ε * gammaPS S st < |gammaHat X - gammaPS S st|) ≤ δ := by
  exact theorem_1_spectral_package (ergodicOfStandard S st hirr haper)
    n ε δ C hε hε' hδ hδ' hC mu0 hmu hsum hn

/-! ## Theorem 2: minimax bounds -/

/-- **Theorem 2** (Minimax bounds), lower and upper bounds on the minimax
sample size `n*`.  The class `C(d,p,g)` consists of ergodic chains on `Fin d`
with `π_⋆ ≥ p` and `γ_ps ≥ g`.  The minimax size is the least `n` for which
some trajectory-based estimator has relative error `≤ ε` with success
probability `≥ 2/3`, uniformly over the class and all deterministic initial
states.  One may take `c = 1/2048`; the lower bound holds even for reversible
chains with a common known stationary law. -/
theorem theorem_2 [NeZero d] (hd : 2 ≤ d) (p g ε : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / d) (hg : 0 < g) (hg' : g ≤ 1 / 8)
    (hε : 0 < ε) (hε' : ε < 1 / 2) :
    (1 / 2048 : ℝ) / (p * g * ε ^ 2) ≤ standardNStar d p g ε ∧
    (standardNStar d p g ε : ℝ) ≤ 73729 / (p * g * ε ^ 2) * log (24 * d / (p * g)) := by
  rw [standardNStar_eq_nStar d p g ε hg]
  exact PsgEst.Paper.theorem_2 hd p g ε hp hp' hg hg' hε hε'

/-- The fixed lower constant of Theorem 2, without an added existence premise. -/
theorem theorem_2_lower [NeZero d] (hd : 2 ≤ d) (p g ε : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / d) (hg : 0 < g) (hg' : g ≤ 1 / 8)
    (hε : 0 < ε) (hε' : ε < 1 / 2) :
    (1 / 2048 : ℝ) / (p * g * ε ^ 2) ≤ standardNStar d p g ε := by
  rw [standardNStar_eq_nStar d p g ε hg]
  exact PsgEst.Paper.theorem_2_lower hd p g ε hp hp' hg hg' hε hε'

/-- A single explicit universal upper constant, independent of all model parameters. -/
theorem theorem_2_upper [NeZero d] (hd : 2 ≤ d) (p g ε : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / d) (hg : 0 < g) (hg' : g ≤ 1 / 8)
    (hε : 0 < ε) (hε' : ε < 1 / 2) :
    (standardNStar d p g ε : ℝ) ≤ 73729 / (p * g * ε ^ 2) * log (24 * d / (p * g)) := by
  rw [standardNStar_eq_nStar d p g ε hg]
  exact PsgEst.Paper.theorem_2_upper hd p g ε hp hp' hg hg' hε hε'

/-- Theorem 2's necessary sample-size bound, directly for every successful estimator. -/
theorem minimax_necessary_sample [NeZero d] (hd : 2 ≤ d) (p g ε : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / d) (hg : 0 < g) (hg' : g ≤ 1 / 8)
    (hε : 0 < ε) (hε' : ε < 1 / 2)
    (n : ℕ) (est : (Fin (n + 1) → Fin d) → ℝ)
    (hacc : standardRelativelyAccurate n d est p g ε) :
    (1 / 2048 : ℝ) / (p * g * ε ^ 2) ≤ n :=
  PsgEst.minimax_lower d hd p g ε hp hp' hg hg' hε hε' n est
    ((standardRelativelyAccurate_iff n d est p g ε hg).mp hacc)

/-- The same lower bound on strictly positive reversible chains with a fixed,
known stationary distribution, as asserted after Theorem 2. -/
theorem reversible_known_stationary_lower [NeZero d] (hd : 2 ≤ d) (p g ε : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / d) (hg : 0 < g) (hg' : g ≤ 1 / 8)
    (hε : 0 < ε) (hε' : ε < 1 / 2)
    (n : ℕ) (est : (Fin (n + 1) → Fin d) → ℝ)
    (hacc : ∀ (S : Stoch d) (st : Stationary S),
      (∀ i j, 0 < S.P i j) →
      (∀ i j, st.mu i * S.P i j = st.mu j * S.P j i) →
      st.mu = hardMu d p → p ≤ Stationary.star st → g ≤ gammaPS S st →
      ∀ x0 : Fin d,
        2/3 ≤ pathMeasure S.P (fun i => if i=x0 then 1 else 0)
          {X | |est X - gammaPS S st| ≤ ε * gammaPS S st}) :
    (1 / 2048 : ℝ) / (p * g * ε ^ 2) ≤ n :=
  PsgEst.minimax_lower_reversible_known_stationary d hd p g ε hp hp' hg hg' hε hε'
    n est hacc

/-! ## Lemma 1: gaps of powers -/

/-- **Lemma 1** (Gaps of powers).
For every integer `k ≥ 1`,
`(1/4) min{k γ_ps(P), 1} ≤ γ_ps(P^k) ≤ min{k γ_ps(P), 1}`.
Moreover `a_t > 1/2` for every integer `t ≥ 1/γ_ps(P)`.
The gap of the powered chain is taken at any stationary law of `P^k` with the
same stationary vector as `st` (the law is unique). -/
theorem lemma_1 (S : Stoch d) (st : Stationary S) (hgap : 0 < gammaPS S st) :
    (∀ k : ℕ, 0 < k →
      ∀ st' : Stationary (S.pow k), st'.mu = st.mu →
        (1 / 4 : ℝ) * min ((k : ℝ) * gammaPS S st) 1
          ≤ gammaPS (S.pow k) st'
        ∧ gammaPS (S.pow k) st' ≤ min ((k : ℝ) * gammaPS S st) 1)
    ∧ (∀ t : ℕ, 0 < t → (1 / gammaPS S st : ℝ) ≤ t → (1 / 2 : ℝ) < aK S st t) := by
  have h := PsgEst.lemma_1 S st hgap
  refine ⟨?_, h.2⟩
  intro k hk st' hmu
  have heq : st' = stationaryPow S st k := by
    exact stationary_ext_mu st' (stationaryPow S st k) hmu
  rw [heq]
  exact h.1 k hk

/-- **Lemma 1** in the paper's ergonomic form on an `Ergodic` package. -/
theorem lemma_1_ergodic (E : Ergodic d) :
    (∀ k : ℕ, 0 < k →
      ∀ st' : Stationary (E.S.pow k), st'.mu = E.st.mu →
        (1 / 4 : ℝ) * min ((k : ℝ) * gammaPS E.S E.st) 1
          ≤ gammaPS (E.S.pow k) st'
        ∧ gammaPS (E.S.pow k) st' ≤ min ((k : ℝ) * gammaPS E.S E.st) 1)
    ∧ (∀ t : ℕ, 0 < t → (1 / gammaPS E.S E.st : ℝ) ≤ t →
        (1 / 2 : ℝ) < aK E.S E.st t) := by
  have h := PsgEst.lemma_1 E.S E.st E.gap_pos
  refine ⟨?_, h.2⟩
  intro k hk st' hmu
  have heq : st' = stationaryPow E.S E.st k := by
    exact stationary_ext_mu st' (stationaryPow E.S E.st k) hmu
  rw [heq]
  exact h.1 k hk

/-! ## Proposition 1: regularized relative Laplacian concentration -/

/-- **Proposition 1** (Regularized relative Laplacian concentration).
Consider `m` transitions from an ergodic chain `Q` on `Fin d`, from any initial
distribution.  Let `π` be its stationary law, `p = min_i π_i`, `Γ = γ_ps(Q)`.
Write `L = D_π^{1/2} Q D_π^{-1/2}` and `h = 1 - σ_2(L)`.  Form `L̂` from the
transition counts as in (6) and `ĥ = 1 - σ_2(L̂)` when all degrees are positive.
If `τ > 0`, `0 < η ≤ 1/4`, and `m Γ ≥ 1`, then, except on an event of
probability at most
`4d/p · exp(-m p Γ η² / 36) + 4d · exp(-3 m p τ η² / 16)`,
all degrees are positive and `|ĥ - h| ≤ η(3h+τ)/(1-η)`. -/
theorem proposition_1 (m : ℕ) (Q : Stoch d) (st : Stationary Q) [NeZero d]
    (τ η : ℝ) (mu0 : Fin d → ℝ)
    (hτ : 0 < τ) (hη : 0 < η) (hη' : η ≤ 1 / 4)
    (hm : (1 : ℝ) ≤ m * gammaPS Q st)
    (hmu : ∀ i, 0 ≤ mu0 i) (hsum : ∑ i, mu0 i = 1) :
    let p := Stationary.star st
    let Γ := gammaPS Q st
    let h := 1 - sigma2 (simil st.mu Q.P)
    pathMeasure Q.P mu0
      (Finset.univ.filter fun Y : Fin (m + 1) → Fin d =>
        ¬ (degPos Y ∧
          |(1 - sigma2 (lHat Y)) - h| ≤ η * (3 * h + τ) / (1 - η)))
      ≤ 4 * d / p * exp (-(m * p * Γ * η ^ 2) / 36)
        + 4 * (d : ℝ) * exp (-(3 * m * p * τ * η ^ 2) / 16) := by
  exact PsgEst.Paper.proposition_1 m Q st τ η mu0 hτ hη hη' hm hmu hsum

/-! ## Lemma 2: visit-count bound from contraction -/

/-- **Lemma 2** (visit-count bound from contraction, Appendix A).
Let `Q` be an ergodic chain on `Fin d`, with stationary law `π`, minimum `p > 0`
and pseudo-spectral gap `Γ > 0`.  Fix `0 < η ≤ 1/4` and set
`b = ⌈(1 + 2 log(4/(η p))) / Γ⌉`.  For `m` transitions, the outgoing and
incoming degree vectors both have relative error at most `η` with probability
at least `1 - δ` whenever `m ≥ 72b/(p η²) · log(4 d b / δ)`, `0 < δ < 1`.
More precisely, if `m ≥ 2b` and `m p / (2b) ≥ 2/η`, the failure probability is
at most `4 d b · exp(-m p η² / (72 b))`. -/
theorem lemma_2 (m : ℕ) (Q : Stoch d) (st : Stationary Q) [NeZero d]
    (η δ : ℝ) (mu0 : Fin d → ℝ)
    (hη : 0 < η) (hη' : η ≤ 1 / 4) (hδ : 0 < δ) (hδ' : δ < 1)
    (hmu : ∀ i, 0 ≤ mu0 i) (hsum : ∑ i, mu0 i = 1)
    (hΓ : 0 < gammaPS Q st) :
    let p := Stationary.star st
    let Γ := gammaPS Q st
    let b : ℕ := Nat.ceil ((1 + 2 * log (4 / (η * p))) / Γ)
    let fail : Finset (Fin (m + 1) → Fin d) :=
      Finset.univ.filter fun Y => ¬ degreeEvent st.mu η Y
    (((m : ℝ) ≥ 72 * b / (p * η ^ 2) * log (4 * (d : ℝ) * b / δ))
      → pathMeasure Q.P mu0 fail ≤ δ)
    ∧
    ((2 * b ≤ m ∧ (m : ℝ) * p / (2 * b) ≥ 2 / η)
      → pathMeasure Q.P mu0 fail
          ≤ 4 * (d : ℝ) * b * exp (-((m : ℝ) * p * η ^ 2) / (72 * b))) := by
  exact PsgEst.Paper.lemma_2_paper m Q st η δ mu0 hη hη' hδ hδ' hmu hsum hΓ

/-! ## Intermediate contracts: estimator contractivity -/

/-- Contractivity of the empirical operator: for nonnegative counts with
positive row sums `r` and column sums `c`, `L̂ = diag(r)^{-1/2} C diag(c)^{-1/2}`
satisfies `‖L̂ u‖₂ ≤ ‖u‖₂`. -/
theorem lhat_contraction {m : ℕ} (Y : Fin (m + 1) → Fin d)
    (hpos : degPos Y) (u : Fin d → ℝ) :
    (∑ i, (lHat Y *ᵥ u) i ^ 2) ≤ ∑ i, u i ^ 2 :=
  PsgEst.lhat_contraction Y hpos u

/-- `L̂ √c = √r` and `‖√c‖₂ = ‖√r‖₂`, hence `σ_1(L̂) = 1`. -/
theorem lhat_sigma1_one {m : ℕ} (Y : Fin (m + 1) → Fin d) (hpos : degPos Y) :
    lHat Y *ᵥ (fun j => ((inDeg Y j : ℝ)) ^ (1 / 2 : ℝ))
      = (fun i => ((outDeg Y i : ℝ)) ^ (1 / 2 : ℝ))
    ∧ (∑ i, (((inDeg Y i : ℝ)) ^ (1 / 2 : ℝ)) ^ 2)
      = ∑ i, (((outDeg Y i : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 :=
  PsgEst.lhat_sigma1_one Y hpos

/-- Deterministic range of the empirical deficit: `0 ≤ â ≤ 1` on every data set
(including the zero-degree case, where `â = 0`). -/
theorem aHat_range {m : ℕ} (Y : Fin (m + 1) → Fin d) :
    0 ≤ aHat Y ∧ aHat Y ≤ 1 :=
  PsgEst.aHat_mem Y

/-- Estimator range: `0 ≤ γ̂_n ≤ 1` for every trajectory. -/
theorem gammaHat_range {n : ℕ} (X : Fin (n + 1) → Fin d) :
    0 ≤ gammaHat X ∧ gammaHat X ≤ 1 := by
  exact PsgEst.gammaHat_mem X

/-- Lag contribution bound: the candidate at lag `k` is at most `1/k`. -/
theorem lag_bound {n : ℕ} (X : Fin (n + 1) → Fin d) (k : ℕ) (hk : 0 < k) :
    aHat (skipPath X k) / k ≤ 1 / k :=
  PsgEst.lag_bound X k hk

/-! ## Intermediate contracts: gaps of powers machinery -/

/-- Submultiplicativity of the contraction norm `b_t = ‖P^t - Π‖_π`:
`b_{r+s} ≤ b_r · b_s`. -/
theorem bNorm_mul (S : Stoch d) (st : Stationary S) (r s : ℕ) :
    bNorm S st (r + s) ≤ bNorm S st r * bNorm S st s :=
  PsgEst.bNorm_mul S st r s

/-- Range of the contraction norm: `0 ≤ b_t ≤ 1`. -/
theorem bNorm_mem (S : Stoch d) (st : Stationary S) (t : ℕ) :
    0 ≤ bNorm S st t ∧ bNorm S st t ≤ 1 :=
  PsgEst.bNorm_mem S st t

/-- The maximizing lag `k0` of `a_k / k` satisfies `k0 ≤ 1/γ` and
`a_{k0}/k0 = γ_ps`. -/
theorem exists_max_lag (S : Stoch d) (st : Stationary S)
    (hgap : 0 < gammaPS S st) :
    ∃ k0 : ℕ, 0 < k0 ∧ aK S st k0 / k0 = gammaPS S st
      ∧ (k0 : ℝ) ≤ 1 / gammaPS S st :=
  PsgEst.exists_max_lag S st hgap

/-! ## Intermediate contracts: hard pair -/

/-- The hard pair `P_s` is reversible with stationary law `hardMu d p`, and
the stationary minimum is exactly `p`. -/
theorem hardP_reversible (hd : 2 ≤ d) (p s : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / (d : ℝ)) (hs : 0 < s) (hs' : s < 1) :
    (∀ i j, hardMu d p i * hardP d p s i j = hardMu d p j * hardP d p s j i)
    ∧ (⨅ i, hardMu d p i) = p :=
  PsgEst.hardP_reversible hd p s hp hp' hs hs'

/-- Spectrum of the hard pair: `γ_ps(P_s) = s(2-s)`, the exact transformation
between `a = 1-σ₂²` and `h = 1-σ₂`. -/
theorem hardP_gamma (hd : 2 ≤ d) (p s : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / (d : ℝ)) (hs : 0 < s) (hs' : s < 1)
    (S : Stoch d) (hSP : S.P = hardP d p s)
    (st : Stationary S) (hmu : st.mu = hardMu d p) :
    gammaPS S st = s * (2 - s) := by
  let S' := hardP_isStoch hd p s hp hp' hs hs'
  let st' := hardSt hd p s hp hp' hs hs'
  have heq : S = S' := by
    exact stoch_ext_matrix S S' hSP
  subst S
  have hst : st = st' := by
    exact stationary_ext_mu st st' hmu
  rw [hst]
  exact PsgEst.hardP_gamma hd p s hp hp' hs hs'

/-- Choosing `s0 = 1 - sqrt(1-g)` and `s1 = (1+8ε) s0` yields gaps
`g0 = g`, `g ≤ g1 ≤ 5g`, and disjoint relative-error intervals. -/
theorem hardPair_disjoint (g ε : ℝ)
    (hg : 0 < g) (hg' : g ≤ 1 / 8) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    let s0 := 1 - sqrt (1 - g)
    let s1 := (1 + 8 * ε) * s0
    let g0 := s0 * (2 - s0)
    let g1 := s1 * (2 - s1)
    g0 = g ∧ g ≤ g1 ∧ g1 ≤ 5 * g ∧ (1 + ε) * g0 < (1 - ε) * g1 :=
  PsgEst.hardPair_disjoint g ε hg hg' hε hε'

/-! ## Intermediate contracts: KL lower-bound pieces -/

/-- Paper inequality (24): for `0 < u < v < 1` with `v = (1+8ε)u ≤ 1/3`,
`KL(Ber u ‖ Ber v) ≤ 128 ε² u`. -/
theorem bernKL_le (u v ε : ℝ) (hu : 0 < u) (hv : u < v) (hv' : v ≤ 1 / 3)
    (hrel : v = (1 + 8 * ε) * u) (hε : 0 < ε) :
    bernKL u v ≤ 128 * ε ^ 2 * u :=
  PsgEst.bernKL_le u v ε hu hv hv' hrel hε

/-- Path-space KL of the hard pair from a fixed reservoir start is at most
`256 n p g ε²`, so `n ≤ 1/(2048 p g ε²)` forces total variation at most `1/4`
and every `2/3`-accurate estimator yields a test with error sum `< 3/4`. -/
theorem pathKL_hard (n : ℕ) (hd : 2 ≤ d) (p g ε : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / (d : ℝ)) (hg : 0 < g) (hg' : g ≤ 1 / 8)
    (hε : 0 < ε) (hε' : ε < 1 / 2) :
    let s0 := 1 - sqrt (1 - g)
    let s1 := (1 + 8 * ε) * s0
    let x0 : Fin d := ⟨1, by omega⟩
    let mu0 : Fin d → ℝ := fun i => if i = x0 then (1 : ℝ) else 0
    @pathKL d n (hardP d p s0) (hardP d p s1) mu0 mu0
      ≤ 256 * (n : ℝ) * p * g * ε ^ 2 := by
  letI : NeZero d := ⟨by omega⟩
  intro s0 s1 x0 mu0
  have h := pathKL_hardPair_le d n hd p g ε hp hp' hg hg' hε hε' x0
    (by show (1 : ℕ) ≠ 0; omega) mu0 rfl
  change pathKL (n := n) (hardP d p s0) (hardP d p s1) mu0 mu0 ≤ _
  have heq : pathKL (n := n) (hardP d p s0) (hardP d p s1) mu0 mu0 =
      klDist (fun X : Fin (n + 1) → Fin d => pathProb (hardP d p s0) mu0 X)
        (fun X => pathProb (hardP d p s1) mu0 X) := by
    rfl
  rw [heq]
  exact h

/-! ## Intermediate contracts: deterministic Proposition 1 core -/

/-- On the good event and under the martingale bounds,
`(1-2η)h - ητ ≤ (1+η) ĥ` and `(1-η) ĥ ≤ (1+2η)h + ητ`, hence
`|ĥ - h| ≤ η(3h+τ)/(1-η)`. -/
theorem prop1_deterministic (h τ η hhat : ℝ)
    (hη : 0 < η) (hη' : η ≤ 1 / 4) (hτ : 0 < τ) (hh : 0 ≤ h)
    (hlo : ((1 - 2 * η) * h - η * τ) / (1 + η) ≤ hhat)
    (hhi : hhat ≤ ((1 + 2 * η) * h + η * τ) / (1 - η)) :
    |hhat - h| ≤ η * (3 * h + τ) / (1 - η) :=
  PsgEst.prop1_deterministic h τ η hhat hη hη' hτ hh hlo hhi

/-- Comparison of path measures under different initial laws: `μ_i ≤ π_i / π_⋆`
gives `P_μ(E) ≤ P_π(E) / π_⋆`. -/
theorem pathMeasure_init_le (P : Matrix (Fin d) (Fin d) ℝ)
    (mu0 st : Fin d → ℝ) (hP : ∀ i j, 0 ≤ P i j) (hst : ∀ i, 0 < st i)
    (hmu : ∀ i, mu0 i ≤ st i / ⨅ j, st j)
    {n : ℕ} (E : Finset (Fin (n + 1) → Fin d)) :
    pathMeasure P mu0 E ≤ pathMeasure P st E / (⨅ j, st j) :=
  PsgEst.pathMeasure_init_le P mu0 st hP hst hmu E

/-- Ordered population Laplacian spectrum, including repeated unit singular values. -/
theorem population_laplacian_spectrum (hd : 1 < d)
    (S : Stoch d) (st : Stationary S) (t : ℕ) :
    (bipH_isHermitian (Lk S st t)).eigenvalues₀
      ⟨Fintype.card (Fin d ⊕ Fin d)-2, by simp; omega⟩ = 1-sigma2 (Lk S st t) :=
  PsgEst.Lk_bipH_second_smallest_eq hd S st t

/-- Ordered empirical Laplacian spectrum for the actual normalized counts. -/
theorem empirical_laplacian_spectrum {m : ℕ} (hd : 1 < d)
    (Y : Fin (m+1) → Fin d) (hpos : degPos Y) :
    (bipH_isHermitian (lHat Y)).eigenvalues₀
      ⟨Fintype.card (Fin d ⊕ Fin d)-2, by simp; omega⟩ = 1-sigma2 (lHat Y) :=
  PsgEst.lhat_bipH_second_smallest_eq hd Y hpos

/-- The source's relative perturbation bound uses the concrete change
of normalization; its ordered spectral comparison is proved from quadratic forms. -/
theorem matrix_relative_perturbation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H Hbar : Matrix ι ι ℝ) (hH : H.IsHermitian) (hHbar : Hbar.IsHermitian)
    (τ η : ℝ) (hη : 0 < η) (hη' : η ≤ 1 / 4) (hτ : 0 < τ)
    (hHpsd : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (H *ᵥ x))
    (hbarpsd : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (Hbar *ᵥ x))
    (hlo : ∀ x : ι → ℝ,
      (1 - 2 * η) * (x ⬝ᵥ (H *ᵥ x)) - η * τ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Hbar *ᵥ x))
    (hhi : ∀ x : ι → ℝ,
      x ⬝ᵥ (Hbar *ᵥ x) ≤ (1 + 2 * η) * (x ⬝ᵥ (H *ᵥ x)) + η * τ * (x ⬝ᵥ x))
    (t : ι → ℝ) (hT : ∀ i, 1 - η ≤ t i ∧ t i ≤ 1 + η)
    (j : Fin (Fintype.card ι)) :
    |(diagonalNormalize_isHermitian Hbar hHbar t).eigenvalues₀ j - hH.eigenvalues₀ j| ≤
      η * (3 * hH.eigenvalues₀ j + τ) / (1 - η) :=
  PsgEst.prop1_deterministic_of_matrix_bounds H Hbar hH hHbar τ η hη hη' hτ
    hHpsd hbarpsd hlo hhi t hT j

/-- Equation (2) uses the actual centered Markov operator in its stationary norm. -/
theorem weighted_norm_identity (S : Stoch d) (st : Stationary S) (t : ℕ) :
    bNorm S st t = weightedOperatorNorm st.mu ((S.pow t).P - piMat st.mu) :=
  PsgEst.bNorm_eq_weightedOperatorNorm S st t

/-- The alternative h/k estimand in Section 2 has only factor-two equivalence. -/
theorem alternative_estimand (S : Stoch d) (st : Stationary S) :
    gammaPS S st / 2 ≤ singularDeficitGamma S st ∧
    singularDeficitGamma S st ≤ gammaPS S st :=
  PsgEst.singularDeficitGamma_compare S st

/-- The actual-count deterministic implication of Proposition 1. -/
theorem actual_laplacian_error {m : ℕ} (hd : 1 < d) (S : Stoch d) (st : Stationary S)
    (k : ℕ) (Y : Fin (m+1) → Fin d) (hm : 0 < m)
    (τ η : ℝ) (hτ : 0 < τ) (hη : 0 < η) (hη' : η ≤ 1/4)
    (hout : degEvent (fun i => (outDeg Y i : ℝ) / (m : ℝ)) st.mu η)
    (hin : degEvent (fun i => (inDeg Y i : ℝ) / (m : ℝ)) st.mu η)
    (hlo : ∀ x : Fin d ⊕ Fin d → ℝ,
      (1 - 2 * η) * (x ⬝ᵥ (bipH (Lk S st k) *ᵥ x)) - η * τ * (x ⬝ᵥ x) ≤
        x ⬝ᵥ (empiricalHbar st.mu Y *ᵥ x))
    (hhi : ∀ x : Fin d ⊕ Fin d → ℝ,
      x ⬝ᵥ (empiricalHbar st.mu Y *ᵥ x) ≤
        (1 + 2 * η) * (x ⬝ᵥ (bipH (Lk S st k) *ᵥ x)) + η * τ * (x ⬝ᵥ x)) :
    degPos Y ∧ |(1 - sigma2 (lHat Y)) - (1 - sigma2 (Lk S st k))| ≤
      η * (3 * (1 - sigma2 (Lk S st k)) + τ) / (1 - η) :=
  PsgEst.prop1_deterministic_counts hd S st k Y hm τ η hτ hη hη' hout hin hlo hhi

/-- The source model class and the implementation have exactly the same
sample-size infimum, including the empty-set convention. -/
theorem source_model_class [NeZero d] (p g ε : ℝ) (hg : 0 < g) :
    standardNStar d p g ε = nStar d p g ε :=
  PsgEst.standardNStar_eq_nStar d p g ε hg

/-- Ordinary finite irreducibility and aperiodicity, rather than a spectral
surrogate, characterize the positive gap for the same stationary law. -/
theorem source_ergodicity (S : Stoch d) (st : Stationary S) :
    0 < gammaPS S st ↔ MatrixIrreducible S ∧ MatrixAperiodic S :=
  PsgEst.positive_gap_iff_irreducible_aperiodic S st

/-- The source's multiplicative reversiblization is the actual matrix
(P*)^k P^k; its gap is obtained independently from its characteristic roots. -/
theorem reversiblization_gap (hd : 1 < d) (S : Stoch d) (st : Stationary S) (k : ℕ) :
    charpolySpectralGap (reversiblization S st k) = aK S st k :=
  PsgEst.reversiblization_spectralGap_eq_aK hd S st k

/-- Appendix A's exponential contraction bound for the actual weighted norm. -/
theorem appendix_mixing (S : Stoch d) (st : Stationary S)
    (hgap : 0 < gammaPS S st) (t : ℕ) :
    weightedOperatorNorm st.mu ((S.pow t).P - piMat st.mu) ^ 2 ≤
      exp (1 - gammaPS S st * (t : ℝ)) :=
  PsgEst.weighted_centered_norm_sq_le_exp S st hgap t

/-- Conditional principal upper theorem. The two cited external concentration
theorems are explicit; this does not replace the unconditioned source contract. -/
theorem conditional_uniform_upper [NeZero d] (h : ExternalConcentrationInputs d)
    (E : Ergodic d) (n : ℕ) (ε δ : ℝ)
    (hε : 0 < ε) (hε' : ε < 1/2) (hδ : 0 < δ) (hδ' : δ < 1)
    (mu : Fin d → ℝ) (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (hn : 73728/(Stationary.star E.st*gammaPS E.S E.st*ε^2)*
      log (8*(d:ℝ)/(δ*Stationary.star E.st*gammaPS E.S E.st)) ≤ (n:ℝ)) :
    pathMeasure E.S.P mu (Finset.univ.filter fun X : Fin (n+1) → Fin d =>
      ε*gammaPS E.S E.st < |gammaHat X-gammaPS E.S E.st|) ≤ δ :=
  PsgEst.uniform_upper_from_external h E n ε δ hε hε' hδ hδ' mu hmu hsum hn

/-- Conditional principal minimax theorem on the ordinary source class. -/
theorem conditional_minimax [NeZero d] (h : ExternalConcentrationInputs d)
    (hd : 2 ≤ d) (p g ε : ℝ) (hp : 0 < p) (hp' : p ≤ 1/d)
    (hg : 0 < g) (hg' : g ≤ 1/8) (hε : 0 < ε) (hε' : ε < 1/2) :
    (1/2048 : ℝ)/(p*g*ε^2) ≤ standardNStar d p g ε ∧
    (standardNStar d p g ε : ℝ) ≤ 73729/(p*g*ε^2)*log (24*d/(p*g)) :=
  PsgEst.minimax_bounds_from_external h hd p g ε hp hp' hg hg' hε hε'

/-- Proposition 1's complete own derivation from the two original cited inputs;
the full unconditioned proposition_1 remains a separate required target. -/
theorem conditional_proposition_1 [NeZero d] {m : ℕ} (Q : Stoch d) (st : Stationary Q)
    (τ η : ℝ) (mu : Fin d → ℝ) (hτ : 0 < τ) (hη : 0 < η) (hη' : η ≤ 1/4)
    (hmΓ : 1 ≤ (m:ℝ)*gammaPS Q st) (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (hPaulin : PaulinOriginalInput Q st (gammaPS Q st))
    (hFreedman : MatrixFreedmanInput Q mu) :
    pathMeasure Q.P mu (Finset.univ.filter fun Y : Fin (m+1) → Fin d =>
      ¬ RelativeConcentration.good Q st τ η Y) ≤
      4*(d:ℝ)/Stationary.star st*exp (-((m:ℝ)*Stationary.star st*gammaPS Q st*η^2)/36) +
      4*(d:ℝ)*exp (-(3*(m:ℝ)*Stationary.star st*τ*η^2)/16) :=
  PsgEst.RelativeConcentration.proposition_1_of_external Q st τ η mu
    hτ hη hη' hmΓ hmu hsum hPaulin hFreedman

/-- Both original Lemma 2 conclusions, with only the original Freedman input explicit. -/
theorem conditional_lemma_2 [NeZero d] (h : ExternalConcentrationInputs d) (m : ℕ) (Q : Stoch d) (st : Stationary Q)
    (η δ : ℝ) (mu0 : Fin d → ℝ)
    (hη : 0 < η) (hη' : η ≤ 1 / 4) (hδ : 0 < δ) (hδ' : δ < 1)
    (hmu : ∀ i, 0 ≤ mu0 i) (hsum : ∑ i, mu0 i = 1)
    (hΓ : 0 < gammaPS Q st) :
    let p := Stationary.star st
    let Γ := gammaPS Q st
    let b : ℕ := Nat.ceil ((1 + 2 * log (4 / (η * p))) / Γ)
    let fail : Finset (Fin (m + 1) → Fin d) :=
      Finset.univ.filter fun Y => ¬ degreeEvent st.mu η Y
    (((m : ℝ) ≥ 72 * b / (p * η ^ 2) * log (4 * (d : ℝ) * b / δ))
      → pathMeasure Q.P mu0 fail ≤ δ)
    ∧
    ((2 * b ≤ m ∧ (m : ℝ) * p / (2 * b) ≥ 2 / η)
      → pathMeasure Q.P mu0 fail
          ≤ 4 * (d : ℝ) * b * exp (-((m : ℝ) * p * η ^ 2) / (72 * b))) :=
  PsgEst.lemma_2_from_external h m Q st η δ mu0 hη hη' hδ hδ' hmu hsum hΓ


/-- The corrected original Paulin inequality is proved without a probability input. -/
theorem paulin_bernstein (Q : Stoch d) (st : Stationary Q) :
    PaulinOriginalInput Q st (gammaPS Q st) :=
  PsgEst.PaulinProof.paulin_original Q st

/-- The complete original matrix Freedman input is an actual theorem. -/
theorem matrix_freedman (Q : Stoch d) (mu : Fin d → ℝ) :
    MatrixFreedmanInput Q mu := PsgEst.matrixFreedman_proved Q mu

/-- Both probability inputs used in the original principal derivations are proved. -/
theorem concentration_inputs_proved [NeZero d] : ExternalConcentrationInputs d :=
  PsgEst.externalConcentrationInputs_proved

/-- The source counterexample's complete ordered spectra, with multiplicities. -/
theorem shift_register_full_spectrum :
    List.ofFn (gramEig₀ shiftRegisterP) = [1,1,0,0] ∧
    List.ofFn (fun j : Fin (Fintype.card (Fin 4)) =>
      sqrt (max 0 (gramEig₀ shiftRegisterP j))) = [1,1,0,0] :=
  ⟨PsgEst.shiftRegister_ordered_gram_spectrum,
    PsgEst.shiftRegister_ordered_singular_spectrum⟩

/-- The appendix's alternative extra-log estimator guarantee, on the actual trajectory. -/
theorem appendix_alternative_upper [NeZero d] (E : Ergodic d)
    (n : ℕ) (ε δ : ℝ) (hε : 0 < ε) (hε2 : ε < 1/2) (hδ : 0 < δ) (hδ1 : δ < 1)
    (mu : Fin d → ℝ) (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (hn : let p := Stationary.star E.st
      let γ := gammaPS E.S E.st
      let B := 1+2*log (64/(ε*p))
      184320*B/(p*γ*ε^2)*log (40*(d:ℝ)*B/(δ*γ^2)) ≤ (n:ℝ)) :
    pathMeasure E.S.P mu (Finset.univ.filter fun X : Fin (n+1) → Fin d =>
      ε*gammaPS E.S E.st < |gammaHat X-gammaPS E.S E.st|) ≤ δ :=
  PsgEst.AlternativeUpper.uniform_upper E n ε δ hε hε2 hδ hδ1 mu hmu hsum hn

end P21Contract

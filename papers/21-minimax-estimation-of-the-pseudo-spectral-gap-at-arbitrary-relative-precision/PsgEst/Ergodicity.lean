import PsgEst.NormIdentity
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.NumberTheory.FrobeniusNumber

/-!
# Positive pseudo-spectral gap and the usual finite-chain properties

The predicates below state the standard matrix criteria literally: positive
powers connect every pair of states; the positive return lengths have gcd one;
and a single positive integer power has every entry strictly positive.  They do
not define ergodicity in terms of the pseudo-spectral gap.

All equivalences involving the spectral package quantify a given positive
stationary law. Existence and uniqueness of an invariant probability for an
arbitrary finite irreducible transition matrix are separate textbook results,
not proved or assumed as axioms here. A precise reference for that remaining
standalone bridge is Levin--Peres, *Markov Chains and Mixing Times*, second
edition (2017), Corollary 1.17; see
https://pages.uoregon.edu/dlevin/MARKOV/markovmixing.pdf . The graph-period bridge
itself is proved below using `Nat.exists_mem_closure_of_ge`.
-/

open Matrix BigOperators Real Finset Classical

namespace PsgEst

variable {d : ℕ}

/-- Standard finite-chain irreducibility: every ordered pair communicates. -/
def MatrixIrreducible (S : Stoch d) : Prop :=
  ∀ i j, ∃ n : ℕ, 0 < n ∧ 0 < (S.P ^ n) i j

/-- Standard aperiodicity, expressed as the gcd-one criterion for positive
return times: their only common natural-number divisor is one. -/
def MatrixAperiodic (S : Stoch d) : Prop :=
  ∀ (i : Fin d) (q : ℕ),
    (∀ n : ℕ, 0 < n → 0 < (S.P ^ n) i i → q ∣ n) → q = 1

/-- A primitive finite transition matrix has a strictly positive integer power. -/
def MatrixPrimitive (S : Stoch d) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ i j, 0 < (S.P ^ n) i j

/-- The standard eventual-positivity criterion. -/
def EventuallyPositive (S : Stoch d) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ i j, 0 < (S.P ^ n) i j

/-- A stochastic row contains a positive entry. -/
lemma stoch_row_exists_pos (S : Stoch d) (i : Fin d) : ∃ j, 0 < S.P i j := by
  by_contra h
  push_neg at h
  have hs : ∑ j, S.P i j ≤ 0 := Finset.sum_nonpos (fun j _ => h j)
  rw [S.row_stoch] at hs
  norm_num at hs

/-- Once a stochastic matrix power is positive, all later powers are positive. -/
theorem primitive_eventually_positive (S : Stoch d) (h : MatrixPrimitive S) :
    EventuallyPositive S := by
  obtain ⟨k, hk, hpos⟩ := h
  refine ⟨k, fun n hn => ?_⟩
  induction n, hn using Nat.le_induction with
  | base => exact hpos
  | succ n hn ih =>
    intro i j
    rw [pow_succ', Matrix.mul_apply]
    obtain ⟨a, ha⟩ := stoch_row_exists_pos S i
    exact Finset.sum_pos' (fun b _ => mul_nonneg (S.nonneg i b) (S.pow_nonneg n b j))
      ⟨a, Finset.mem_univ a, mul_pos ha (ih a j)⟩

/-- Eventual positivity implies primitivity. -/
theorem eventually_positive_primitive (S : Stoch d) (h : EventuallyPositive S) :
    MatrixPrimitive S := by
  obtain ⟨N, hN⟩ := h
  exact ⟨max N 1, by omega, hN _ (le_max_left _ _)⟩

/-- Eventual positivity implies the usual communication criterion. -/
theorem eventually_positive_irreducible (S : Stoch d) (h : EventuallyPositive S) :
    MatrixIrreducible S := by
  obtain ⟨N, hN⟩ := h
  intro i j
  exact ⟨max N 1, by omega, hN _ (le_max_left _ _) i j⟩

/-- Consecutive sufficiently large return times have gcd one. -/
theorem eventually_positive_aperiodic (S : Stoch d) (h : EventuallyPositive S) :
    MatrixAperiodic S := by
  obtain ⟨N, hN⟩ := h
  intro i q hq
  let k := max N 1
  have hk : 0 < k := by dsimp [k]; omega
  have hkN : N ≤ k := le_max_left _ _
  have h1 := hq k hk (hN k hkN i i)
  have h2 := hq (k + 1) (by omega) (hN (k + 1) (by omega) i i)
  have hdvd : q ∣ 1 := by simpa using Nat.dvd_sub h2 h1
  exact Nat.dvd_one.mp hdvd

/-- A positive pseudo-spectral gap forces the centered operator norm to become
arbitrarily small at every sufficiently late time. -/
theorem positive_gap_bNorm_small (S : Stoch d) (st : Stationary S)
    (hgap : 0 < gammaPS S st) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → bNorm S st n < δ := by
  obtain ⟨k, hk, hmax, -⟩ := exists_max_lag S st hgap
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hak : 0 < aK S st k := by
    have h := (div_pos_iff_of_pos_right hkr).mp (hmax ▸ hgap)
    exact h
  have hb2 : bNorm S st k ^ 2 = 1 - aK S st k :=
    gapB_sq (aK_gapAx S st).le_one k
  have hb0 := bNorm_nonneg S st k
  have hb1 : bNorm S st k < 1 := by nlinarith
  obtain ⟨q, hq⟩ := exists_pow_lt_of_lt_one hδ hb1
  refine ⟨q * k, fun n hn => ?_⟩
  have hqdiv : q ≤ n / k := (Nat.le_div_iff_mul_le hk).mpr hn
  have hdec : bNorm S st k ^ (n / k) ≤ bNorm S st k ^ q :=
    pow_le_pow_of_le_one hb0 (le_of_lt hb1) hqdiv
  have hkey : (n / k) * k + n % k = n := by
    rw [mul_comm]
    exact Nat.div_add_mod n k
  have hstep : bNorm S st n ≤ bNorm S st ((n / k) * k) := by
    have hm := bNorm_mul S st ((n / k) * k) (n % k)
    rw [hkey] at hm
    exact hm.trans ((mul_le_mul_of_nonneg_left (bNorm_mem S st (n % k)).2
      (bNorm_nonneg S st ((n / k) * k))).trans_eq (mul_one _))
  exact lt_of_le_of_lt (hstep.trans ((gapB_pow (aK_gapAx S st) k (n / k)).trans hdec)) hq

/-- A positive pseudo-spectral gap and positive stationary law imply the
standard eventual strict positivity of all transition probabilities. -/
theorem positive_gap_eventually_positive (S : Stoch d) (st : Stationary S)
    (hgap : 0 < gammaPS S st) : EventuallyPositive S := by
  have hd : d ≠ 0 := by
    intro hz
    subst d
    have h := st.sum_one
    simp at h
  letI : NeZero d := ⟨hd⟩
  obtain ⟨ij, -, hmin⟩ := Finset.exists_min_image
    (s := (Finset.univ : Finset (Fin d × Fin d)))
    (f := fun ij => stVec st ij.1 * stVec st ij.2) Finset.univ_nonempty
  have hδ : 0 < stVec st ij.1 * stVec st ij.2 := mul_pos (stVec_pos st _) (stVec_pos st _)
  obtain ⟨N, hN⟩ := positive_gap_bNorm_small S st hgap _ hδ
  refine ⟨N, fun n hn i j => ?_⟩
  have hb := (hN n hn).trans_le (hmin (i, j) (Finset.mem_univ _))
  have habs : |LkSub S st n i j| < stVec st i * stVec st j :=
    (LkSub_entry_abs_le_bNorm S st n i j).trans_lt hb
  have hL : 0 < Lk S st n i j := by
    have hh := (abs_lt.mp habs).1
    change -(stVec st i * stVec st j) <
      Lk S st n i j - stVec st i * stVec st j at hh
    linarith
  have hprod : (0 : ℝ) < (st.mu i) ^ (1 / 2 : ℝ) * (S.P ^ n) i j *
      (st.mu j) ^ (-(1 / 2 : ℝ)) := by
    simpa only [Lk, simil, Matrix.mul_diagonal, Matrix.diagonal_mul] using hL
  exact (mul_pos_iff_of_pos_left (Real.rpow_pos_of_pos (st.pos i) _)).mp
    ((mul_pos_iff_of_pos_right (Real.rpow_pos_of_pos (st.pos j) _)).mp hprod)

/-- In particular the paper's positive-gap package has the standard
irreducibility, aperiodicity and primitivity properties. -/
theorem positive_gap_standard_properties (S : Stoch d) (st : Stationary S)
    (hgap : 0 < gammaPS S st) :
    MatrixIrreducible S ∧ MatrixAperiodic S ∧ MatrixPrimitive S := by
  have h := positive_gap_eventually_positive S st hgap
  exact ⟨eventually_positive_irreducible S h, eventually_positive_aperiodic S h,
    eventually_positive_primitive S h⟩

private lemma mu_mul_neg_half (S : Stoch d) (st : Stationary S) (j : Fin d) :
    st.mu j * (st.mu j) ^ (-(1 / 2 : ℝ)) = (st.mu j) ^ (1 / 2 : ℝ) := by
  have h := Real.rpow_add (st.pos j) (-(1 / 2 : ℝ)) (1 : ℝ)
  rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by ring, Real.rpow_one] at h
  exact (mul_comm _ _).trans h.symm

/-- A genuine Doeblin minorization of one matrix power yields a positive
pseudo-spectral gap.  The proof constructs the residual stochastic kernel. -/
theorem minorization_positive_gap (S : Stoch d) (st : Stationary S) (hd : 1 < d)
    (k : ℕ) (hk : 0 < k) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hminor : ∀ i j, θ * st.mu j ≤ (S.P ^ k) i j) :
    0 < gammaPS S st := by
  have hden : 0 < 1 - θ := by linarith
  have hden0 : 1 - θ ≠ 0 := ne_of_gt hden
  let Q : Stoch d := {
    P := fun i j => ((S.P ^ k) i j - θ * st.mu j) / (1 - θ)
    nonneg := fun i j => div_nonneg (sub_nonneg.mpr (hminor i j)) hden.le
    row_stoch := by
      intro i
      rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
        S.pow_row_stoch, st.sum_one, mul_one, div_self hden0] }
  have hstation (j : Fin d) : ∑ i, st.mu i * (S.P ^ k) i j = st.mu j :=
    (stationaryPow S st k).station j
  let stQ : Stationary Q := {
    mu := st.mu
    pos := st.pos
    sum_one := st.sum_one
    station := by
      intro j
      change (∑ i, st.mu i * (((S.P ^ k) i j - θ * st.mu j) / (1 - θ))) = st.mu j
      simp_rw [← mul_div_assoc, mul_sub]
      rw [← Finset.sum_div, Finset.sum_sub_distrib, hstation,
        ← Finset.sum_mul, st.sum_one, one_mul]
      field_simp }
  have heq : Lk S st k = θ • piProj st + (1 - θ) • Lk Q stQ 1 := by
    ext i j
    simp only [Lk, simil, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, pow_one, piProj, stVec]
    change (st.mu i) ^ (1 / 2 : ℝ) * (S.P ^ k) i j * (st.mu j) ^ (-(1 / 2 : ℝ)) =
      θ * ((st.mu i) ^ (1 / 2 : ℝ) * (st.mu j) ^ (1 / 2 : ℝ)) +
        (1 - θ) * ((st.mu i) ^ (1 / 2 : ℝ) *
          (((S.P ^ k) i j - θ * st.mu j) / (1 - θ)) * (st.mu j) ^ (-(1 / 2 : ℝ)))
    calc
      _ = (st.mu i) ^ (1 / 2 : ℝ) * ((S.P ^ k) i j - θ * st.mu j) *
          (st.mu j) ^ (-(1 / 2 : ℝ)) +
          θ * (st.mu i) ^ (1 / 2 : ℝ) * (st.mu j * (st.mu j) ^ (-(1 / 2 : ℝ))) := by ring
      _ = _ := by
        rw [mu_mul_neg_half S st j]
        field_simp
        ring
  obtain ⟨x, hx, horth, hσ⟩ :=
    (sigma2_rayleigh_fixed (Lk S st k) (stVec st) hd (stVec_sq_sum st)
      (Lk_mulVec_stVec S st k) (Lk_transpose_mulVec_stVec S st k)
      (Lk_contraction S st k)).2
  have horth' : ∑ j, stVec st j * x j = 0 := by simpa only [mul_comm] using horth
  have hproj : piProj st *ᵥ x = 0 := by
    rw [piProj_mulVec]
    funext i
    simp [horth']
  have hact : Lk S st k *ᵥ x = (1 - θ) • (Lk Q stQ 1 *ᵥ x) := by
    rw [heq, Matrix.add_mulVec]
    simp only [Matrix.smul_mulVec, hproj, smul_zero, zero_add]
  have hcon : ∑ i, (Lk Q stQ 1 *ᵥ x) i ^ 2 ≤ 1 := by
    simpa only [hx] using Lk_contraction Q stQ 1 x
  have hσle : sigma2 (Lk S st k) ^ 2 ≤ (1 - θ) ^ 2 := by
    calc
      _ = ∑ i, (Lk S st k *ᵥ x) i ^ 2 := hσ.symm
      _ = (1 - θ) ^ 2 * ∑ i, (Lk Q stQ 1 *ᵥ x) i ^ 2 := by
        rw [hact]
        simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
      _ ≤ (1 - θ) ^ 2 := by nlinarith [sq_nonneg (1 - θ)]
  have ha : 0 < aK S st k := by
    change 0 < 1 - sigma2 (Lk S st k) ^ 2
    nlinarith
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hle := le_gapGamma (aK S st) hk (fun t => (aK_mem S st t).2)
  exact (div_pos ha hkr).trans_le (by simpa only [gammaPS_eq_gapGamma] using hle)

/-- A positive matrix power gives a concrete minorization and hence a positive
pseudo-spectral gap for any positive stationary probability law. -/
theorem primitive_positive_gap (S : Stoch d) (st : Stationary S)
    (hprim : MatrixPrimitive S) : 0 < gammaPS S st := by
  by_cases hd : 1 < d
  · letI : NeZero d := ⟨by omega⟩
    obtain ⟨k, hk, hpos⟩ := hprim
    obtain ⟨ij, -, hmin⟩ := Finset.exists_min_image
      (s := (Finset.univ : Finset (Fin d × Fin d)))
      (f := fun ij => (S.P ^ k) ij.1 ij.2) Finset.univ_nonempty
    let θ := min ((S.P ^ k) ij.1 ij.2) (1 / 2 : ℝ)
    have hθ : 0 < θ := lt_min (hpos _ _) (by norm_num)
    have hθ1 : θ < 1 := (min_le_right _ _).trans_lt (by norm_num)
    apply minorization_positive_gap S st hd k hk θ hθ hθ1
    intro i j
    have hmu1 : st.mu j ≤ 1 := by
      have h := Finset.single_le_sum (fun a _ => st.nonneg a) (Finset.mem_univ j)
      simpa only [st.sum_one] using h
    calc
      θ * st.mu j ≤ θ := mul_le_of_le_one_right hθ.le hmu1
      _ ≤ (S.P ^ k) ij.1 ij.2 := min_le_left _ _
      _ ≤ (S.P ^ k) i j := hmin (i, j) (Finset.mem_univ _)
  · have ha : aK S st 1 = 1 := by simp [aK, aOf, sigma2, hd]
    have h := le_gapGamma (aK S st) (k := 1) (by norm_num) (fun t => (aK_mem S st t).2)
    rw [ha] at h
    have hg : (1 : ℝ) ≤ gammaPS S st := by simpa [gammaPS_eq_gapGamma] using h
    linarith

/-- With a positive stationary probability law, the gap-based and standard
primitive-matrix criteria agree, by proofs in both directions. -/
theorem positive_gap_iff_primitive (S : Stoch d) (st : Stationary S) :
    0 < gammaPS S st ↔ MatrixPrimitive S := by
  exact ⟨fun h => eventually_positive_primitive S (positive_gap_eventually_positive S st h),
    primitive_positive_gap S st⟩

/-- Construct the package used in Basic from a primitive stochastic matrix and
its positive stationary law. -/
noncomputable def ergodicOfPrimitive (S : Stoch d) (st : Stationary S)
    (hprim : MatrixPrimitive S) : Ergodic d where
  S := S
  st := st
  gap_pos := primitive_positive_gap S st hprim
  gap_le_one := by
    rw [gammaPS_eq_gapGamma]
    exact gapGamma_le_one _ (fun t => (aK_mem S st t).2)

/-- The usual set of strictly positive return lengths at a state. -/
def positiveReturnTimes (S : Stoch d) (i : Fin d) : Set ℕ :=
  {n | 0 < n ∧ 0 < (S.P ^ n) i i}

/-- Our common-divisor criterion is exactly gcd one for the standard return set. -/
theorem matrixAperiodic_iff_return_gcd_one (S : Stoch d) :
    MatrixAperiodic S ↔ ∀ i, Nat.setGcd (positiveReturnTimes S i) = 1 := by
  constructor
  · intro h i
    apply h i
    intro n hn hpos
    exact Nat.setGcd_dvd_of_mem (show n ∈ positiveReturnTimes S i from ⟨hn, hpos⟩)
  · intro h i q hq
    have hdvd : q ∣ Nat.setGcd (positiveReturnTimes S i) :=
      Nat.dvd_setGcd_iff.mpr (fun n hn => hq n hn.1 hn.2)
    rw [h i] at hdvd
    exact Nat.dvd_one.mp hdvd

lemma pow_entry_pos_add (S : Stoch d) (a b : ℕ) (i r j : Fin d)
    (ha : 0 < (S.P ^ a) i r) (hb : 0 < (S.P ^ b) r j) :
    0 < (S.P ^ (a + b)) i j := by
  rw [pow_add, Matrix.mul_apply]
  exact Finset.sum_pos'
    (fun ℓ _ => mul_nonneg (S.pow_nonneg a i ℓ) (S.pow_nonneg b ℓ j))
    ⟨r, Finset.mem_univ r, mul_pos ha hb⟩

private noncomputable def returnMonoid (S : Stoch d) (i : Fin d) : AddSubmonoid ℕ where
  carrier := {n | 0 < (S.P ^ n) i i}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; exact pow_entry_pos_add S a b i i i ha hb

/-- The numerical semigroup theorem turns gcd-one return times into eventual
positive return probabilities. -/
theorem aperiodic_eventually_positive_return (S : Stoch d) (h : MatrixAperiodic S)
    (i : Fin d) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < (S.P ^ n) i i := by
  have hgcd := (matrixAperiodic_iff_return_gcd_one S).mp h i
  obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge (positiveReturnTimes S i)
  have hclosure : AddSubmonoid.closure (positiveReturnTimes S i) ≤ returnMonoid S i :=
    AddSubmonoid.closure_le.mpr (fun _ hn => hn.2)
  refine ⟨N, fun n hn => ?_⟩
  apply hclosure
  apply hN n hn
  rw [hgcd]
  exact one_dvd n

/-- The standard finite-chain graph-period bridge: irreducible and aperiodic
matrices have all entries of all sufficiently large powers strictly positive. -/
theorem irreducible_aperiodic_eventually_positive (S : Stoch d)
    (hirr : MatrixIrreducible S) (haper : MatrixAperiodic S) : EventuallyPositive S := by
  have hpair : ∀ ij : Fin d × Fin d, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 < (S.P ^ n) ij.1 ij.2 := by
    intro ij
    obtain ⟨ℓ, hℓ, hpath⟩ := hirr ij.1 ij.2
    obtain ⟨N, hN⟩ := aperiodic_eventually_positive_return S haper ij.1
    refine ⟨N + ℓ, fun n hn => ?_⟩
    have hsub : N ≤ n - ℓ := by omega
    have heq : (n - ℓ) + ℓ = n := Nat.sub_add_cancel (by omega)
    rw [← heq]
    exact pow_entry_pos_add S (n - ℓ) ℓ ij.1 ij.1 ij.2 (hN _ hsub) hpath
  choose N hN using hpair
  refine ⟨Finset.univ.sup N, fun n hn i j => ?_⟩
  exact hN (i, j) n ((Finset.le_sup (f := N) (Finset.mem_univ (i, j))).trans hn)

/-- The standard primitive criterion is equivalent to irreducibility and
aperiodicity for finite stochastic matrices. -/
theorem primitive_iff_irreducible_aperiodic (S : Stoch d) :
    MatrixPrimitive S ↔ MatrixIrreducible S ∧ MatrixAperiodic S := by
  constructor
  · intro hp
    have h := primitive_eventually_positive S hp
    exact ⟨eventually_positive_irreducible S h, eventually_positive_aperiodic S h⟩
  · rintro ⟨hi, ha⟩
    exact eventually_positive_primitive S (irreducible_aperiodic_eventually_positive S hi ha)

/-- With a positive stationary law, the paper's positive-gap criterion agrees
with the usual irreducible-and-aperiodic finite-chain criterion. -/
theorem positive_gap_iff_irreducible_aperiodic (S : Stoch d) (st : Stationary S) :
    0 < gammaPS S st ↔ MatrixIrreducible S ∧ MatrixAperiodic S := by
  rw [positive_gap_iff_primitive, primitive_iff_irreducible_aperiodic]

/-- Construct the paper's spectral package from the standard source properties,
keeping the same transition matrix and positive stationary law. -/
noncomputable def ergodicOfStandard (S : Stoch d) (st : Stationary S)
    (hi : MatrixIrreducible S) (ha : MatrixAperiodic S) : Ergodic d :=
  ergodicOfPrimitive S st ((primitive_iff_irreducible_aperiodic S).mpr ⟨hi, ha⟩)

/-- Invariance of a real weight vector propagates to every matrix power. -/
theorem invariant_weights_pow (S : Stoch d) (mu : Fin d → ℝ)
    (hstat : ∀ j, ∑ i, mu i * S.P i j = mu j) (n : ℕ) (j : Fin d) :
    ∑ i, mu i * (S.P ^ n) i j = mu j := by
  induction n with
  | zero => simp [Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ']
    change (∑ i, mu i * ∑ ℓ, S.P i ℓ * (S.P ^ n) ℓ j) = mu j
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hstat]
    exact ih

/-- Any invariant probability law of a finite irreducible chain has full support;
positivity need not be postulated separately once invariance is available. -/
theorem invariant_probability_positive (S : Stoch d) (hirr : MatrixIrreducible S)
    (mu : Fin d → ℝ) (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (hstat : ∀ j, ∑ i, mu i * S.P i j = mu j) : ∀ j, 0 < mu j := by
  have hex : ∃ i, 0 < mu i := by
    by_contra h
    push_neg at h
    have hle : ∑ i, mu i ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
    rw [hsum] at hle
    norm_num at hle
  obtain ⟨i, hi⟩ := hex
  intro j
  obtain ⟨n, hn, hpath⟩ := hirr i j
  have hle : mu i * (S.P ^ n) i j ≤ ∑ a, mu a * (S.P ^ n) a j :=
    Finset.single_le_sum (fun a _ => mul_nonneg (hmu a) (S.pow_nonneg n a j))
      (Finset.mem_univ i)
  rw [invariant_weights_pow S mu hstat n j] at hle
  exact (mul_pos hi hpath).trans_le hle

/-- The standard model can be packaged from a merely nonnegative invariant
probability vector; irreducibility supplies its strict positivity. -/
noncomputable def ergodicOfInvariantProbability (S : Stoch d)
    (hi : MatrixIrreducible S) (ha : MatrixAperiodic S)
    (mu : Fin d → ℝ) (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (hstat : ∀ j, ∑ i, mu i * S.P i j = mu j) : Ergodic d :=
  ergodicOfStandard S
    { mu := mu, pos := invariant_probability_positive S hi mu hmu hsum hstat,
      sum_one := hsum, station := hstat } hi ha

end PsgEst

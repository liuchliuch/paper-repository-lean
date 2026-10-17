import Paper02.Bounds
import Paper02.Fourier
import Paper02.LowerBound
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Polynomial.Basic

/-!
# Passing from dyadic lower bounds to all cutoffs

The infimum lemmas record nonemptiness explicitly because `rho` is a real-valued
conditional infimum.  The paper's exact Fourier decomposition supplies it.
-/

noncomputable section
namespace Paper02.Cutoff

open Paper02 Real
open scoped ENNReal

/-- Restricting the cutoff preserves both approximation and envelope. -/
lemma admissible_mono_cutoff {gp gn : ℝ → ℝ} {u : ℤ → ℝ}
    {n N : ℕ} {η ρ : ℝ} (hN : N ≤ n)
    (h : AdmissibleLSymPair gp gn u n η ρ) :
    AdmissibleLSymPair gp gn u N η ρ := by
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · intro k hk
    apply h.2.2.1 k
    exact hk.trans (by exact_mod_cast hN)
  · intro k hk
    apply h.2.2.2 k
    exact hk.trans (by exact_mod_cast hN)

/-- Increasing the allowed relative error preserves an admissible pair. -/
lemma admissible_mono_error {gp gn : ℝ → ℝ} {u : ℤ → ℝ}
    {n : ℕ} {η η' ρ : ℝ} (hu : ∀ k, 0 ≤ u k) (hη : η ≤ η')
    (h : AdmissibleLSymPair gp gn u n η ρ) :
    AdmissibleLSymPair gp gn u n η' ρ := by
  refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
  intro k hk
  exact (h.2.2.1 k hk).trans (mul_le_mul_of_nonneg_right hη (hu k))

/-- The real-valued cancellation infimum is nonnegative, including an empty set. -/
lemma rho_nonneg (u : ℤ → ℝ) (n : ℕ) (η : ℝ) : 0 ≤ rho u n η := by
  unfold rho
  by_cases h : {ρ : ℝ | 0 ≤ ρ ∧ ∃ gp gn, AdmissibleLSymPair gp gn u n η ρ}.Nonempty
  · exact le_csInf h fun _ hx => hx.1
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

/-- A uniform lower bound on all admissible pairs passes to the infimum. -/
lemma le_rho_of_pairs {u : ℤ → ℝ} {n : ℕ} {η b : ℝ}
    (hne : ∃ ρ gp gn, 0 ≤ ρ ∧ AdmissibleLSymPair gp gn u n η ρ)
    (hb : ∀ ρ gp gn, AdmissibleLSymPair gp gn u n η ρ → b ≤ ρ) :
    b ≤ rho u n η := by
  apply le_csInf
  · rcases hne with ⟨ρ, gp, gn, hρ, h⟩
    exact ⟨ρ, hρ, gp, gn, h⟩
  · rintro ρ ⟨_, gp, gn, h⟩
    exact hb ρ gp gn h

/-- Increasing the cutoff can only increase the infimum when pairs exist. -/
lemma rho_mono_cutoff {u : ℤ → ℝ} {n N : ℕ} {η : ℝ} (hN : N ≤ n)
    (hne : ∃ ρ gp gn, 0 ≤ ρ ∧ AdmissibleLSymPair gp gn u n η ρ) :
    rho u N η ≤ rho u n η := by
  apply csInf_le_csInf ⟨0, fun _ hx => hx.1⟩
  · rcases hne with ⟨ρ, gp, gn, hρ, h⟩
    exact ⟨ρ, hρ, gp, gn, h⟩
  · rintro ρ ⟨hρ, gp, gn, h⟩
    exact ⟨hρ, gp, gn, admissible_mono_cutoff hN h⟩

/-- Allowing a larger error can only reduce the optimal cost. -/
lemma rho_antitone_error {u : ℤ → ℝ} {n : ℕ} {η η' : ℝ}
    (hu : ∀ k, 0 ≤ u k) (hη : η ≤ η')
    (hne : ∃ ρ gp gn, 0 ≤ ρ ∧ AdmissibleLSymPair gp gn u n η ρ) :
    rho u n η' ≤ rho u n η := by
  apply csInf_le_csInf ⟨0, fun _ hx => hx.1⟩
  · rcases hne with ⟨ρ, gp, gn, hρ, h⟩
    exact ⟨ρ, hρ, gp, gn, h⟩
  · rintro ρ ⟨hρ, gp, gn, h⟩
    exact ⟨hρ, gp, gn, admissible_mono_error hu hη h⟩

/-- The explicit Fourier construction makes every nonnegative-error cost set nonempty. -/
lemma target_costSet_nonempty (n : ℕ) (hn : 1 ≤ n) (η : ℝ) (hη : 0 ≤ η) :
    ∃ ρ gp gn, 0 ≤ ρ ∧ AdmissibleLSymPair gp gn f n η ρ := by
  rcases Fourier.prop_3_3 n hn with ⟨gp, gn, hpair⟩
  exact ⟨6 * sqrt (2 * (n : ℝ) + 1), gp, gn, by positivity,
    admissible_mono_error f_nonneg hη hpair⟩

/-- The exact cancellation upper bound of Proposition 3.3. -/
theorem prop_3_3_rho (n : ℕ) (hn : 1 ≤ n) :
    rho f n 0 ≤ 6 * sqrt (2 * (n : ℝ) + 1) := by
  rcases Fourier.prop_3_3 n hn with ⟨gp, gn, hpair⟩
  exact rho_le_of_pair (by positivity) hpair ⟨gp, gn, hpair⟩

/-- Exact decompositions are also approximate decompositions. -/
theorem rho_eta_le_rho_zero (n : ℕ) (hn : 1 ≤ n) (η : ℝ) (hη : 0 ≤ η) :
    rho f n η ≤ rho f n 0 :=
  rho_antitone_error f_nonneg hη (target_costSet_nonempty n hn 0 le_rfl)

/-- The paper's cancellation cost with its stated empty-set convention. -/
def rhoExtended (u : ℤ → ℝ) (n : ℕ) (η : ℝ) : ℝ≥0∞ :=
  ⨅ (r : {ρ : ℝ // 0 ≤ ρ ∧ ∃ gp gn, AdmissibleLSymPair gp gn u n η ρ}),
    ENNReal.ofReal r.val

/-- Whenever the feasible set is nonempty, the original real infimum agrees
with the finite value of the extended cancellation cost. -/
lemma rhoExtended_eq_of_nonempty {u : ℤ → ℝ} {n : ℕ} {η : ℝ}
    (hne : ∃ ρ gp gn, 0 ≤ ρ ∧ AdmissibleLSymPair gp gn u n η ρ) :
    rhoExtended u n η = ENNReal.ofReal (rho u n η) := by
  obtain ⟨ρ, gp, gn, hρ, hpair⟩ := hne
  letI : Nonempty {ρ : ℝ // 0 ≤ ρ ∧ ∃ gp gn, AdmissibleLSymPair gp gn u n η ρ} :=
    ⟨⟨ρ, hρ, gp, gn, hpair⟩⟩
  rw [rhoExtended, ← ENNReal.ofReal_iInf]
  congr 1
  unfold rho
  change sInf (Set.range (fun r : {ρ : ℝ // 0 ≤ ρ ∧
    ∃ gp gn, AdmissibleLSymPair gp gn u n η ρ} => (r : ℝ))) = _
  rw [Subtype.range_coe_subtype]

/-- Empty feasible sets have cost infinity, as specified in (1.2). -/
lemma rhoExtended_eq_top_of_empty {u : ℤ → ℝ} {n : ℕ} {η : ℝ}
    (hne : ¬ ∃ ρ gp gn, 0 ≤ ρ ∧ AdmissibleLSymPair gp gn u n η ρ) :
    rhoExtended u n η = ⊤ := by
  letI : IsEmpty {ρ : ℝ // 0 ≤ ρ ∧ ∃ gp gn, AdmissibleLSymPair gp gn u n η ρ} :=
    ⟨fun r => by
      rcases r.property with ⟨hr, gp, gn, hp⟩
      exact hne ⟨r.val, gp, gn, hr, hp⟩⟩
  exact iInf_of_empty _

/-- The extended cost is infinite exactly when no admissible pair exists. -/
lemma rhoExtended_eq_top_iff (u : ℤ → ℝ) (n : ℕ) (η : ℝ) :
    rhoExtended u n η = ⊤ ↔
      ¬ ∃ ρ gp gn, 0 ≤ ρ ∧ AdmissibleLSymPair gp gn u n η ρ := by
  constructor
  · intro h hne
    rw [rhoExtended_eq_of_nonempty hne] at h
    exact ENNReal.ofReal_ne_top h
  · exact rhoExtended_eq_top_of_empty

/-- For the paper's target the exact Fourier split proves the cost is finite
and the real-valued implementation equals its value. -/
theorem target_rhoExtended_toReal (n : ℕ) (hn : 1 ≤ n) (η : ℝ) (hη : 0 ≤ η) :
    (rhoExtended f n η).toReal = rho f n η := by
  rw [rhoExtended_eq_of_nonempty (target_costSet_nonempty n hn η hη)]
  exact ENNReal.toReal_ofReal (rho_nonneg f n η)

/-- Monotonicity in the cutoff holds without any nonemptiness qualification
for the extended cost. -/
lemma rhoExtended_mono_cutoff {u : ℤ → ℝ} {n N : ℕ} {η : ℝ} (hN : N ≤ n) :
    rhoExtended u N η ≤ rhoExtended u n η := by
  apply le_iInf
  rintro ⟨ρ, hρ, gp, gn, hp⟩
  exact iInf_le_of_le ⟨ρ, hρ, gp, gn, admissible_mono_cutoff hN hp⟩ le_rfl

/-- Antitonicity in accuracy holds without a nonemptiness qualification
for the extended cost. -/
lemma rhoExtended_antitone_error {u : ℤ → ℝ} {n : ℕ} {η η' : ℝ}
    (hu : ∀ k, 0 ≤ u k) (hη : η ≤ η') :
    rhoExtended u n η' ≤ rhoExtended u n η := by
  apply le_iInf
  rintro ⟨ρ, hρ, gp, gn, hp⟩
  exact iInf_le_of_le ⟨ρ, hρ, gp, gn, admissible_mono_error hu hη hp⟩ le_rfl

/-- The dyadic scale used in Corollary 3.2. -/
lemma dyadic_choice (n : ℕ) (hn : 15 ≤ n) :
    16 ≤ 2 ^ Nat.log2 (n + 1) ∧
    2 ^ Nat.log2 (n + 1) - 1 ≤ n ∧
    n + 1 < 2 * 2 ^ Nat.log2 (n + 1) := by
  have hne : n + 1 ≠ 0 := by omega
  have hlog : 4 ≤ Nat.log2 (n + 1) := (Nat.le_log2 hne).2 (by norm_num; omega)
  have hlo := Nat.log2_self_le hne
  have hhi := Nat.lt_log2_self (n := n + 1)
  rw [pow_succ, Nat.mul_comm] at hhi
  refine ⟨?_, by omega, hhi⟩
  exact (show 16 = 2 ^ 4 by norm_num).trans_le (Nat.pow_le_pow_right (by omega) hlog)

/-- The strict denominator comparison used in the paper's all-cutoff proof. -/
lemma denominator_lt (N : ℕ) (hN : 16 ≤ N) :
    3 * (sqrt (2 * (N : ℝ)) + 3) < (13 / 2 : ℝ) * sqrt (N : ℝ) := by
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hsN : 4 ≤ sqrt (N : ℝ) := by
    have h := sqrt_le_sqrt hNr
    norm_num at h ⊢
    exact h
  have hs2 : sqrt (2 : ℝ) < 17 / 12 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hmul := mul_lt_mul_of_pos_right hs2 (by linarith : 0 < sqrt (N : ℝ))
  rw [sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith

/-- Strict improvement over `sqrt N / 8` at every eligible dyadic scale. -/
lemma numeric_strict_lower (N : ℕ) (hN : 16 ≤ N) (η : ℝ) (hη : η < 1 / 6) :
    (1 - 6 * η) * sqrt (N : ℝ) / 8 <
      (1 - 6 * η) * ((N : ℝ) - 3) / (3 * (sqrt (2 * (N : ℝ)) + 3)) := by
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hNs : 0 < sqrt (N : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hden : 0 < 3 * (sqrt (2 * (N : ℝ)) + 3) := by positivity
  have hdenlt := denominator_lt N hN
  have hprod := mul_lt_mul_of_pos_left hdenlt (by positivity : 0 < sqrt (N : ℝ) / 8)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
  have hbase : sqrt (N : ℝ) / 8 <
      ((N : ℝ) - 3) / (3 * (sqrt (2 * (N : ℝ)) + 3)) := by
    rw [lt_div_iff₀ hden]
    nlinarith
  have hpos : 0 < 1 - 6 * η := by linarith
  have h := mul_lt_mul_of_pos_left hbase hpos
  simpa only [mul_div_assoc] using h

/-- Conversion from a dyadic bound to the strict constant in (3.5). -/
lemma numeric_all_cutoffs (n N : ℕ) (hN : 16 ≤ N)
    (hlarge : (n : ℝ) + 1 < 2 * N) (η : ℝ) (hη : η < 1 / 6) :
    (1 - 6 * η) * sqrt ((n : ℝ) + 1) / (8 * sqrt 2) <
      (1 - 6 * η) * ((N : ℝ) - 3) / (3 * (sqrt (2 * (N : ℝ)) + 3)) := by
  apply lt_trans _ (numeric_strict_lower N hN η hη)
  have hs2 : 0 < sqrt (2 : ℝ) := by positivity
  have h := Bounds.cor_3_2_sqrt n N hlarge
  have hηpos : 0 < 1 - 6 * η := by linarith
  rw [div_lt_div_iff₀ (by positivity : 0 < 8 * sqrt (2 : ℝ)) (by norm_num : (0 : ℝ) < 8)]
  nlinarith [mul_lt_mul_of_pos_left h hηpos]

/-- The complete numerical chain (3.3) at relative error `1/100`. -/
lemma eta_inv100_chain (N : ℕ) (hN : 16 ≤ N) :
    (47 : ℝ) * ((N : ℝ) - 3) / (150 * (sqrt (2 * (N : ℝ)) + 3)) ≥
      (N : ℝ) / (6 * (sqrt (2 * (N : ℝ)) + 3)) ∧
    (N : ℝ) / (6 * (sqrt (2 * (N : ℝ)) + 3)) ≥ sqrt (N : ℝ) / (12 * sqrt 2) := by
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : 0 < sqrt (2 * (N : ℝ)) + 3 := by positivity
  have hs2 : 0 < sqrt (2 : ℝ) := by positivity
  constructor
  · rw [ge_iff_le, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Bounds.eta_inv100_first N hN]
  · have hthree := Bounds.three_le_sqrt_twoN N hN
    have hmul : sqrt (N : ℝ) * sqrt (2 * (N : ℝ)) = (N : ℝ) * sqrt 2 := by
      rw [sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)]
    rw [ge_iff_le, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hthree (sqrt_nonneg (N : ℝ))]

/-- Specialization of (3.5), including the paper's strict `1/24` constant. -/
lemma eta_inv100_constant (n : ℕ) :
    sqrt ((n : ℝ) + 1) / 24 <
      (1 - 6 * (1 / 100 : ℝ)) * sqrt ((n : ℝ) + 1) / (8 * sqrt 2) := by
  have hs : 0 < sqrt ((n : ℝ) + 1) := by positivity
  have hs2 : 0 < sqrt (2 : ℝ) := by positivity
  have hs2lt : sqrt (2 : ℝ) < 2 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 24) (by positivity)]
  nlinarith [mul_lt_mul_of_pos_right hs2lt hs]

/-- A convenient uniform upper comparison on positive cutoffs. -/
lemma upper_sqrt_scale (n : ℕ) (hn : 1 ≤ n) :
    6 * sqrt (2 * (n : ℝ) + 1) ≤ 12 * sqrt (n : ℝ) := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := sqrt_le_sqrt (show 2 * (n : ℝ) + 1 ≤ 4 * n by linarith)
  rw [sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at h
  norm_num at h
  linarith

/-- A convenient positive lower comparison for the square-root order. -/
lemma lower_sqrt_scale (n : ℕ) (η : ℝ) (hη : η < 1 / 6) :
    (1 - 6 * η) * sqrt (n : ℝ) / 16 <
      (1 - 6 * η) * sqrt ((n : ℝ) + 1) / (8 * sqrt 2) := by
  have hs2 : 0 < sqrt (2 : ℝ) := by positivity
  have hs2lt : sqrt (2 : ℝ) < 2 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hns := sqrt_lt_sqrt (show (0 : ℝ) ≤ n by positivity)
    (show (n : ℝ) < (n : ℝ) + 1 by linarith)
  have ha : 0 < 1 - 6 * η := by linarith
  have hpos : 0 < sqrt ((n : ℝ) + 1) := by positivity
  have hmul := mul_lt_mul_of_pos_right hs2lt hpos
  rw [mul_comm (sqrt (2 : ℝ))] at hmul
  have hle := mul_le_mul_of_nonneg_right hns.le hs2.le
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 16) (by positivity)]
  nlinarith [mul_lt_mul_of_pos_left (lt_of_le_of_lt hle hmul) ha]

open Asymptotics Filter

/-- Numerical bounds of (1.7) imply the asserted square-root Theta order. -/
lemma isTheta_sqrt_of_bounds (R : ℕ → ℝ) (η : ℝ) (hη : η < 1 / 6)
    (hb : ∀ n : ℕ, 15 ≤ n →
      (1 - 6 * η) * sqrt ((n : ℝ) + 1) / (8 * sqrt 2) < R n ∧
      R n ≤ 6 * sqrt (2 * (n : ℝ) + 1)) :
    R =Θ[atTop] (fun n : ℕ => sqrt (n : ℝ)) := by
  have ha : 0 < 1 - 6 * η := by linarith
  constructor
  · apply isBigO_iff.2
    refine ⟨12, (eventually_ge_atTop 15).mono ?_⟩
    intro n hn
    have hl := (hb n hn).1
    have hu := (hb n hn).2.trans (upper_sqrt_scale n (by omega))
    have hr : 0 ≤ R n := le_trans (by positivity) hl.le
    simpa only [Real.norm_of_nonneg hr, Real.norm_of_nonneg (sqrt_nonneg _)] using hu
  · apply isBigO_iff.2
    refine ⟨16 / (1 - 6 * η), (eventually_ge_atTop 15).mono ?_⟩
    intro n hn
    have hl := (lower_sqrt_scale n η hη).trans (hb n hn).1
    have hr : 0 ≤ R n := le_trans (by positivity) (hb n hn).1.le
    rw [Real.norm_of_nonneg hr, Real.norm_of_nonneg (sqrt_nonneg _)]
    rw [div_mul_eq_mul_div, le_div_iff₀ ha]
    linarith

/-- Every power of `log (2n)` is little-oh of `sqrt n`. -/
lemma log_pow_isLittleO_sqrt (k : ℕ) :
    (fun n : ℕ => log (2 * (n : ℝ)) ^ k) =o[atTop]
      (fun n : ℕ => sqrt (n : ℝ)) := by
  have ht : Tendsto (fun n : ℕ => 2 * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto ht
  have h' : (fun n : ℕ => log (2 * (n : ℝ)) ^ k) =o[atTop]
      (fun n : ℕ => sqrt 2 * sqrt (n : ℝ)) := by
    simpa only [Function.comp_def, Real.rpow_natCast, ← Real.sqrt_eq_rpow, sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] using h
  exact h'.of_const_mul_right

/-- Square-root growth excludes every fixed power of `log (2n)`. -/
lemma not_isBigO_log_pow_of_isTheta (R : ℕ → ℝ)
    (hR : R =Θ[atTop] (fun n : ℕ => sqrt (n : ℝ))) (k : ℕ) :
    ¬ R =O[atTop] (fun n : ℕ => log (2 * (n : ℝ)) ^ k) := by
  intro hbad
  have hsmall := (hR.2.trans hbad).trans_isLittleO (log_pow_isLittleO_sqrt k)
  apply isLittleO_irrefl (f'' := fun n : ℕ => sqrt (n : ℝ)) ?_ hsmall
  apply Filter.Eventually.frequently
  apply (eventually_ge_atTop 1).mono
  intro n hn
  exact ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n by omega)))

/-- No polynomial in `log (2n)` can bound a function of square-root order. -/
lemma not_isBigO_polynomial_log_of_isTheta (R : ℕ → ℝ)
    (hR : R =Θ[atTop] (fun n : ℕ => sqrt (n : ℝ))) (P : Polynomial ℝ) :
    ¬ R =O[atTop] (fun n : ℕ => P.eval (log (2 * (n : ℝ)))) := by
  intro hbad
  have hdeg : P.degree ≤ (Polynomial.X ^ P.natDegree : Polynomial ℝ).degree := by
    simpa only [Polynomial.degree_X_pow] using P.degree_le_natDegree
  have hpoly := (Polynomial.isBigO_of_degree_le P (Polynomial.X ^ P.natDegree) hdeg).comp_tendsto
    (Real.tendsto_log_atTop.comp
      (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_natCast_atTop_atTop))
  apply not_isBigO_log_pow_of_isTheta R hR P.natDegree
  simpa using hbad.trans hpoly

/-- Proposition 3.1 specialized to the full chain of numerical constants (3.3). -/
theorem prop_3_1_eta_inv100 (m : ℕ) (ρ : ℝ) (gp gn : ℝ → ℝ)
    (hN : 16 ≤ 2 ^ m)
    (hpair : AdmissibleLSymPair gp gn f (2 ^ m - 1) (1 / 100) ρ) :
    sqrt ((2 ^ m : ℕ) : ℝ) / (12 * sqrt 2) ≤ ρ := by
  have h := LowerBound.prop_3_1 m (1 / 100) ρ gp gn hN (by norm_num) (by norm_num) hpair
  have h' : (47 : ℝ) * (((2 ^ m : ℕ) : ℝ) - 3) /
      (150 * (sqrt (2 * ((2 ^ m : ℕ) : ℝ)) + 3)) ≤ ρ := by
    convert h using 1
    field_simp
    ring
  have hc := eta_inv100_chain (2 ^ m) hN
  exact hc.2.trans (hc.1.trans h')

/-- **Corollary 3.2**, for the actual target and the entire symmetric Lévy cone. -/
theorem cor_3_2 (n : ℕ) (hn : 15 ≤ n) (η : ℝ) (hη0 : 0 ≤ η) (hη : η < 1 / 6) :
    (1 - 6 * η) * sqrt ((n : ℝ) + 1) / (8 * sqrt 2) < rho f n η := by
  obtain ⟨hN, hle, hlarge⟩ := dyadic_choice n hn
  have hbound : (1 - 6 * η) * (((2 ^ Nat.log2 (n + 1) : ℕ) : ℝ) - 3) /
      (3 * (sqrt (2 * ((2 ^ Nat.log2 (n + 1) : ℕ) : ℝ)) + 3)) ≤ rho f n η := by
    apply le_rho_of_pairs (target_costSet_nonempty n (by omega) η hη0)
    intro ρ gp gn hp
    exact LowerBound.prop_3_1 (Nat.log2 (n + 1)) η ρ gp gn hN hη0 hη
      (admissible_mono_cutoff hle hp)
  apply lt_of_lt_of_le _ hbound
  exact numeric_all_cutoffs n (2 ^ Nat.log2 (n + 1)) hN (by exact_mod_cast hlarge) η hη

/-- The strict example given immediately after Theorem 1.1. -/
theorem cor_3_2_eta_inv100 (n : ℕ) (hn : 15 ≤ n) :
    sqrt ((n : ℝ) + 1) / 24 < rho f n (1 / 100) :=
  (eta_inv100_constant n).trans (cor_3_2 n hn (1 / 100) (by norm_num) (by norm_num))

/-- The full cancellation-cost inequality (1.7) with the paper's hypotheses. -/
theorem theorem_1_1_bounds (n : ℕ) (hn : 15 ≤ n) (η : ℝ)
    (hη0 : 0 < η) (hη : η < 1 / 6) :
    (1 - 6 * η) * sqrt ((n : ℝ) + 1) / (8 * sqrt 2) < rho f n η ∧
    rho f n η ≤ rho f n 0 ∧
    rho f n 0 ≤ 6 * sqrt (2 * (n : ℝ) + 1) :=
  ⟨cor_3_2 n hn η hη0.le hη, rho_eta_le_rho_zero n (by omega) η hη0.le,
    prop_3_3_rho n (by omega)⟩

/-- The asymptotic assertion in Theorem 1.1, proved for the actual infimum. -/
theorem rho_isTheta_sqrt (η : ℝ) (hη0 : 0 ≤ η) (hη : η < 1 / 6) :
    (fun n : ℕ => rho f n η) =Θ[atTop] (fun n : ℕ => sqrt (n : ℝ)) := by
  apply isTheta_sqrt_of_bounds _ η hη
  intro n hn
  exact ⟨cor_3_2 n hn η hη0 hη,
    (rho_eta_le_rho_zero n (by omega) η hη0).trans (prop_3_3_rho n (by omega))⟩

/-- The target cost cannot be Big-O of any polynomial in `log (2n)`. -/
theorem rho_not_isBigO_polynomial_log (η : ℝ) (hη0 : 0 ≤ η) (hη : η < 1 / 6)
    (P : Polynomial ℝ) :
    ¬ (fun n : ℕ => rho f n η) =O[atTop]
      (fun n : ℕ => P.eval (log (2 * (n : ℝ)))) :=
  not_isBigO_polynomial_log_of_isTheta _ (rho_isTheta_sqrt η hη0 hη) P

/-- Consequently no fixed-error polynomial-in-logarithmic-cutoff bound exists. -/
theorem no_polynomial_log_bound (η : ℝ) (hη0 : 0 ≤ η) (hη : η < 1 / 6)
    (P : Polynomial ℝ) :
    ¬ ∀ n : ℕ, 1 ≤ n → rho f n η ≤ P.eval (log (2 * (n : ℝ))) := by
  intro hb
  apply rho_not_isBigO_polynomial_log η hη0 hη P
  apply isBigO_iff.2
  refine ⟨1, (eventually_ge_atTop 1).mono ?_⟩
  intro n hn
  rw [Real.norm_of_nonneg (rho_nonneg f n η), one_mul, Real.norm_eq_abs]
  exact (hb n hn).trans (le_abs_self _)

/-- The specialization at `η = 1/100` that refutes (1.4). -/
theorem controlled_decomposition_conjecture_false :
    ¬ ∃ P : Polynomial ℝ, ∀ n : ℕ, 1 ≤ n →
      rho f n (1 / 100) ≤ P.eval (log (2 * (n : ℝ))) := by
  rintro ⟨P, hP⟩
  exact no_polynomial_log_bound (1 / 100) (by norm_num) (by norm_num) P hP

/-- The original two-variable polynomial form (1.4) is impossible as well.
A polynomial in two variables is represented as a polynomial over `ℝ[X]`;
the outer variable is inverse accuracy and the inner variable is log cutoff. -/
theorem controlled_decomposition_conjecture_false_bivariate :
    ¬ ∃ Q : Polynomial (Polynomial ℝ), ∀ n : ℕ, 1 ≤ n →
      ∀ η : ℝ, 0 < η → η < 1 →
        rho f n η ≤ (Q.eval (Polynomial.C η⁻¹)).eval (log (2 * (n : ℝ))) := by
  rintro ⟨Q, hQ⟩
  apply controlled_decomposition_conjecture_false
  refine ⟨Q.eval (Polynomial.C 100), ?_⟩
  intro n hn
  have h := hQ n hn (1 / 100) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- The faithful extended cost of this target is always finite. -/
theorem target_rhoExtended_ne_top (n : ℕ) (hn : 1 ≤ n) (η : ℝ) (hη : 0 ≤ η) :
    rhoExtended f n η ≠ ⊤ := by
  rw [rhoExtended_eq_of_nonempty (target_costSet_nonempty n hn η hη)]
  exact ENNReal.ofReal_ne_top

/-- Equation (1.7) expressed directly in the extended nonnegative reals. -/
theorem theorem_1_1_ennreal_bounds (n : ℕ) (hn : 15 ≤ n) (η : ℝ)
    (hη0 : 0 < η) (hη : η < 1 / 6) :
    ENNReal.ofReal ((1 - 6 * η) * sqrt ((n : ℝ) + 1) / (8 * sqrt 2)) < rhoExtended f n η ∧
    rhoExtended f n η ≤ rhoExtended f n 0 ∧
    rhoExtended f n 0 ≤ ENNReal.ofReal (6 * sqrt (2 * (n : ℝ) + 1)) := by
  rw [rhoExtended_eq_of_nonempty (target_costSet_nonempty n (by omega) η hη0.le),
    rhoExtended_eq_of_nonempty (target_costSet_nonempty n (by omega) 0 le_rfl)]
  have hb := theorem_1_1_bounds n hn η hη0 hη
  have hnonneg : 0 ≤ (1 - 6 * η) * sqrt ((n : ℝ) + 1) / (8 * sqrt 2) := by
    have ha : 0 ≤ 1 - 6 * η := by linarith
    positivity
  exact ⟨(ENNReal.ofReal_lt_ofReal_iff_of_nonneg hnonneg).2 hb.1,
    ENNReal.ofReal_le_ofReal hb.2.1, ENNReal.ofReal_le_ofReal hb.2.2⟩

/-- Equation (1.7) also holds for the finite value of the faithful extended
infimum with the paper's empty-set convention. -/
theorem theorem_1_1_extended_bounds (n : ℕ) (hn : 15 ≤ n) (η : ℝ)
    (hη0 : 0 < η) (hη : η < 1 / 6) :
    (1 - 6 * η) * sqrt ((n : ℝ) + 1) / (8 * sqrt 2) < (rhoExtended f n η).toReal ∧
    (rhoExtended f n η).toReal ≤ (rhoExtended f n 0).toReal ∧
    (rhoExtended f n 0).toReal ≤ 6 * sqrt (2 * (n : ℝ) + 1) := by
  rw [target_rhoExtended_toReal n (by omega) η hη0.le,
    target_rhoExtended_toReal n (by omega) 0 le_rfl]
  exact theorem_1_1_bounds n hn η hη0 hη

end Paper02.Cutoff

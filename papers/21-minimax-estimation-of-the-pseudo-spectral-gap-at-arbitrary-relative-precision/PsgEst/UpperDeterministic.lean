import PsgEst.Estimator
import PsgEst.GapsOfPowers

/-!
# Deterministic final step of the uniform upper bound

Theorem 1 uses concentration only at lags at most `⌊1/γ⌋₊`. The empirical
contractivity bound handles every larger lag, while a maximizing population lag
supplies the lower bound. This file proves that implication and the transformation
of Proposition 1's singular-deficit error into the error of `â_k` in (21).
-/

open Matrix BigOperators Real

namespace PsgEst

variable {d : ℕ}

/-- The transformation from singular deficit `h` to squared singular deficit
`h(2-h)` is 2-Lipschitz on `[0,1]`. -/
theorem deficit_transform_lipschitz {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |x * (2 - x) - y * (2 - y)| ≤ 2 * |x - y| := by
  have hfactor : x * (2 - x) - y * (2 - y) = (x - y) * (2 - x - y) := by ring
  have hbound : |2 - x - y| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  rw [hfactor, abs_mul]
  calc |x - y| * |2 - x - y| ≤ |x - y| * 2 :=
      mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
    _ = 2 * |x - y| := mul_comm _ _

/-- The constant in (21): at `η=ε/16`, the transformed Proposition 1
error is at most `ετ`, provided `h≤τ`. -/
theorem deficit_transform_error {h hhat τ ε : ℝ}
    (hh : h ∈ Set.Icc (0 : ℝ) 1) (hhhat : hhat ∈ Set.Icc (0 : ℝ) 1)
    (hτ : 0 ≤ τ) (hhτ : h ≤ τ) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (herr : |hhat - h| ≤ (ε / 16) * (3 * h + τ) / (1 - ε / 16)) :
    |hhat * (2 - hhat) - h * (2 - h)| ≤ ε * τ := by
  have hden : 0 < 1 - ε / 16 := by linarith
  have hη : 0 ≤ ε / 16 := by positivity
  have hscale : (ε / 16) * (3 * h + τ) / (1 - ε / 16) ≤
      (ε / 16) * (4 * τ) / (1 - ε / 16) := by
    apply div_le_div_of_nonneg_right _ hden.le
    apply mul_le_mul_of_nonneg_left _ hη
    linarith
  have hcoef : 8 * (ε / 16) / (1 - ε / 16) ≤ ε := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  calc |hhat * (2 - hhat) - h * (2 - h)| ≤ 2 * |hhat - h| :=
      deficit_transform_lipschitz hhhat hh
    _ ≤ 2 * ((ε / 16) * (3 * h + τ) / (1 - ε / 16)) :=
      mul_le_mul_of_nonneg_left herr (by norm_num)
    _ ≤ 2 * ((ε / 16) * (4 * τ) / (1 - ε / 16)) :=
      mul_le_mul_of_nonneg_left hscale (by norm_num)
    _ = (8 * (ε / 16) / (1 - ε / 16)) * τ := by ring
    _ ≤ ε * τ := mul_le_mul_of_nonneg_right hcoef hτ

/-- Every population lag candidate is bounded by the pseudo-spectral gap. -/
theorem aK_div_le_gammaPS [DecidableEq (Fin d)] (S : Stoch d) (st : Stationary S)
    (k : ℕ) (hk : 0 < k) : aK S st k / k ≤ gammaPS S st := by
  rw [gammaPS_eq_gapGamma]
  exact le_gapGamma (aK S st) hk (fun t => (aK_mem S st t).2)

/-- The equivalent undivided population lag bound. -/
theorem aK_le_mul_gammaPS [DecidableEq (Fin d)] (S : Stoch d) (st : Stationary S)
    (k : ℕ) (hk : 0 < k) : aK S st k ≤ k * gammaPS S st := by
  have h := (div_le_iff₀ (Nat.cast_pos.mpr hk : (0 : ℝ) < k)).mp
    (aK_div_le_gammaPS S st k hk)
  simpa [mul_comm] using h

/-- Proposition 1's deficit bound, with `η=ε/16` and `τ=kγ`, gives exactly
(21) for the actual empirical and population operators. -/
theorem aHat_error_of_prop1 [DecidableEq (Fin d)] {n : ℕ}
    (X : Fin (n + 1) → Fin d) (S : Stoch d) (st : Stationary S)
    (hgap : 0 < gammaPS S st) (k : ℕ) (hk : 0 < k)
    (hpos : degPos (skipPath X k)) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (herr : |(1 - sigma2 (lHat (skipPath X k))) - (1 - sigma2 (Lk S st k))| ≤
      (ε / 16) * (3 * (1 - sigma2 (Lk S st k)) + k * gammaPS S st) /
        (1 - ε / 16)) :
    |aHat (skipPath X k) - aK S st k| ≤ ε * k * gammaPS S st := by
  have hs := sigma2_mem_of_contraction (Lk S st k) (Lk_contraction S st k)
  have hshat := sigma2_mem_of_contraction (lHat (skipPath X k))
    (lhat_contraction (skipPath X k) hpos)
  have hh : (1 - sigma2 (Lk S st k)) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hs.1, hs.2]
  have hhhat : (1 - sigma2 (lHat (skipPath X k))) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hshat.1, hshat.2]
  have ha : (1 - sigma2 (Lk S st k)) * (2 - (1 - sigma2 (Lk S st k))) =
      aK S st k := by unfold aK aOf; ring
  have hahat : (1 - sigma2 (lHat (skipPath X k))) *
      (2 - (1 - sigma2 (lHat (skipPath X k)))) = aHat (skipPath X k) := by
    rw [aHat_eq_of_degPos _ hpos]
    unfold aOf
    calc
      (1 - sigma2 (lHat (skipPath X k))) *
          (2 - (1 - sigma2 (lHat (skipPath X k)))) =
          1 - sigma2 (lHat (skipPath X k)) ^ 2 := by ring
      _ = _ := congrArg (fun t : ℝ => 1 - t ^ 2)
        (congrArg (fun inst : DecidableEq (Fin d) =>
          @sigma2 d (lHat (skipPath X k)) inst) (Subsingleton.elim _ _))
  have hhτ : 1 - sigma2 (Lk S st k) ≤ k * gammaPS S st := by
    have hle : 1 - sigma2 (Lk S st k) ≤ aK S st k := by
      rw [← ha]
      nlinarith [hh.1, hh.2]
    exact hle.trans (aK_le_mul_gammaPS S st k hk)
  have h := deficit_transform_error hh hhhat
    (mul_nonneg (Nat.cast_nonneg k) hgap.le) hhτ hε hε' herr
  rw [ha, hahat] at h
  simpa [mul_assoc] using h

/-- Deterministic Theorem 1 implication: simultaneous errors at small lags
control the maximum over *all* lags in the observed trajectory. -/
theorem gammaHat_error_of_small_lag_errors [DecidableEq (Fin d)] {n : ℕ}
    (X : Fin (n + 1) → Fin d) (S : Stoch d) (st : Stationary S)
    (hgap : 0 < gammaPS S st) (ε : ℝ) (hε : 0 ≤ ε)
    (hn : ⌊1 / gammaPS S st⌋₊ ≤ n)
    (hgood : ∀ k : ℕ, 0 < k → k ≤ ⌊1 / gammaPS S st⌋₊ →
      |aHat (skipPath X k) - aK S st k| ≤ ε * k * gammaPS S st) :
    |gammaHat X - gammaPS S st| ≤ ε * gammaPS S st := by
  have hεγ : 0 ≤ ε * gammaPS S st := mul_nonneg hε hgap.le
  have hupper : gammaHat X ≤ gammaPS S st + ε * gammaPS S st := by
    apply gammaHat_le X _ (by positivity)
    intro k hk hkn
    have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    by_cases hkK : k ≤ ⌊1 / gammaPS S st⌋₊
    · have herr := (abs_le.mp (hgood k hk hkK)).2
      calc aHat (skipPath X k) / k ≤
          (aK S st k + ε * k * gammaPS S st) / k :=
            div_le_div_of_nonneg_right (by linarith) hkR.le
        _ = aK S st k / k + ε * gammaPS S st := by
            field_simp
        _ ≤ gammaPS S st + ε * gammaPS S st :=
            add_le_add_right (aK_div_le_gammaPS S st k hk) _
    · have hinv : 1 / gammaPS S st < (k : ℝ) :=
        (Nat.floor_lt (by positivity)).mp (Nat.lt_of_not_ge hkK)
      have hlarge : (1 : ℝ) / k < gammaPS S st := by
        apply (div_lt_iff₀ hkR).mpr
        have h := (div_lt_iff₀ hgap).mp hinv
        simpa [mul_comm] using h
      exact (lag_bound X k hk).trans (hlarge.le.trans (by linarith))
  obtain ⟨k0, hk0, hmax, hk0R⟩ := exists_max_lag S st hgap
  have hk0K : k0 ≤ ⌊1 / gammaPS S st⌋₊ := Nat.le_floor hk0R
  have hk0n : k0 ≤ n := hk0K.trans hn
  have hk0pos : (0 : ℝ) < k0 := Nat.cast_pos.mpr hk0
  have herr := (abs_le.mp (hgood k0 hk0 hk0K)).1
  have hlower : gammaPS S st - ε * gammaPS S st ≤ gammaHat X := by
    calc gammaPS S st - ε * gammaPS S st =
        (aK S st k0 - ε * k0 * gammaPS S st) / k0 := by
          rw [sub_div, hmax]
          congr 1
          field_simp
      _ ≤ aHat (skipPath X k0) / k0 :=
          div_le_div_of_nonneg_right (by linarith) hk0pos.le
      _ ≤ gammaHat X := gammaHat_candidate_le X k0 hk0 hk0n
  rw [abs_le]
  constructor <;> linarith

/-- Direct deterministic completion of Theorem 1 on the simultaneous good event
from Proposition 1 at the small lags. -/
theorem gammaHat_error_of_prop1_bounds [DecidableEq (Fin d)] {n : ℕ}
    (X : Fin (n + 1) → Fin d) (S : Stoch d) (st : Stationary S)
    (hgap : 0 < gammaPS S st) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (hn : ⌊1 / gammaPS S st⌋₊ ≤ n)
    (hgood : ∀ k : ℕ, 0 < k → k ≤ ⌊1 / gammaPS S st⌋₊ →
      degPos (skipPath X k) ∧
      |(1 - sigma2 (lHat (skipPath X k))) - (1 - sigma2 (Lk S st k))| ≤
        (ε / 16) * (3 * (1 - sigma2 (Lk S st k)) + k * gammaPS S st) /
          (1 - ε / 16)) :
    |gammaHat X - gammaPS S st| ≤ ε * gammaPS S st := by
  apply gammaHat_error_of_small_lag_errors X S st hgap ε hε.le hn
  intro k hk hkK
  exact aHat_error_of_prop1 X S st hgap k hk (hgood k hk hkK).1 ε hε hε'
    (hgood k hk hkK).2

end PsgEst

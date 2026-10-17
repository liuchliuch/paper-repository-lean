import PUT.Basic
import PUT.Fourier

/-!
# Creation-direction coefficient bounds (paper 24, (12)–(14))

The principal creation contribution splits into a cutoff-change term and a
posterior-mean displacement term.  This file supplies the displacement
estimate `‖√q - √u‖² ≤ R/(a² d)` and the numerical `h`-identity.
-/

noncomputable section
namespace PUT

/-- Legacy scalar coefficient convention. The actual normalized `D₊`
coefficient is `PUT.Principal.creationPlus` in `PrincipalCoefficients`. -/
def createCoeffPlus (a A : ℝ) {d : ℕ} (k : Fin d → ℕ) (i : Fin d) : ℝ :=
  (1 / Real.sqrt (d : ℝ)) * (cutoff A (degUp k i) * createCoeff a k i - cutoff A k)

/-- Legacy scalar convention; the actual normalized `D₋` coefficient is
`PUT.Principal.creationMinus` in `PrincipalCoefficients`. -/
def createCoeffMinus (a A : ℝ) {d : ℕ} (k : Fin d → ℕ) (i : Fin d) : ℝ :=
  (1 / Real.sqrt (d : ℝ)) * (cutoff A k * createCoeff a k i - cutoff A (degUp k i))

/-! ## Square-root estimates -/

/-- `(√x - √y)² ≤ (x - y)² / y` for `0 ≤ x` and `0 < y`. -/
theorem sq_sqrt_sub_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) :
    (Real.sqrt x - Real.sqrt y) ^ 2 ≤ (x - y) ^ 2 / y := by
  have hsum : 0 < Real.sqrt x + Real.sqrt y := by
    have : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
    positivity
  have hxy : (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) = x - y := by
    calc (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y)
        = (Real.sqrt x) ^ 2 - (Real.sqrt y) ^ 2 := by ring
      _ = x - y := by rw [Real.sq_sqrt hx, Real.sq_sqrt (le_of_lt hy)]
  have hkey : Real.sqrt x - Real.sqrt y = (x - y) / (Real.sqrt x + Real.sqrt y) := by
    rw [eq_div_iff_mul_eq (ne_of_gt hsum)]
    exact hxy
  have hge : y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have h1 : Real.sqrt y ≤ Real.sqrt x + Real.sqrt y := by
      nlinarith [Real.sqrt_nonneg x]
    have h2 : (Real.sqrt y) ^ 2 ≤ (Real.sqrt x + Real.sqrt y) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg y) h1 2
    rwa [Real.sq_sqrt (le_of_lt hy)] at h2
  calc (Real.sqrt x - Real.sqrt y) ^ 2
      = ((x - y) / (Real.sqrt x + Real.sqrt y)) ^ 2 := by rw [hkey]
    _ = (x - y) ^ 2 / (Real.sqrt x + Real.sqrt y) ^ 2 := by rw [div_pow]
    _ ≤ (x - y) ^ 2 / y :=
      div_le_div_of_nonneg_left (sq_nonneg _) hy hge

/-! ## Posterior mean bookkeeping -/

/-- `q_i - 1/d = (k_i - K/d) / S`. -/
theorem postMean_sub_one_div {d : ℕ} (a : ℝ) (k : Fin d → ℕ) (i : Fin d)
    (ha : 0 < a) (hd : 0 < d) :
    postMean a k i - (1:ℝ) / d
      = ((k i : ℝ) - (degK k : ℝ) / d) / postTotal a k := by
  have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have hSne : a * (d:ℝ) + (degK k : ℝ) ≠ 0 := by
    have h1 : 0 < a * (d:ℝ) := mul_pos ha (by exact_mod_cast hd)
    have h2 : (0:ℝ) ≤ degK k := Nat.cast_nonneg _
    linarith
  have hsub : ∀ x y z w : ℝ, y ≠ 0 → w ≠ 0 → x / y - z / w = (x * w - z * y) / (y * w) := by
    intro x y z w hy hw
    have := div_sub_div x z hy hw
    rw [mul_comm y z] at this
    exact this
  unfold postMean postTotal
  rw [hsub (a + (k i : ℝ)) (a * d + (degK k : ℝ)) 1 d hSne hd']
  have hnum : (a + (k i : ℝ)) * d - 1 * (a * d + (degK k : ℝ))
      = (k i : ℝ) * d - (degK k : ℝ) := by ring
  rw [hnum]
  have key : ((k i : ℝ) * d - (degK k : ℝ)) / ((a * d + (degK k : ℝ)) * d)
      = ((k i : ℝ) - (degK k : ℝ) / d) / (a * d + (degK k : ℝ)) := by
    field_simp [hd', hSne]
  exact key

/-- Sum of squared deviations of the degree vector from its mean: at most `R`. -/
theorem sum_sq_dev_le {d : ℕ} (k : Fin d → ℕ) (hd : 0 < d) :
    ∑ i, ((k i : ℝ) - (degK k : ℝ) / d) ^ 2 ≤ (degR k : ℝ) := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hde : (d:ℝ) ≠ 0 := ne_of_gt hd'
  have hK : (degK k : ℝ) = ∑ i, (k i : ℝ) := degK_coe k
  have hR : (degR k : ℝ) = ∑ i, (k i : ℝ) ^ 2 := degR_coe k
  have heq : ∀ i : Fin d, ((k i : ℝ) - (degK k : ℝ) / d) ^ 2
      = (k i : ℝ) ^ 2 - 2 * ((k i : ℝ) * ((degK k : ℝ) / d))
          + ((degK k : ℝ) / d) ^ 2 := by
    intro i
    rw [sub_sq]
    ring
  have h2 : (∑ i : Fin d, 2 * ((k i : ℝ) * ((degK k : ℝ) / d)))
      = 2 * ((degK k : ℝ) / d) * degK k := by
    have hfactor : (fun i : Fin d => 2 * ((k i : ℝ) * ((degK k : ℝ) / d)))
        = (fun i : Fin d => 2 * ((degK k : ℝ) / d) * (k i : ℝ)) := by
      funext i; ring
    have h2b : (∑ i : Fin d, 2 * ((k i : ℝ) * ((degK k : ℝ) / d)))
        = (∑ i : Fin d, 2 * ((degK k : ℝ) / d) * (k i : ℝ)) :=
      congrArg (fun f : Fin d → ℝ => Finset.sum (Finset.univ : Finset (Fin d)) f) hfactor
    rw [h2b, ← Finset.mul_sum, hK]
  have h3 : ∑ _i : Fin d, ((degK k : ℝ) / d) ^ 2 = (d:ℝ) * ((degK k : ℝ) / d) ^ 2 := by
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have h4 : (d:ℝ) * ((degK k : ℝ) / d) ^ 2 = ((degK k : ℝ) ^ 2 / d) := by
    have : ((degK k : ℝ) / d) ^ 2 = (degK k : ℝ) ^ 2 / d ^ 2 := div_pow _ _ _
    rw [this]
    field_simp [hde]
    try ring
  have hpos : 0 ≤ (degK k : ℝ) ^ 2 / d :=
    div_nonneg (sq_nonneg _) (le_of_lt hd')
  have h6 : 0 ≤ 2 * ((degK k : ℝ) / d) * degK k - ((degK k : ℝ) ^ 2 / d) := by
    have : 2 * ((degK k : ℝ) / d) * degK k - ((degK k : ℝ) ^ 2 / d)
        = (degK k : ℝ) ^ 2 / d := by
      have hdne : (d:ℝ) ≠ 0 := hde
      field_simp [hdne]
      try ring
    rw [this]
    exact hpos
  calc ∑ i, ((k i : ℝ) - (degK k : ℝ) / d) ^ 2
      = ∑ i, ((k i : ℝ) ^ 2 - 2 * ((k i : ℝ) * ((degK k : ℝ) / d))
          + ((degK k : ℝ) / d) ^ 2) := by
        simp_rw [heq]
    _ = ∑ i, (k i : ℝ) ^ 2
          - ∑ i, 2 * ((k i : ℝ) * ((degK k : ℝ) / d))
          + ∑ i, ((degK k : ℝ) / d) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (degR k : ℝ) - 2 * ((degK k : ℝ) / d) * degK k
          + (d:ℝ) * ((degK k : ℝ) / d) ^ 2 := by
        rw [hR, h2, h3]
    _ = (degR k : ℝ) - 2 * ((degK k : ℝ) / d) * degK k
          + ((degK k : ℝ) ^ 2 / d) := by
        rw [h4]
    _ ≤ (degR k : ℝ) := by
        linarith

/-! ## Main displacement estimate -/

/-- Square-root mean deviation `‖√q - √u‖² ≤ R/(a²d)` (paper (14)). -/
theorem sqrt_mean_dev (a : ℝ) {d : ℕ} (k : Fin d → ℕ) (ha : 0 < a) (hd : 0 < d) :
    ∑ i, (Real.sqrt (postMean a k i) - Real.sqrt ((1:ℝ) / d)) ^ 2
      ≤ (degR k : ℝ) / (a ^ 2 * d) := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hS : 0 < postTotal a k := by
    unfold postTotal
    have h1 : (0:ℝ) < a * d := mul_pos ha hd'
    have h2 : (0:ℝ) ≤ degK k := Nat.cast_nonneg _
    linarith
  have hq : ∀ i, 0 ≤ postMean a k i := by
    intro i
    unfold postMean
    have hnum : 0 ≤ a + (k i : ℝ) := by
      have : (0:ℝ) ≤ k i := Nat.cast_nonneg _
      linarith
    exact div_nonneg hnum (le_of_lt hS)
  have hstep1 : ∀ i, (Real.sqrt (postMean a k i) - Real.sqrt ((1:ℝ) / d)) ^ 2
      ≤ d * (postMean a k i - (1:ℝ) / d) ^ 2 := by
    intro i
    have h := sq_sqrt_sub_le (postMean a k i) ((1:ℝ) / d) (hq i) (by positivity)
    have h' : (postMean a k i - (1:ℝ) / d) ^ 2 / ((1:ℝ) / d)
        = d * (postMean a k i - (1:ℝ) / d) ^ 2 := by
      have h1 : (1:ℝ) / ((1:ℝ) / d) = d := by field_simp
      calc (postMean a k i - (1:ℝ) / d) ^ 2 / ((1:ℝ) / d)
          = (postMean a k i - (1:ℝ) / d) ^ 2 * ((1:ℝ) / ((1:ℝ) / d)) := by
            rw [div_eq_mul_one_div]
        _ = (postMean a k i - (1:ℝ) / d) ^ 2 * d := by rw [h1]
        _ = d * (postMean a k i - (1:ℝ) / d) ^ 2 := by ring
    rw [h'] at h
    exact h
  calc ∑ i, (Real.sqrt (postMean a k i) - Real.sqrt ((1:ℝ) / d)) ^ 2
      ≤ ∑ i, d * (postMean a k i - (1:ℝ) / d) ^ 2 :=
        Finset.sum_le_sum fun i _ => hstep1 i
    _ = d * ∑ i, (postMean a k i - (1:ℝ) / d) ^ 2 := by
        rw [Finset.mul_sum]
    _ = d * ∑ i, (((k i : ℝ) - (degK k : ℝ) / d) / postTotal a k) ^ 2 := by
        congr 1
        have hpm : ∀ i : Fin d, postMean a k i - (1:ℝ) / d
            = ((k i : ℝ) - (degK k : ℝ) / d) / postTotal a k :=
          fun i => postMean_sub_one_div a k i ha hd
        simp_rw [hpm]
    _ = d * (∑ i, ((k i : ℝ) - (degK k : ℝ) / d) ^ 2) / (postTotal a k) ^ 2 := by
        have hdiv : ∀ i, (((k i : ℝ) - (degK k : ℝ) / d) / postTotal a k) ^ 2
            = ((k i : ℝ) - (degK k : ℝ) / d) ^ 2 / (postTotal a k) ^ 2 := by
          intro i
          exact div_pow _ _ _
        simp_rw [hdiv]
        rw [← Finset.sum_div, mul_div_assoc]
    _ ≤ d * (degR k : ℝ) / (postTotal a k) ^ 2 := by
        have hX : ∑ i, ((k i : ℝ) - (degK k : ℝ) / d) ^ 2 ≤ (degR k : ℝ) :=
          sum_sq_dev_le k hd
        have hS2 : 0 < (postTotal a k) ^ 2 := pow_pos hS 2
        have hmul : d * (∑ i, ((k i : ℝ) - (degK k : ℝ) / d) ^ 2) ≤ d * (degR k : ℝ) :=
          mul_le_mul_of_nonneg_left hX (le_of_lt hd')
        exact div_le_div_of_nonneg_right hmul (le_of_lt hS2)
    _ ≤ d * (degR k : ℝ) / (a ^ 2 * d ^ 2) := by
        have hSge : a * (d:ℝ) ≤ postTotal a k := by
          unfold postTotal
          have : (0:ℝ) ≤ degK k := Nat.cast_nonneg _
          linarith
        have hSge2 : (a * (d:ℝ)) ^ 2 ≤ (postTotal a k) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (le_of_lt ha) (le_of_lt hd')) hSge 2
        have hnum : 0 ≤ d * (degR k : ℝ) :=
          mul_nonneg (le_of_lt hd') (Nat.cast_nonneg _)
        have hden2 : 0 < (a * (d:ℝ)) ^ 2 := by positivity
        have hsymm : a ^ 2 * d ^ 2 = (a * (d:ℝ)) ^ 2 := by ring
        rw [hsymm]
        exact div_le_div_of_nonneg_left hnum hden2 hSge2
    _ = (degR k : ℝ) / (a ^ 2 * d) := by
        have hd'' : (d:ℝ) ≠ 0 := ne_of_gt hd'
        field_simp
        try ring

/-- The `h` term: `A^{3/2}/(a√d) = A * √A / (a√d)`. -/
theorem h_term_bound (A a d : ℝ) (hA : 0 < A) (ha : 0 < a) (hd : 0 < d) :
    A ^ (3/2:ℝ) / (a * Real.sqrt d) = A * Real.sqrt A / (a * Real.sqrt d) := by
  have _ := ha
  have _ := hd
  have h32 : ((3:ℝ)/2) = 1 + 1/2 := by norm_num
  have h1 : A ^ (3/2:ℝ) = A ^ (1:ℝ) * A ^ (1/(2:ℝ)) := by
    rw [h32, Real.rpow_add hA 1 (1/2)]
  have h2 : A ^ (1:ℝ) = A := Real.rpow_one A
  have h3 : A ^ (1/(2:ℝ)) = Real.sqrt A := (Real.sqrt_eq_rpow A).symm
  rw [h1, h2, h3]

end PUT

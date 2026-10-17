import PUT.Basic

/-!
# Kutin collision reduction (paper 24, §4 constant-accuracy range)

For `d ≥ 8` set `D = 4 ⌊d/4⌋`.  A one-to-one instance produces `u_d`; a
four-to-one instance produces a distribution at TV distance `3D/(4d) ≥ 6/11 > 1/2`.
Kutin's collision lower bound then forces `Q = Ω(D^{1/3}) = Ω(d^{1/3})` in the
constant-accuracy regime `1/48 < ε < 1/2`.  Small dimensions `2 ≤ d < 8` are
handled by a point-mass alternative at TV distance `1 - 1/d ≥ 1/2`.
-/

noncomputable section
namespace PUT

/-- Collision instance size `D = 4 ⌊d/4⌋`. -/
def collD (d : ℕ) : ℕ := 4 * (d / 4)

/-- TV distance of the four-to-one instance is `3D/(4d)`. -/
def collTV (d : ℕ) : ℝ := (3 * collD d : ℝ) / (4 * d)

/-- For `d ≥ 8`, `D/d ≥ 8/11`, because `d = 4m + r` with `m = ⌊d/4⌋ ≥ 2`
and `0 ≤ r ≤ 3`, so `4m/(4m+r) ≥ 8/11` is equivalent to `3m ≥ 2r`. -/
theorem collD_ratio (d : ℕ) (hd : 8 ≤ d) : (8 / 11 : ℝ) ≤ collD d / d := by
  have hd0 : (0 : ℝ) < d := by
    have h8 : (0 : ℝ) < 8 := by norm_num
    exact lt_of_lt_of_le h8 (by exact_mod_cast hd)
  have hm : (2 : ℕ) ≤ d / 4 := Nat.div_le_div_right (c := 4) hd
  have hr : d % 4 ≤ 3 := by
    have := Nat.mod_lt d (by norm_num : (0 : ℕ) < 4)
    omega
  have hdecomp : (d : ℝ) = 4 * (d / 4 : ℕ) + (d % 4 : ℕ) := by
    have := (Nat.div_add_mod d 4).symm
    exact_mod_cast this
  have hm' : (2 : ℝ) ≤ (d / 4 : ℕ) := by exact_mod_cast hm
  have hr' : ((d % 4 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hr
  have key : (8 : ℝ) * d ≤ 44 * (d / 4 : ℕ) := by
    nlinarith
  have hthis : (8 / 11 : ℝ) * d ≤ (4 * (d / 4 : ℕ) : ℝ) := by
    have h11 : (0 : ℝ) < 11 := by norm_num
    have e : (8 / 11 : ℝ) * d = 8 * d / 11 := by ring
    rw [e, div_le_iff₀ h11]
    nlinarith
  have h : (8 / 11 : ℝ) ≤ (4 * (d / 4 : ℕ) : ℝ) / d := (le_div_iff₀ hd0).2 hthis
  simpa [collD] using h

/-- Hence `collTV d = 3D/(4d) ≥ 6/11 > 1/2`. -/
theorem collTV_gt_half (d : ℕ) (hd : 8 ≤ d) : (1 / 2 : ℝ) < collTV d := by
  have h611 : (1 / 2 : ℝ) < 6 / 11 := by norm_num
  have hratio : (8 / 11 : ℝ) ≤ (4 * (d / 4 : ℕ) : ℝ) / d := by
    simpa [collD] using collD_ratio d hd
  have hd0 : (0 : ℝ) < d := by
    have h8 : (0 : ℝ) < 8 := by norm_num
    exact lt_of_lt_of_le h8 (by exact_mod_cast hd)
  have h6 : (6 / 11 : ℝ) ≤ (3 * (4 * (d / 4 : ℕ)) : ℝ) / (4 * d) := by
    have hpos : (0 : ℝ) < 4 * d := by positivity
    have hposd : (0 : ℝ) < d := hd0
    have hthis : (6 / 11 : ℝ) * (4 * d) ≤ 3 * (4 * (d / 4 : ℕ)) := by
      have h11 : (0 : ℝ) < 11 := by norm_num
      have e : (6 / 11 : ℝ) * (4 * d) = 6 * (4 * d) / 11 := by ring
      rw [e, div_le_iff₀ h11]
      have h : (8 / 11 : ℝ) * d ≤ (4 * (d / 4 : ℕ) : ℝ) := (le_div_iff₀ hposd).1 hratio
      have e2 : (8 / 11 : ℝ) * d = 8 * d / 11 := by ring
      rw [e2, div_le_iff₀ h11] at h
      nlinarith
    exact (le_div_iff₀ hpos).2 hthis
  have h12 : (1 / 2 : ℝ) < (3 * (4 * (d / 4 : ℕ)) : ℝ) / (4 * d) := lt_of_lt_of_le h611 h6
  simpa [collTV, collD] using h12

/-- A point mass sits at TV distance `1 - 1/d` from uniform, at least `1/2`
when `d ≥ 2`. -/
theorem point_mass_tv (d : ℕ) (hd : 2 ≤ d) : (1 / 2 : ℝ) ≤ 1 - 1 / (d : ℝ) := by
  have hd0 : (0 : ℝ) < d := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    exact lt_of_lt_of_le h2 (by exact_mod_cast hd)
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h : (1 : ℝ) / d ≤ 1 / 2 := by
    rw [div_le_iff₀ hd0]
    nlinarith
  linarith

/-- Finite small dimensions need at least one query: the point-mass
alternative is a promised input at distance `≥ 1/2`. -/
theorem small_d_query (d : ℕ) (hd : 2 ≤ d) (_hd' : d < 8) : (1 / 2 : ℝ) ≤ 1 - 1 / (d : ℝ) :=
  point_mass_tv d hd

/-- Constant-accuracy target is `O(d^{1/3})`: for `ε > 1/48`,
`min(d^{1/3} ε^{-4/3}, √d/ε) ≤ 48^{4/3} d^{1/3}`. -/
theorem const_acc_target (d ε : ℝ) (hd : 2 ≤ d) (hε : 1 / 48 < ε) (_hε' : ε < 1 / 2) :
    theorem1Bound 1 d ε ≤ 48 ^ (4 / 3 : ℝ) * d ^ (1 / 3 : ℝ) := by
  have hε0 : 0 < ε := lt_trans (show (0 : ℝ) < 1 / 48 by norm_num) hε
  have hd13 : 0 ≤ d ^ (1 / 3 : ℝ) := by positivity
  -- ε > 1/48 ⇒ ε⁻¹ < 48
  have hεinv : ε⁻¹ < 48 := by
    have h : (1 : ℝ) < 48 * ε := by
      have h' : (48 : ℝ)⁻¹ < ε := by
        have : ((1 : ℝ) / 48) < ε := hε
        rw [one_div] at this
        exact this
      nlinarith [mul_pos (show (0 : ℝ) < 48 by norm_num) hε0]
    have : (1 : ℝ) / ε < 48 := (div_lt_iff₀ hε0).2 h
    rwa [one_div] at this
  -- ε^{-4/3} = (ε⁻¹)^{4/3} < 48^{4/3}
  have hεpow : ε ^ ((-4 / 3 : ℝ)) < 48 ^ (4 / 3 : ℝ) := by
    have hrewrite : ε ^ ((-4 / 3 : ℝ)) = ε⁻¹ ^ (4 / 3 : ℝ) := by
      rw [show ((-4 / 3 : ℝ)) = -(4 / 3 : ℝ) by ring, Real.rpow_neg (le_of_lt hε0),
        Real.inv_rpow (le_of_lt hε0)]
    rw [hrewrite]
    exact Real.rpow_lt_rpow (le_of_lt (inv_pos.mpr hε0)) hεinv (by norm_num)
  have hmin : min (d ^ (1 / 3 : ℝ) * ε ^ ((-4 / 3 : ℝ))) (Real.sqrt d / ε)
      ≤ d ^ (1 / 3 : ℝ) * ε ^ ((-4 / 3 : ℝ)) := min_le_left _ _
  have hprod : d ^ (1 / 3 : ℝ) * ε ^ ((-4 / 3 : ℝ))
      ≤ 48 ^ (4 / 3 : ℝ) * d ^ (1 / 3 : ℝ) := by
    have := mul_le_mul_of_nonneg_left (le_of_lt hεpow) hd13
    nlinarith
  unfold theorem1Bound
  rw [one_mul]
  exact le_trans hmin hprod

end PUT

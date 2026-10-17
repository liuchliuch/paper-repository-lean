import PUT.Main
import PUT.NormBound

/-!
# Actual parameter-to-query inequalities for paper 24, Section 4

The internal interface `AtScaleBound a d Q` is for one fixed, legal prior
scale `a`. It is obtained by applying the operational lower theorem with
this prior and each admissible cutoff. It is NOT an external dependency,
NOT a proof of the Fourier--Dirichlet norm estimate, and NOT an assertion
of the source main theorem. The main assembly must supply it from the actual
hard instances, their genuine query-difference bound, and TV good-event mass.

In particular, a fixed `Q` is never assumed to satisfy this interface for
all `a ≥ 1`: large `a` need not retain good-event mass for a fixed accuracy.
Only `a = dirichletScale ε` is used for the small-accuracy theorem.

Unlike the legacy `regime_assembly`, every main result below is a genuine
query-count inequality. Both cutoff choices are proved admissible, the full
printed RHS is bounded by `80` or `80√(a/d)`, and all losses from ninefold
amplification, cutoff balancing, and the fixed powers of `48` are retained.
-/
noncomputable section

namespace PUT.ParameterLowerBound

/-- Internal composition interface at one fixed legal scale. The denominator
is the full printed Lemma 1 envelope, including all three terms. -/
def AtScaleBound (a d Q : ℝ) : Prop :=
  ∀ A : ℝ, 1 ≤ A → q0 * A / (72 * lemma1RHS A a d) ≤ Q

def scaleConstant : ℝ := q0 / (72 * 80)

def smallConstant : ℝ := q0 * c0 / (72 * 80)

theorem scaleConstant_pos : 0 < scaleConstant := by norm_num [scaleConstant, q0]

theorem smallConstant_pos : 0 < smallConstant := by norm_num [smallConstant, q0, c0]

/-- The printed query-difference envelope has a strictly positive denominator. -/
theorem lemma1RHS_pos (A a d : ℝ) (hA : 1 ≤ A) (ha : 1 ≤ a) (hd : 2 ≤ d) :
    0 < lemma1RHS A a d := by
  have hA0 : 0 < A := by linarith
  have ha0 : 0 < a := by linarith
  have hd0 : 0 < d := by linarith
  unfold lemma1RHS
  positivity

/-- The low-regime cutoff is a legal cutoff `A ≥ 1`. -/
theorem low_cutoff_ge_one (a d : ℝ) (ha : 1 ≤ a) (hd : 2 ≤ d) :
    1 ≤ cutoffLow a d := by
  have ha2 : 1 ≤ a ^ 2 := by nlinarith
  have hprod : 1 ≤ d * a ^ 2 := by
    calc
      1 ≤ d := by linarith
      _ = d * 1 := by ring
      _ ≤ d * a ^ 2 := mul_le_mul_of_nonneg_left ha2 (by linarith)
  exact Real.one_le_rpow hprod (by norm_num)

/-- Splitting the low cutoff gives the first branch in (21), exactly. -/
theorem low_cutoff_eq (a d : ℝ) (ha : 0 < a) (hd : 0 < d) :
    cutoffLow a d = d ^ (1 / 3 : ℝ) * a ^ (2 / 3 : ℝ) := by
  unfold cutoffLow
  rw [Real.mul_rpow hd.le (sq_nonneg a)]
  congr 1
  rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha.le]
  norm_num

/-- In the first regime, the complete Lemma 1 RHS is at most `80`. -/
theorem low_rhs_le_eighty (a d : ℝ) (ha : 1 ≤ a) (hd : 2 ≤ d) (had : a ≤ d) :
    lemma1RHS (cutoffLow a d) a d ≤ 80 := by
  have ha0 : 0 < a := by linarith
  have hd0 : 0 < d := by linarith
  have hfirst : Real.sqrt (1 + cutoffLow a d / d) ≤ 2 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num, by linarith [low_regime_div a d ha0 hd0 had]⟩
  have hlast := low_regime_last a d ha0 hd0 had
  unfold lemma1RHS
  rw [low_regime_mid a d ha0 hd0]
  linarith

/-- In the second regime `A=a` is legal, and the complete RHS is at most
`80√(a/d)`. -/
theorem high_rhs_le_eighty (a d : ℝ) (_ha : 1 ≤ a) (hd : 2 ≤ d) (hda : d ≤ a) :
    lemma1RHS a a d ≤ 80 * Real.sqrt (a / d) := by
  have h := high_regime_bound a d (by linarith) (by linarith) hda
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    apply (Real.sqrt_le_iff).mpr
    norm_num
  have hs : 0 ≤ Real.sqrt (a / d) := Real.sqrt_nonneg _
  change lemma1RHS a a d ≤ _ at h
  nlinarith [mul_le_mul_of_nonneg_right hsqrt hs]

/-- The low-regime actual ratio dominates the minimum in (21), divided by
`80`. This is a non-reflexive ratio inequality using the full norm envelope. -/
theorem low_ratio (a d : ℝ) (ha : 1 ≤ a) (hd : 2 ≤ d) (had : a ≤ d) :
    min (d ^ (1 / 3 : ℝ) * a ^ (2 / 3 : ℝ)) (Real.sqrt (a * d)) / 80 ≤
      cutoffLow a d / lemma1RHS (cutoffLow a d) a d := by
  have hA := low_cutoff_ge_one a d ha hd
  have hB := lemma1RHS_pos (cutoffLow a d) a d hA ha hd
  have hnum : 0 ≤ cutoffLow a d := by linarith
  have hmin : min (d ^ (1 / 3 : ℝ) * a ^ (2 / 3 : ℝ)) (Real.sqrt (a * d)) ≤
      cutoffLow a d := by
    rw [low_cutoff_eq a d (by linarith) (by linarith)]
    exact min_le_left _ _
  exact (div_le_div_of_nonneg_right hmin (by norm_num)).trans
    (div_le_div_of_nonneg_left hnum hB (low_rhs_le_eighty a d ha hd had))

/-- The high-regime ratio is at least `√(ad)/80`; in particular it dominates
the minimum in (21), divided by `80`. -/
theorem high_ratio (a d : ℝ) (ha : 1 ≤ a) (hd : 2 ≤ d) (hda : d ≤ a) :
    min (d ^ (1 / 3 : ℝ) * a ^ (2 / 3 : ℝ)) (Real.sqrt (a * d)) / 80 ≤
      a / lemma1RHS a a d := by
  have ha0 : 0 < a := by linarith
  have hd0 : 0 < d := by linarith
  have hB := lemma1RHS_pos a a d ha ha hd
  have hspos : 0 < Real.sqrt (a * d) := by positivity
  have hid : Real.sqrt (a * d) * Real.sqrt (a / d) = a := by
    have h := high_term3 a d ha0 hd0
    change a / Real.sqrt (a * d) = Real.sqrt (a / d) at h
    have hmul := (div_eq_iff hspos.ne').mp h
    simpa only [mul_comm] using hmul.symm
  have hratio : Real.sqrt (a * d) / 80 ≤ a / lemma1RHS a a d := by
    apply (le_div_iff₀ hB).mpr
    calc
      Real.sqrt (a * d) / 80 * lemma1RHS a a d ≤
          Real.sqrt (a * d) / 80 * (80 * Real.sqrt (a / d)) :=
        mul_le_mul_of_nonneg_left (high_rhs_le_eighty a d ha hd hda) (by positivity)
      _ = a := by nlinarith [hid]
  exact (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)).trans hratio

/-- Full assembly of both cutoff regimes into a genuine query-count bound
at one fixed legal scale. -/
theorem regime_query_lower (a d Q : ℝ) (ha : 1 ≤ a) (hd : 2 ≤ d)
    (hQ : AtScaleBound a d Q) :
    scaleConstant * min (d ^ (1 / 3 : ℝ) * a ^ (2 / 3 : ℝ)) (Real.sqrt (a * d)) ≤ Q := by
  have hq0 : 0 ≤ q0 / 72 := by norm_num [q0]
  rcases le_total a d with had | hda
  · have h := mul_le_mul_of_nonneg_left (low_ratio a d ha hd had) hq0
    have hscaled : scaleConstant *
        min (d ^ (1 / 3 : ℝ) * a ^ (2 / 3 : ℝ)) (Real.sqrt (a * d)) ≤
        q0 * cutoffLow a d / (72 * lemma1RHS (cutoffLow a d) a d) := by
      convert h using 1
      · unfold scaleConstant
        ring
      · ring
    exact hscaled.trans (hQ _ (low_cutoff_ge_one a d ha hd))
  · have h := mul_le_mul_of_nonneg_left (high_ratio a d ha hd hda) hq0
    have hscaled : scaleConstant *
        min (d ^ (1 / 3 : ℝ) * a ^ (2 / 3 : ℝ)) (Real.sqrt (a * d)) ≤
        q0 * a / (72 * lemma1RHS a a d) := by
      convert h using 1
      · unfold scaleConstant
        ring
      · ring
    exact hscaled.trans (hQ a ha)

/-- The prior scale selected in the source is legal throughout the
small-accuracy range, including its endpoint. -/
theorem dirichletScale_ge_one {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 48) :
    1 ≤ dirichletScale ε := by
  unfold dirichletScale
  apply one_le_zpow_of_nonpos₀ (by positivity : 0 < 48 * ε)
    (by linarith : 48 * ε ≤ 1) (by norm_num : (-2 : ℤ) ≤ 0)

/-- The actual query bound for `0 < ε ≤ 1/48`, including all fixed constants
lost in (21), the substitution, and ninefold amplification. -/
theorem small_accuracy_query_lower (d ε Q : ℝ) (hd : 2 ≤ d)
    (hε : 0 < ε) (hsmall : ε ≤ 1 / 48)
    (hQ : AtScaleBound (dirichletScale ε) d Q) :
    theorem1Bound smallConstant d ε ≤ Q := by
  have hreg := regime_query_lower (dirichletScale ε) d Q
    (dirichletScale_ge_one hε hsmall) hd hQ
  have htarget := mul_le_mul_of_nonneg_left
    (regime_implies_target d ε (by linarith) hε) scaleConstant_pos.le
  have hreg' : scaleConstant *
      min (d ^ (1 / 3 : ℝ) * (dirichletScale ε) ^ (2 / 3 : ℝ))
        (Real.sqrt (d * dirichletScale ε)) ≤ Q := by
    simpa only [mul_comm (dirichletScale ε) d] using hreg
  calc
    theorem1Bound smallConstant d ε = scaleConstant * theorem1Bound c0 d ε := by
      unfold theorem1Bound smallConstant scaleConstant
      ring
    _ ≤ _ := htarget
    _ ≤ Q := hreg'

/-- Explicit absorption of the source's constant-accuracy collision bound.
The collision/Kutin input is a genuine query inequality and remains visible. -/
theorem constant_accuracy_query_lower (d ε Q k : ℝ) (hd : 2 ≤ d)
    (hε : 1 / 48 < ε) (hεmax : ε < 1 / 2) (hk : 0 < k)
    (hcollision : k * d ^ (1 / 3 : ℝ) ≤ Q) :
    theorem1Bound (k / 3000) d ε ≤ Q := by
  have hd0 : 0 < d := by linarith
  have ht : theorem1Bound 1 d ε ≤ 3000 * d ^ (1 / 3 : ℝ) :=
    (const_acc_target d ε hd hε hεmax).trans
      (mul_le_mul_of_nonneg_right pow48_le (Real.rpow_nonneg hd0.le _))
  have hscaled := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ k / 3000)
  have hbound : theorem1Bound (k / 3000) d ε ≤ k * d ^ (1 / 3 : ℝ) := by
    convert hscaled using 1
    · unfold theorem1Bound
      ring
    · ring
  exact hbound.trans hcollision

/-- One positive constant covers both accuracy ranges. -/
def finalConstant (k : ℝ) : ℝ := min smallConstant (k / 3000)

theorem finalConstant_pos {k : ℝ} (hk : 0 < k) : 0 < finalConstant k :=
  lt_min smallConstant_pos (by positivity)

/-- Full accuracy-range assembly. `hsmall` is needed only for the selected
legal scale at this `ε`, and `hcollision` only in the constant-accuracy range.
These are internal composition interfaces, not external exemptions. -/
theorem full_accuracy_query_lower (d ε Q k : ℝ) (hd : 2 ≤ d)
    (hε : 0 < ε) (hεmax : ε < 1 / 2) (hk : 0 < k)
    (hsmall : ε ≤ 1 / 48 → AtScaleBound (dirichletScale ε) d Q)
    (hcollision : 1 / 48 < ε → k * d ^ (1 / 3 : ℝ) ≤ Q) :
    theorem1Bound (finalConstant k) d ε ≤ Q := by
  have htarget : 0 ≤ min (d ^ (1 / 3 : ℝ) * ε ^ (-4 / 3 : ℝ))
      (Real.sqrt d / ε) := by positivity
  by_cases he : ε ≤ 1 / 48
  · have h := small_accuracy_query_lower d ε Q hd hε he (hsmall he)
    apply le_trans ?_ h
    exact mul_le_mul_of_nonneg_right (min_le_left smallConstant (k / 3000)) htarget
  · have he' : 1 / 48 < ε := lt_of_not_ge he
    have h := constant_accuracy_query_lower d ε Q k hd he' hεmax hk (hcollision he')
    apply le_trans ?_ h
    exact mul_le_mul_of_nonneg_right (min_le_right smallConstant (k / 3000)) htarget

/-- An explicit absolute positive final constant exists once the fixed
collision constant is supplied. The remaining interfaces refer to actual
query counts; this result does not assert the hard-instance construction. -/
theorem exists_final_constant (k : ℝ) (hk : 0 < k) :
    ∃ c : ℝ, 0 < c ∧ ∀ d ε Q : ℝ, 2 ≤ d → 0 < ε → ε < 1 / 2 →
      (ε ≤ 1 / 48 → AtScaleBound (dirichletScale ε) d Q) →
      (1 / 48 < ε → k * d ^ (1 / 3 : ℝ) ≤ Q) →
      theorem1Bound c d ε ≤ Q := by
  refine ⟨finalConstant k, finalConstant_pos hk, ?_⟩
  intro d ε Q hd hε hεmax hs hc
  exact full_accuracy_query_lower d ε Q k hd hε hεmax hk hs hc

end PUT.ParameterLowerBound

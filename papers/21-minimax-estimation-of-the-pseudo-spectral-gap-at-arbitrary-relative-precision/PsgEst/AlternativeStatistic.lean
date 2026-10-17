import PsgEst.GapsOfPowers

/-! The alternative population estimand discussed in Section 2: maximizing
`h_k/k` with `h_k=1-σ₂(L_k)` approximates the pseudo-spectral gap only up to a
factor two. The actual estimator in the paper uses the exact squared deficit. -/

open Matrix BigOperators Real
namespace PsgEst
variable {d : ℕ}

noncomputable def singularDeficit (S : Stoch d) (st : Stationary S) (k : ℕ) : ℝ :=
  1 - sigma2 (Lk S st k)

noncomputable def singularDeficitGamma (S : Stoch d) (st : Stationary S) : ℝ :=
  gapGamma (singularDeficit S st)

theorem singularDeficit_mem (S : Stoch d) (st : Stationary S) (k : ℕ) :
    singularDeficit S st k ∈ Set.Icc (0 : ℝ) 1 := by
  have hs := sigma2_mem_of_contraction (Lk S st k) (Lk_contraction S st k)
  unfold singularDeficit
  constructor <;> linarith [hs.1, hs.2]

theorem singularDeficit_compare (S : Stoch d) (st : Stationary S) (k : ℕ) :
    singularDeficit S st k ≤ aK S st k ∧
    aK S st k ≤ 2 * singularDeficit S st k := by
  have hs := sigma2_mem_of_contraction (Lk S st k) (Lk_contraction S st k)
  unfold singularDeficit aK aOf
  constructor <;> nlinarith [hs.1, hs.2]

theorem singularDeficitGamma_compare (S : Stoch d) (st : Stationary S) :
    gammaPS S st / 2 ≤ singularDeficitGamma S st ∧
    singularDeficitGamma S st ≤ gammaPS S st := by
  have hrange : ∀ k, singularDeficit S st k ≤ 1 :=
    fun k => (singularDeficit_mem S st k).2
  have hnonneg : 0 ≤ singularDeficitGamma S st := gapGamma_nonneg _ hrange
  constructor
  · have hle : gammaPS S st ≤ 2 * singularDeficitGamma S st := by
      unfold gammaPS
      apply ciSup_le
      intro k
      split_ifs with hk
      · have hcomp := div_le_div_of_nonneg_right
          (singularDeficit_compare S st k).2 (Nat.cast_nonneg k)
        have hsup := le_gapGamma (singularDeficit S st) hk hrange
        change singularDeficit S st k / (k : ℝ) ≤ singularDeficitGamma S st at hsup
        calc
          aK S st k / (k : ℝ) ≤ (2 * singularDeficit S st k) / k := hcomp
          _ = 2 * (singularDeficit S st k / k) := by ring
          _ ≤ 2 * singularDeficitGamma S st := by linarith
      · linarith
    linarith
  · unfold singularDeficitGamma gapGamma
    apply ciSup_le
    intro k
    split_ifs with hk
    · have hcomp := div_le_div_of_nonneg_right
        (singularDeficit_compare S st k).1 (Nat.cast_nonneg k)
      exact hcomp.trans (by
        rw [gammaPS_eq_gapGamma]
        exact le_gapGamma (aK S st) hk (fun t => (aK_mem S st t).2))
    · rw [gammaPS_eq_gapGamma]
      exact gapGamma_nonneg _ (fun t => (aK_mem S st t).2)

theorem singularDeficit_gapAx (S : Stoch d) (st : Stationary S) :
    GapAx (singularDeficit S st) := by
  refine ⟨fun k => (singularDeficit_mem S st k).1,
    fun k => (singularDeficit_mem S st k).2, ?_⟩
  intro r s
  have hsq := sigma2_Lk_submul S st r s
  have hr := (sigma2_mem_of_contraction (Lk S st r) (Lk_contraction S st r)).1
  have hs := (sigma2_mem_of_contraction (Lk S st s) (Lk_contraction S st s)).1
  have hrs := (sigma2_mem_of_contraction (Lk S st (r+s))
    (Lk_contraction S st (r+s))).1
  simp only [singularDeficit, sub_sub_cancel]
  nlinarith [mul_nonneg hr hs, sq_nonneg (sigma2 (Lk S st (r+s)) -
    sigma2 (Lk S st r) * sigma2 (Lk S st s))]

theorem singularDeficitGamma_exists_max (S : Stoch d) (st : Stationary S)
    (hgap : 0 < gammaPS S st) :
    ∃ k : ℕ, 0 < k ∧ singularDeficit S st k / k = singularDeficitGamma S st ∧
      (k : ℝ) ≤ 1 / singularDeficitGamma S st := by
  have hpos : 0 < singularDeficitGamma S st :=
    (div_pos hgap (by norm_num)).trans_le (singularDeficitGamma_compare S st).1
  exact gapGamma_exists_max (singularDeficit_gapAx S st) hpos

end PsgEst

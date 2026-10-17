import Paper26.OneCopyStageRoutine
import Paper26.MultiscaleRefinement

/-!
# A common integer budget for all one-copy multiscale stages

These are scalar inequalities for the actual `copyBudget` from Lemma 5.3.
A single ambient-dimensional integer is selected before the active subspaces
or observations are known.  The logarithm and integer rounding are explicit.
-/
noncomputable section
open scoped BigOperators
namespace Paper26.MultiscaleOneCopyCost
open MultiscaleRefinement

/-- The nonlogarithmic common per-stage scale. -/
def prefactor (r d L : ℕ) (e : ℝ) : ℝ :=
  (r : ℝ) * Real.sqrt r * d * Real.sqrt d * L / e

/-- One common real budget, before rounding. -/
def realBudget (r d L : ℕ) (e δ : ℝ) : ℝ :=
  2304 * prefactor r d L e * commonLog d L δ

/-- Every stage consumes exactly this many fresh copies. -/
def stageCopies (r d L : ℕ) (e δ : ℝ) : ℕ := ⌈realBudget r d L e δ⌉₊

/-- The exact integer copy count for L stages with the common stage budget. -/
def totalCopies (r d L : ℕ) (e δ : ℝ) : ℕ := stageCopies r d L e δ * L

lemma accuracy_pos {e : ℝ} (he : 0 < e) {L : ℕ} (hL : 0 < L) (j : Fin L) :
    0 < stageAccuracy e L j := by
  unfold stageAccuracy
  exact div_pos (mul_pos he (dyadicLower_pos L j)) (by positivity)

lemma commonLog_ge_log_two {d L : ℕ} (hd : 0 < d) (hL : 0 < L)
    {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    Real.log 2 ≤ commonLog d L δ := by
  have hd₁ : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hL₁ : (1:ℝ) ≤ L := by exact_mod_cast hL
  have hp : (1:ℝ) ≤ (d:ℝ)*L := one_le_mul_of_one_le_of_one_le hd₁ hL₁
  unfold commonLog
  apply Real.log_le_log (by norm_num)
  apply (le_div_iff₀ hδ).mpr
  nlinarith

lemma prefactor_ge_one {r d L : ℕ} (hr : 1 ≤ r) (hrd : r ≤ d) (hL : 0 < L)
    {e : ℝ} (he : 0 < e) (he₁ : e ≤ 1) : 1 ≤ prefactor r d L e := by
  have hr₁ : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hd₁ : (1:ℝ) ≤ d := by exact_mod_cast hr.trans hrd
  have hL₁ : (1:ℝ) ≤ L := by exact_mod_cast hL
  have hsR : 1 ≤ Real.sqrt (r:ℝ) := Real.one_le_sqrt.mpr hr₁
  have hsD : 1 ≤ Real.sqrt (d:ℝ) := Real.one_le_sqrt.mpr hd₁
  unfold prefactor
  apply (le_div_iff₀ he).mpr
  have hp : (1:ℝ) ≤ (r:ℝ)*Real.sqrt r*d*Real.sqrt d*L :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hr₁ hsR) hd₁) hsD) hL₁
  simpa only [one_mul] using he₁.trans hp

/-- The actual one-copy coefficient is dominated by the scalar stage cost. -/
lemma copyBudget_le_stageCost (r d L : ℕ) (W η δ : ℝ)
    (hW : 0 ≤ W) (hη : 0 < η) (hd : 0 < d) (hL : 0 < L)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    OneCopySubmatrix.copyBudget (ι:=Fin d) r W η (δ/(L:ℝ)) ≤
      72 * stageCost r d W η * commonLog d L δ := by
  have hlog : 0 ≤ commonLog d L δ :=
    (Real.log_pos (by norm_num : (1:ℝ)<2)).le.trans
      (commonLog_ge_log_two hd hL hδ hδ₁)
  have hlogeq : Real.log (2*(d:ℝ)/(δ/(L:ℝ))) = commonLog d L δ := by
    unfold commonLog
    congr 1
    field_simp
  unfold OneCopySubmatrix.copyBudget
  simp only [Fintype.card_fin]
  rw [hlogeq]
  apply mul_le_mul_of_nonneg_right _ hlog
  unfold stageCost
  have hfirst : 0 ≤ (r:ℝ)*d*W/η := by positivity
  have hsecond : 0 ≤ (d:ℝ)*Real.sqrt ((r:ℝ)/η) := by positivity
  have heq : 36*(r:ℝ)*d*W/η + 4*d*Real.sqrt ((r:ℝ)/η) =
      36*((r:ℝ)*d*W/η) + 4*((d:ℝ)*Real.sqrt ((r:ℝ)/η)) := by ring
  rw [heq]
  nlinarith

/-- The terminal dyadic window controls every actual ambient stage budget. -/
theorem stageBudget_le (r d L : ℕ) (e δ : ℝ)
    (hr : 1 ≤ r) (hrd : r ≤ d) (hL : 0 < L) (he : 0 < e)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hscale : e/(2*(d:ℝ)) ≤ ((2:ℝ)^L)⁻¹) (j : Fin L) :
    OneCopySubmatrix.copyBudget (ι:=Fin d) r (massAllowance r e L j)
      (stageAccuracy e L j) (δ/(L:ℝ)) ≤ realBudget r d L e δ := by
  letI : NeZero L := ⟨by omega⟩
  have hd : 0 < d := lt_of_lt_of_le (by omega : 0<r) hrd
  have hlog : 0 ≤ commonLog d L δ :=
    (Real.log_pos (by norm_num : (1:ℝ)<2)).le.trans
      (commonLog_ge_log_two hd hL hδ hδ₁)
  have hs : e/(2*(d:ℝ)) ≤ dyadicLower L j := by
    apply hscale.trans
    simpa only [dyadicLower_last] using dyadicLower_floor L j
  have hc : stageCost (r:ℝ) d (massAllowance r e L j) (stageAccuracy e L j) ≤
      32 * prefactor r d L e := by
    exact stageCost_le (by exact_mod_cast hr) (by exact_mod_cast hrd)
      (by exact_mod_cast hL) he hs rfl (massAllowance_le hr e L j)
  calc
    _ ≤ 72*stageCost r d (massAllowance r e L j) (stageAccuracy e L j)*commonLog d L δ :=
      copyBudget_le_stageCost r d L _ _ δ (massAllowance_nonneg r e L j)
        (accuracy_pos he hL j) hd hL hδ hδ₁
    _ ≤ 72*(32*prefactor r d L e)*commonLog d L δ := by gcongr
    _ = realBudget r d L e δ := by unfold realBudget; ring

/-- Positive least-dyadic stage count excludes the sole boundary scale L=0. -/
lemma e_lt_dimension_of_stages_pos (d : ℕ) {e : ℝ} (he : 0 < e)
    (hL : 0 < dyadicStages d e) : e < d := by
  by_contra hn
  have hz : dyadicStages d e ≤ 0 := by
    unfold dyadicStages
    apply Nat.find_min'
    simpa only [pow_zero] using (div_le_one he).mpr (le_of_not_gt hn)
  omega

/-- The intended least-dyadic schedule supplies the scale premise internally. -/
theorem scheduled_stageBudget_le (r d L : ℕ) (e δ : ℝ)
    (hr : 1 ≤ r) (hrd : r ≤ d) (hL : 0 < L) (he : 0 < e)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hSchedule : L = dyadicStages d e) (j : Fin L) :
    OneCopySubmatrix.copyBudget (ι:=Fin d) r (massAllowance r e L j)
      (stageAccuracy e L j) (δ/(L:ℝ)) ≤ realBudget r d L e δ := by
  apply stageBudget_le r d L e δ hr hrd hL he hδ hδ₁
  rw [hSchedule]
  exact (dyadicStages_window d he
    (e_lt_dimension_of_stages_pos d he (by simpa only [← hSchedule] using hL))).2.le

lemma realBudget_pos (r d L : ℕ) (e δ : ℝ)
    (hr : 1 ≤ r) (hrd : r ≤ d) (hL : 0 < L) (he : 0 < e) (he₁ : e ≤ 1)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) : 0 < realBudget r d L e δ := by
  have hp := prefactor_ge_one hr hrd hL he he₁
  have hl := commonLog_ge_log_two (lt_of_lt_of_le (by omega : 0<r) hrd) hL hδ hδ₁
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp₀ : 0 < prefactor r d L e := lt_of_lt_of_le zero_lt_one hp
  have hl₀ : 0 < commonLog d L δ := hlog₂.trans_le hl
  unfold realBudget
  positivity

lemma stageCopies_pos (r d L : ℕ) (e δ : ℝ)
    (hr : 1 ≤ r) (hrd : r ≤ d) (hL : 0 < L) (he : 0 < e) (he₁ : e ≤ 1)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) : 0 < stageCopies r d L e δ :=
  Nat.ceil_pos.mpr (realBudget_pos r d L e δ hr hrd hL he he₁ hδ hδ₁)

/-- One common integer budget dominates every stage's actual real budget. -/
theorem scheduled_stageBudget_le_stageCopies (r d L : ℕ) (e δ : ℝ)
    (hr : 1 ≤ r) (hrd : r ≤ d) (hL : 0 < L) (he : 0 < e)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hSchedule : L = dyadicStages d e) (j : Fin L) :
    OneCopySubmatrix.copyBudget (ι:=Fin d) r (massAllowance r e L j)
      (stageAccuracy e L j) (δ/(L:ℝ)) ≤ (stageCopies r d L e δ : ℝ) :=
  (scheduled_stageBudget_le r d L e δ hr hrd hL he hδ hδ₁ hSchedule j).trans (Nat.le_ceil _)

/-- The stage rounding loss is absorbed using prefactor >= 1 and log >= log 2. -/
theorem totalCopies_le (r d L : ℕ) (e δ : ℝ)
    (hr : 1 ≤ r) (hrd : r ≤ d) (hL : 0 < L) (he : 0 < e) (he₁ : e ≤ 1)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    (totalCopies r d L e δ : ℝ) ≤
      (2304+1/Real.log 2) *
        ((r:ℝ)*Real.sqrt r*d*Real.sqrt d*(L:ℝ)^2/e) * commonLog d L δ := by
  have hp := prefactor_ge_one hr hrd hL he he₁
  have hl := commonLog_ge_log_two (lt_of_lt_of_le (by omega : 0<r) hrd) hL hδ hδ₁
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ commonLog d L δ := hlog₂.le.trans hl
  have hone : 1 ≤ (1/Real.log 2) * prefactor r d L e * commonLog d L δ := by
    have hm := mul_le_mul_of_nonneg_right hp hlog
    have hdv : 1 ≤ (prefactor r d L e * commonLog d L δ)/Real.log 2 :=
      (le_div_iff₀ hlog₂).mpr (by simpa only [one_mul] using hl.trans (by simpa only [one_mul] using hm))
    convert hdv using 1; ring
  have hN : (stageCopies r d L e δ : ℝ) ≤ realBudget r d L e δ + 1 :=
    (Nat.ceil_lt_add_one (realBudget_pos r d L e δ hr hrd hL he he₁ hδ hδ₁).le).le
  have hs : (stageCopies r d L e δ : ℝ) ≤
      (2304+1/Real.log 2) * prefactor r d L e * commonLog d L δ := by
    calc
      _ ≤ realBudget r d L e δ + 1 := hN
      _ ≤ realBudget r d L e δ + (1/Real.log 2)*prefactor r d L e*commonLog d L δ :=
        add_le_add_left hone _
      _ = _ := by unfold realBudget; ring
  have ht := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg L)
  calc
    _ = (stageCopies r d L e δ : ℝ)*(L:ℝ) := by simp only [totalCopies, Nat.cast_mul]
    _ ≤ ((2304+1/Real.log 2)*prefactor r d L e*commonLog d L δ)*(L:ℝ) := ht
    _ = _ := by unfold prefactor; ring

/-- Failure allocation stays positive at every positive finite stage count. -/
lemma stageFailure_pos {δ : ℝ} {L : ℕ} (hδ : 0 < δ) (hL : 0 < L) :
    0 < δ/(L:ℝ) := div_pos hδ (Nat.cast_pos.mpr hL)

lemma stageFailure_lt_half {δ : ℝ} {L : ℕ} (hδ : 0 < δ) (hδ₁ : δ < 1/2)
    (hL : 0 < L) : δ/(L:ℝ) < 1/2 := by
  have hL₁ : (1:ℝ) ≤ L := by exact_mod_cast hL
  exact (div_le_self hδ.le hL₁).trans_lt hδ₁

section ActualAmbient
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- No relabeling of the actual ambient matrices is required for the budget. -/
theorem actual_stageBudget_le_stageCopies (r L : ℕ) (e δ : ℝ)
    (hr : 1 ≤ r) (hrd : r ≤ Fintype.card ι) (hL : 0 < L) (he : 0 < e)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hSchedule : L = dyadicStages (Fintype.card ι) e)
    (j : Fin L) :
    OneCopySubmatrix.copyBudget (ι:=ι) r (massAllowance r e L j)
      (stageAccuracy e L j) (δ/(L:ℝ)) ≤
        (stageCopies r (Fintype.card ι) L e δ : ℝ) := by
  simpa only [OneCopySubmatrix.copyBudget, Fintype.card_fin] using
    scheduled_stageBudget_le_stageCopies r (Fintype.card ι) L e δ hr hrd hL he hδ hδ₁ hSchedule j

/-- Direct integer interface for the already proved fixed-budget actual routine. -/
theorem actual_copies_le_stageCopies (r L : ℕ) (e δ : ℝ)
    (hr : 1 ≤ r) (hrd : r ≤ Fintype.card ι) (hL : 0 < L) (he : 0 < e)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hSchedule : L = dyadicStages (Fintype.card ι) e)
    (j : Fin L) :
    OneCopySubmatrix.copies (ι:=ι) r (massAllowance r e L j)
      (stageAccuracy e L j) (δ/(L:ℝ)) ≤ stageCopies r (Fintype.card ι) L e δ :=
  Nat.ceil_le.mpr (actual_stageBudget_le_stageCopies r L e δ hr hrd hL he hδ hδ₁ hSchedule j)

/-- All numerical premises for a fixed-length actual stage call are native. -/
theorem actual_stage_parameters (r L : ℕ) (e δ : ℝ)
    (hr : 1 ≤ r) (hrd : r ≤ Fintype.card ι) (hL : 0 < L)
    (he : 0 < e) (he₁ : e ≤ 1) (hδ : 0 < δ) (hδ₁ : δ < 1/2)
    (hSchedule : L = dyadicStages (Fintype.card ι) e) (j : Fin L) :
    0 < stageCopies r (Fintype.card ι) L e δ ∧
      0 < stageAccuracy e L j ∧ 0 < δ/(L:ℝ) ∧ δ/(L:ℝ) < 1/2 ∧
      OneCopySubmatrix.copies (ι:=ι) r (massAllowance r e L j)
        (stageAccuracy e L j) (δ/(L:ℝ)) ≤ stageCopies r (Fintype.card ι) L e δ := by
  have hδle : δ ≤ 1 := by linarith
  exact ⟨stageCopies_pos r _ L e δ hr hrd hL he he₁ hδ hδle,
    accuracy_pos he hL j, stageFailure_pos hδ hL, stageFailure_lt_half hδ hδ₁ hL,
    actual_copies_le_stageCopies r L e δ hr hrd hL he hδ hδle hSchedule j⟩

end ActualAmbient

end Paper26.MultiscaleOneCopyCost

import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.MetricSpace.Lipschitz

open scoped BigOperators NNReal

namespace CalibrationDistance

noncomputable section

variable {α : Type*} [Fintype α]

/-- All predictions and comparator coordinates lie in the unit interval. -/
def Valid (p : α → ℝ) : Prop := ∀ t, p t ∈ Set.Icc (0 : ℝ) 1

def l1Dist (p r : α → ℝ) : ℝ := ∑ t, |p t - r t|

/-- The literal, unbinned perfect-calibration constraint (2.1). -/
def Calibrated (y r : α → ℝ) : Prop :=
  Valid r ∧ ∀ z : ℝ, (∑ t, if r t = z then y t - r t else 0) = 0

def calibratedCosts (p y : α → ℝ) : Set ℝ :=
  {c | ∃ r, Calibrated y r ∧ c = l1Dist p r}

/-- The unnormalized distance in (2.2), with the genuine calibrated set. -/
def calDist (p y : α → ℝ) : ℝ := sInf (calibratedCosts p y)

def bucket (u : α → ℝ) (z : ℝ) : Finset α :=
  Finset.univ.filter (fun t => u t = z)

def binResidual (u y : α → ℝ) (z : ℝ) : ℝ :=
  ∑ t ∈ bucket u z, (y t - u t)

/-- Cumulative unbinned calibration error (2.3). -/
def ece (u y : α → ℝ) : ℝ :=
  ∑ z ∈ Finset.univ.image u, |binResidual u y z|

lemma l1Dist_nonneg (p r : α → ℝ) : 0 ≤ l1Dist p r :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma l1Dist_comm (p r : α → ℝ) : l1Dist p r = l1Dist r p := by
  unfold l1Dist
  exact Finset.sum_congr rfl fun _ _ => abs_sub_comm _ _

lemma l1Dist_triangle (p u r : α → ℝ) : l1Dist p r ≤ l1Dist p u + l1Dist u r := by
  unfold l1Dist
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun t _ => abs_sub_le (p t) (u t) (r t)

lemma self_calibrated {y : α → ℝ} (hy : Valid y) : Calibrated y y := by
  refine ⟨hy, fun z => ?_⟩
  simp

lemma calibratedCosts_nonempty {p y : α → ℝ} (hy : Valid y) :
    (calibratedCosts p y).Nonempty :=
  ⟨l1Dist p y, y, self_calibrated hy, rfl⟩

lemma calibratedCosts_bddBelow (p y : α → ℝ) : BddBelow (calibratedCosts p y) := by
  refine ⟨0, ?_⟩
  rintro c ⟨r, _, rfl⟩
  exact l1Dist_nonneg p r

theorem calDist_nonneg {p y : α → ℝ} (hy : Valid y) : 0 ≤ calDist p y :=
  le_csInf (calibratedCosts_nonempty hy) (by
    rintro c ⟨r, _, rfl⟩
    exact l1Dist_nonneg p r)

theorem calDist_le_of_calibrated {p y r : α → ℝ} (hr : Calibrated y r) :
    calDist p y ≤ l1Dist p r :=
  csInf_le (calibratedCosts_bddBelow p y) ⟨r, hr, rfl⟩

lemma exists_comparator_lt {p y : α → ℝ} (hy : Valid y) {ε : ℝ} (hε : 0 < ε) :
    ∃ r, Calibrated y r ∧ l1Dist p r < calDist p y + ε := by
  obtain ⟨c, ⟨r, hr, rfl⟩, hc⟩ := Real.lt_sInf_add_pos (calibratedCosts_nonempty (p := p) hy) hε
  exact ⟨r, hr, hc⟩

theorem calDist_le_l1_add_calDist (p u : α → ℝ) {y : α → ℝ} (hy : Valid y) :
    calDist p y ≤ l1Dist p u + calDist u y := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r, hr, hc⟩ := exists_comparator_lt (p := u) hy hε
  have h := (calDist_le_of_calibrated (p := p) hr).trans (l1Dist_triangle p u r)
  linarith

/-- Lemma 6.2, (6.7), for any finite index type. -/
theorem proxy_comparison (p u : α → ℝ) {y : α → ℝ} (hy : Valid y) :
    |calDist p y - calDist u y| ≤ l1Dist p u := by
  apply abs_sub_le_iff.mpr
  constructor
  · linarith [calDist_le_l1_add_calDist p u hy]
  · have h := calDist_le_l1_add_calDist u p hy
    rw [l1Dist_comm u p] at h
    linarith

lemma l1Dist_le_card_mul_dist (p u : α → ℝ) :
    l1Dist p u ≤ (Fintype.card α : ℝ) * dist p u := by
  calc
    l1Dist p u ≤ ∑ _t : α, dist p u := by
      apply Finset.sum_le_sum
      intro t ht
      simpa only [Real.dist_eq] using dist_le_pi_dist p u t
    _ = (Fintype.card α : ℝ) * dist p u := by simp

/-- Calibration distance is continuous in the announced forecasts, including at bin collisions. -/
theorem lipschitzWith_calDist {y : α → ℝ} (hy : Valid y) :
    LipschitzWith (Fintype.card α : ℝ≥0) (fun p : α → ℝ => calDist p y) := by
  apply LipschitzWith.of_dist_le_mul
  intro p u
  simpa only [Real.dist_eq, NNReal.coe_natCast] using
    (proxy_comparison p u hy).trans (l1Dist_le_card_mul_dist p u)

theorem continuous_calDist {y : α → ℝ} (hy : Valid y) :
    Continuous (fun p : α → ℝ => calDist p y) :=
  (lipschitzWith_calDist hy).continuous

lemma sum_grouped (u : α → ℝ) (f : α → ℝ) :
    (∑ z ∈ Finset.univ.image u, ∑ t ∈ bucket u z, f t) = ∑ t, f t := by
  classical
  simpa [bucket] using (Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ.image u) (g := u) (f := f)
    (fun t ht => Finset.mem_image_of_mem u ht))

lemma calibrated_weighted_sum {y r : α → ℝ} (hr : Calibrated y r) (f : ℝ → ℝ) :
    (∑ t, f (r t) * (y t - r t)) = 0 := by
  classical
  rw [← sum_grouped r]
  apply Finset.sum_eq_zero
  intro z hz
  have heq : (∑ t ∈ bucket r z, f (r t) * (y t - r t)) =
      f z * (∑ t, if r t = z then y t - r t else 0) := by
    rw [Finset.mul_sum]
    simp only [bucket, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    split_ifs with h
    · rw [h]
    · simp
  rw [heq, hr.2 z, mul_zero]

lemma abs_outcome_sub_le_one {p y : α → ℝ} (hp : Valid p) (hy : Valid y) (t : α) :
    |y t - p t| ≤ 1 := by
  exact abs_le.mpr ⟨by linarith [(hp t).2, (hy t).1],
    by linarith [(hp t).1, (hy t).2]⟩

/-- Infimum transfer for a nonnegative multiplicative comparison. -/
lemma witness_inf_transfer {p y : α → ℝ} (hy : Valid y) {a C : ℝ} (ha : 0 ≤ a)
    (hC : 0 ≤ C) (h : ∀ r, Calibrated y r → a ≤ C * l1Dist p r) :
    a ≤ C * calDist p y := by
  rcases eq_or_lt_of_le hC with hzero | hpos
  · have hz : C = 0 := hzero.symm
    have hh := h y (self_calibrated hy)
    simpa [hz] using hh
  · have hh : a / C ≤ calDist p y := by
      apply le_csInf (calibratedCosts_nonempty hy)
      rintro c ⟨r, hr, rfl⟩
      exact (div_le_iff₀ hpos).mpr (by simpa [mul_comm] using h r hr)
    exact (div_le_iff₀ hpos).mp hh |>.trans_eq (mul_comm _ _)

/-- Lemma 4.1. Stating arbitrary admissible L and B also covers their least values. -/
theorem witness_comparison {p y : α → ℝ} (hp : Valid p) (hy : Valid y)
    (f : ℝ → ℝ) {L B : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hlip : ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
      |f a - f b| ≤ L * |a - b|)
    (hbound : ∀ a ∈ Set.Icc (0 : ℝ) 1, |f a| ≤ B) :
    |∑ t, f (p t) * (y t - p t)| ≤ (L + B) * calDist p y := by
  apply witness_inf_transfer hy (abs_nonneg _) (add_nonneg hL hB)
  intro r hr
  have hzero := calibrated_weighted_sum hr f
  have hdecomp : (∑ t, f (p t) * (y t - p t)) =
      ∑ t, ((f (p t) - f (r t)) * (y t - p t) + f (r t) * (r t - p t)) := by
    have heach (t : α) : f (p t) * (y t - p t) =
        ((f (p t) - f (r t)) * (y t - p t) + f (r t) * (r t - p t)) +
          f (r t) * (y t - r t) := by ring
    simp_rw [heach]
    rw [Finset.sum_add_distrib, hzero, add_zero]
  rw [hdecomp]
  unfold l1Dist
  rw [Finset.mul_sum]
  calc
    |∑ t, ((f (p t) - f (r t)) * (y t - p t) + f (r t) * (r t - p t))| ≤
        ∑ t, |(f (p t) - f (r t)) * (y t - p t) + f (r t) * (r t - p t)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t, (L + B) * |p t - r t| := by
      apply Finset.sum_le_sum
      intro t ht
      calc
        |(f (p t) - f (r t)) * (y t - p t) + f (r t) * (r t - p t)| ≤
            |f (p t) - f (r t)| * |y t - p t| + |f (r t)| * |r t - p t| := by
          simpa [abs_mul] using abs_add_le
            ((f (p t) - f (r t)) * (y t - p t)) (f (r t) * (r t - p t))
        _ ≤ (L * |p t - r t|) * 1 + B * |p t - r t| := by
          rw [abs_sub_comm (r t) (p t)]
          exact add_le_add
            (mul_le_mul (hlip _ (hp t) _ (hr.1 t)) (abs_outcome_sub_le_one hp hy t)
              (abs_nonneg _) (mul_nonneg hL (abs_nonneg _)))
            (mul_le_mul_of_nonneg_right (hbound _ (hr.1 t)) (abs_nonneg _))
        _ = (L + B) * |p t - r t| := by ring

theorem total_residual_le_calDist {p y : α → ℝ} (hp : Valid p) (hy : Valid y) :
    |∑ t, (y t - p t)| ≤ calDist p y := by
  simpa using witness_comparison hp hy (fun _ => 1) (L := 0) (B := 1)
    (by norm_num) (by norm_num) (by intros; simp) (by intros; norm_num)

theorem linear_witness_le_calDist {p y : α → ℝ} (hp : Valid p) (hy : Valid y) :
    (2 / 3 : ℝ) * |∑ t, (1 / 2 - p t) * (y t - p t)| ≤ calDist p y := by
  have h := witness_comparison hp hy (fun a => 1 / 2 - a) (L := 1) (B := 1 / 2)
    (by norm_num) (by norm_num)
    (by intro a ha b hb; simp only [one_mul, sub_sub_sub_cancel_left, abs_sub_comm]; exact le_rfl)
    (by intro a ha; exact abs_le.mpr ⟨by linarith [ha.2], by linarith [ha.1]⟩)
  linarith

/-- Restrictions of the smooth witnesses in (4.4) to the unit interval. -/
def SmoothWitness (f : ℝ → ℝ) : Prop :=
  (∀ a ∈ Set.Icc (0 : ℝ) 1, |f a| ≤ 1) ∧
  (∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1, |f a - f b| ≤ |a - b|)

def smoothCalibrationError (p y : α → ℝ) : ℝ :=
  sSup {c : ℝ | ∃ f : ℝ → ℝ, SmoothWitness f ∧ c = ∑ t, f (p t) * (y t - p t)}

/-- The standard smooth-calibration comparison (4.5), also a consequence of Lemma 4.1. -/
theorem smoothCalibrationError_le_two_calDist {p y : α → ℝ} (hp : Valid p) (hy : Valid y) :
    smoothCalibrationError p y ≤ 2 * calDist p y := by
  apply csSup_le
  · refine ⟨0, (fun _ => 0), ⟨?_, ?_⟩, ?_⟩
    · intro a ha; norm_num
    · intro a ha b hb; simpa using abs_nonneg (a - b)
    · simp
  · rintro c ⟨f, hf, rfl⟩
    have h := witness_comparison hp hy f (L := 1) (B := 1)
      (by norm_num) (by norm_num) (by simpa only [one_mul] using hf.2) hf.1
    norm_num at h
    exact (le_abs_self _).trans h

def binMean (u y : α → ℝ) (z : ℝ) : ℝ :=
  (∑ t ∈ bucket u z, y t) / (bucket u z).card

def meanComparator (u y : α → ℝ) (t : α) : ℝ := binMean u y (u t)

lemma bucket_nonempty {u : α → ℝ} {z : ℝ} (hz : z ∈ Finset.univ.image u) :
    (bucket u z).Nonempty := by
  classical
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨t, by simp [bucket]⟩

lemma binMean_valid {u y : α → ℝ} (hy : Valid y) {z : ℝ}
    (hz : z ∈ Finset.univ.image u) : binMean u y z ∈ Set.Icc (0 : ℝ) 1 := by
  have hc : (0 : ℝ) < (bucket u z).card := by
    exact_mod_cast Finset.card_pos.mpr (bucket_nonempty hz)
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun t ht => (hy t).1) (le_of_lt hc)
  · apply (div_le_one hc).mpr
    calc
      (∑ t ∈ bucket u z, y t) ≤ ∑ _t ∈ bucket u z, (1 : ℝ) :=
        Finset.sum_le_sum fun t ht => (hy t).2
      _ = (bucket u z).card := by simp

lemma binMean_residual_zero {u y : α → ℝ} {z : ℝ}
    (hz : z ∈ Finset.univ.image u) :
    (∑ t ∈ bucket u z, (y t - binMean u y z)) = 0 := by
  have hc : ((bucket u z).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (bucket_nonempty hz))
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  unfold binMean
  rw [mul_div_cancel₀ _ hc, sub_self]

theorem meanComparator_calibrated (u : α → ℝ) {y : α → ℝ} (hy : Valid y) :
    Calibrated y (meanComparator u y) := by
  classical
  refine ⟨fun t => binMean_valid hy (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩), ?_⟩
  intro z
  rw [← sum_grouped u]
  apply Finset.sum_eq_zero
  intro v hv
  have heq : (∑ t ∈ bucket u v,
      if meanComparator u y t = z then y t - meanComparator u y t else 0) =
      if binMean u y v = z then (∑ t ∈ bucket u v, (y t - binMean u y v)) else 0 := by
    calc
      _ = ∑ t ∈ bucket u v,
          (if binMean u y v = z then y t - binMean u y v else 0) := by
        apply Finset.sum_congr rfl
        intro t ht
        have ht' : u t = v := (Finset.mem_filter.mp ht).2
        simp only [meanComparator, ht']
      _ = _ := by split_ifs <;> simp
  rw [heq, binMean_residual_zero hv]
  split_ifs <;> rfl

lemma binResidual_eq_card_mul {u y : α → ℝ} {z : ℝ}
    (hz : z ∈ Finset.univ.image u) :
    binResidual u y z = (bucket u z).card * (binMean u y z - z) := by
  classical
  have hc : ((bucket u z).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (bucket_nonempty hz))
  have hsum : (∑ t ∈ bucket u z, u t) = (bucket u z).card * z := by
    calc
      (∑ t ∈ bucket u z, u t) = ∑ _t ∈ bucket u z, z := by
        apply Finset.sum_congr rfl
        intro t ht
        exact (Finset.mem_filter.mp ht).2
      _ = (bucket u z).card * z := by simp
  unfold binResidual
  rw [Finset.sum_sub_distrib, hsum]
  unfold binMean
  rw [mul_sub, mul_div_cancel₀ _ hc]

theorem l1Dist_meanComparator (u y : α → ℝ) :
    l1Dist u (meanComparator u y) = ece u y := by
  classical
  unfold l1Dist ece
  rw [← sum_grouped u]
  apply Finset.sum_congr rfl
  intro z hz
  calc
    (∑ t ∈ bucket u z, |u t - meanComparator u y t|) =
        ∑ _t ∈ bucket u z, |z - binMean u y z| := by
      apply Finset.sum_congr rfl
      intro t ht
      have ht' : u t = z := (Finset.mem_filter.mp ht).2
      simp only [meanComparator, ht']
    _ = (bucket u z).card * |z - binMean u y z| := by simp
    _ = |binResidual u y z| := by
      rw [binResidual_eq_card_mul hz, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ (bucket u z).card by exact Nat.cast_nonneg _), abs_sub_comm]

theorem calDist_le_ece (u : α → ℝ) {y : α → ℝ} (hy : Valid y) :
    calDist u y ≤ ece u y := by
  rw [← l1Dist_meanComparator]
  exact calDist_le_of_calibrated (meanComparator_calibrated u hy)

/-- Lemma 6.2, (6.8): the comparator merges equal empirical means correctly. -/
theorem calDist_le_l1_add_ece (p u : α → ℝ) {y : α → ℝ} (hy : Valid y) :
    calDist p y ≤ l1Dist p u + ece u y :=
  (calDist_le_l1_add_calDist p u hy).trans (add_le_add_left (calDist_le_ece u hy) _)

theorem calibrated_comp_equiv {β : Type*} [Fintype β] (e : α ≃ β)
    {y r : β → ℝ} (hr : Calibrated y r) : Calibrated (y ∘ e) (r ∘ e) := by
  refine ⟨fun t => hr.1 (e t), fun z => ?_⟩
  exact (e.sum_comp (fun t => if r t = z then y t - r t else 0)).trans (hr.2 z)

theorem l1Dist_equiv {β : Type*} [Fintype β] (e : α ≃ β) (p r : β → ℝ) :
    l1Dist (p ∘ e) (r ∘ e) = l1Dist p r :=
  e.sum_comp (fun t => |p t - r t|)

/-- Changing only the names of rounds preserves the calibrated optimization problem. -/
theorem calDist_equiv {β : Type*} [Fintype β] (e : α ≃ β) (p y : β → ℝ) :
    calDist (p ∘ e) (y ∘ e) = calDist p y := by
  unfold calDist
  congr 1
  ext c
  constructor
  · rintro ⟨r, hr, hc⟩
    refine ⟨r ∘ e.symm, ?_, ?_⟩
    · have h := calibrated_comp_equiv e.symm hr
      have heq : (y ∘ e) ∘ e.symm = y := by funext t; simp
      rw [heq] at h
      exact h
    · rw [hc]
      have heq : (p ∘ e) ∘ e.symm = p := by funext t; simp
      simpa only [heq] using (l1Dist_equiv e.symm (p ∘ e) r).symm
  · rintro ⟨r, hr, hc⟩
    exact ⟨r ∘ e, calibrated_comp_equiv e hr, hc.trans (l1Dist_equiv e p r).symm⟩

def paste {β : Type*} (label : α → β)
    (r : ∀ b, {t : α // label t = b} → ℝ) (t : α) : ℝ :=
  r (label t) ⟨t, rfl⟩

lemma paste_on_fiber {β : Type*} (label : α → β)
    (r : ∀ b, {t : α // label t = b} → ℝ) (b : β) (t : {t : α // label t = b}) :
    paste label r t.1 = r b t := by
  rcases t with ⟨t, ht⟩
  subst b
  rfl

theorem calibrated_paste {β : Type*} [Fintype β] [DecidableEq β]
    (label : α → β) {y : α → ℝ} (r : ∀ b, {t : α // label t = b} → ℝ)
    (hr : ∀ b, Calibrated (fun t : {t : α // label t = b} => y t.1) (r b)) :
    Calibrated y (paste label r) := by
  refine ⟨fun t => (hr (label t)).1 ⟨t, rfl⟩, fun z => ?_⟩
  rw [← Fintype.sum_fiberwise label]
  apply Finset.sum_eq_zero
  intro b hb
  simpa only [paste_on_fiber] using (hr b).2 z

theorem l1Dist_paste {β : Type*} [Fintype β] [DecidableEq β]
    (label : α → β) (p : α → ℝ) (r : ∀ b, {t : α // label t = b} → ℝ) :
    l1Dist p (paste label r) =
      ∑ b, l1Dist (fun t : {t : α // label t = b} => p t.1) (r b) := by
  unfold l1Dist
  rw [← Fintype.sum_fiberwise label]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro t ht
  rw [paste_on_fiber]

/-- Lemma 7.1, strengthened from consecutive nonempty blocks to any finite partition. -/
theorem calDist_partition_le {β : Type*} [Fintype β] [DecidableEq β]
    (label : α → β) (p : α → ℝ) {y : α → ℝ} (hy : Valid y) :
    calDist p y ≤ ∑ b,
      calDist (fun t : {t : α // label t = b} => p t.1)
        (fun t : {t : α // label t = b} => y t.1) := by
  classical
  apply le_of_forall_pos_le_add
  intro ε hε
  have hden : (0 : ℝ) < Fintype.card β + 1 := by
    exact_mod_cast Nat.succ_pos (Fintype.card β)
  have hη : 0 < ε / (Fintype.card β + 1 : ℝ) := div_pos hε hden
  have hex (b : β) := exists_comparator_lt
    (p := fun t : {t : α // label t = b} => p t.1)
    (y := fun t : {t : α // label t = b} => y t.1)
    (fun t => hy t.1) hη
  choose r hr hcost using hex
  calc
    calDist p y ≤ l1Dist p (paste label r) :=
      calDist_le_of_calibrated (calibrated_paste label r hr)
    _ = ∑ b, l1Dist (fun t : {t : α // label t = b} => p t.1) (r b) :=
      l1Dist_paste label p r
    _ ≤ ∑ b, (calDist (fun t : {t : α // label t = b} => p t.1)
        (fun t : {t : α // label t = b} => y t.1) + ε / (Fintype.card β + 1 : ℝ)) :=
      Finset.sum_le_sum (fun b hb => le_of_lt (hcost b))
    _ = (∑ b, calDist (fun t : {t : α // label t = b} => p t.1)
        (fun t : {t : α // label t = b} => y t.1)) +
        Fintype.card β * (ε / (Fintype.card β + 1 : ℝ)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (∑ b, calDist (fun t : {t : α // label t = b} => p t.1)
        (fun t : {t : α // label t = b} => y t.1)) + ε := by
      apply add_le_add_left
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      nlinarith

end

end CalibrationDistance

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto

/-! Finite upper-tail CVaR, with tail mass (rather than confidence level) α.
The risk envelope is a probability law dominated by P/α. -/
namespace Paper36.CVaR

open scoped BigOperators
open Set

structure Law (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ i, 0 ≤ mass i
  total : ∑ i, mass i = 1

variable {Ω : Type*} [Fintype Ω]

noncomputable def expect (w : Ω → ℝ) (X : Ω → ℝ) : ℝ := ∑ i, w i * X i

def Envelope (P : Law Ω) (α : ℝ) (w : Ω → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ (∀ i, w i ≤ P.mass i / α) ∧ ∑ i, w i = 1

noncomputable def value (P : Law Ω) (α : ℝ) (X : Ω → ℝ) : ℝ :=
  sSup ((fun w => expect w X) '' {w | Envelope P α w})

theorem self_envelope (P : Law Ω) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1) :
    Envelope P α P.mass := by
  refine ⟨P.nonneg, fun i => ?_, P.total⟩
  apply (le_div_iff₀ ha).2
  nlinarith [P.nonneg i]

theorem compact_envelope (P : Law Ω) (α : ℝ) :
    IsCompact {w | Envelope P α w} := by
  have heq : {w | Envelope P α w} =
      Icc (fun _ => 0) (fun i => P.mass i / α) ∩ {w | (∑ i, w i) = 1} := by
    ext w
    simp only [Envelope, mem_setOf_eq, mem_inter_iff, mem_Icc, Pi.le_def]
    tauto
  rw [heq]
  exact isCompact_Icc.inter_right (isClosed_eq (by fun_prop) continuous_const)

theorem exists_maximizer (P : Law Ω) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    (X : Ω → ℝ) :
    ∃ w, Envelope P α w ∧ ∀ v, Envelope P α v → expect v X ≤ expect w X := by
  obtain ⟨w, hw, hm⟩ := (compact_envelope P α).exists_isMaxOn (f := fun w => expect w X)
    ⟨P.mass, self_envelope P ha ha1⟩ (by unfold expect; fun_prop)
  exact ⟨w, hw, hm⟩

theorem bddAbove_values (P : Law Ω) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    (X : Ω → ℝ) : BddAbove ((fun w => expect w X) '' {w | Envelope P α w}) := by
  obtain ⟨w, hw, hm⟩ := exists_maximizer P ha ha1 X
  refine ⟨expect w X, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  exact hm v hv

theorem expect_le_value (P : Law Ω) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    {w : Ω → ℝ} (hw : Envelope P α w) (X : Ω → ℝ) :
    expect w X ≤ value P α X :=
  le_csSup (bddAbove_values P ha ha1 X) ⟨w, hw, rfl⟩

theorem exists_optimizer (P : Law Ω) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    (X : Ω → ℝ) : ∃ w, Envelope P α w ∧ value P α X = expect w X := by
  obtain ⟨w, hw, hm⟩ := exists_maximizer P ha ha1 X
  refine ⟨w, hw, le_antisymm ?_ (expect_le_value P ha ha1 hw X)⟩
  apply csSup_le (s := (fun w => expect w X) '' {w | Envelope P α w})
    ⟨expect P.mass X, P.mass, self_envelope P ha ha1, rfl⟩
  rintro _ ⟨v, hv, rfl⟩
  exact hm v hv

theorem value_le (P : Law Ω) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    {X : Ω → ℝ} {b : ℝ} (h : ∀ w, Envelope P α w → expect w X ≤ b) :
    value P α X ≤ b := by
  obtain ⟨w, hw, hval⟩ := exists_optimizer P ha ha1 X
  rw [hval]
  exact h w hw

theorem expect_mono {w : Ω → ℝ} (hw : ∀ i, 0 ≤ w i)
    {X Y : Ω → ℝ} (h : ∀ i, X i ≤ Y i) : expect w X ≤ expect w Y := by
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hw i)

theorem value_mono (P : Law Ω) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    {X Y : Ω → ℝ} (h : ∀ i, X i ≤ Y i) : value P α X ≤ value P α Y := by
  apply value_le P ha ha1
  intro w hw
  exact (expect_mono hw.1 h).trans (expect_le_value P ha ha1 hw Y)

theorem expect_const {w : Ω → ℝ} (hw : ∑ i, w i = 1) (c : ℝ) :
    expect w (fun _ => c) = c := by
  simp only [expect, ← Finset.sum_mul, hw, one_mul]

theorem value_const (P : Law Ω) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1) (c : ℝ) :
    value P α (fun _ => c) = c := by
  obtain ⟨w, hw, hv⟩ := exists_optimizer P ha ha1 (fun _ => c)
  rw [hv, expect_const hw.2.2]

theorem value_bounds (P : Law Ω) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    {X : Ω → ℝ} {l u : ℝ} (hlo : ∀ i, l ≤ X i) (hhi : ∀ i, X i ≤ u) :
    l ≤ value P α X ∧ value P α X ≤ u := by
  constructor
  · simpa only [value_const P ha ha1] using value_mono P ha ha1 hlo
  · simpa only [value_const P ha ha1] using value_mono P ha ha1 hhi

theorem expect_add_const {w : Ω → ℝ} (hw : ∑ i, w i = 1)
    (X : Ω → ℝ) (c : ℝ) : expect w (fun i => X i + c) = expect w X + c := by
  simp only [expect, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul]

theorem value_add_const (P : Law Ω) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    (X : Ω → ℝ) (c : ℝ) : value P α (fun i => X i + c) = value P α X + c := by
  apply le_antisymm
  · apply value_le P ha ha1
    intro w hw
    rw [expect_add_const hw.2.2]
    exact add_le_add_right (expect_le_value P ha ha1 hw X) c
  · obtain ⟨w, hw, hv⟩ := exists_optimizer P ha ha1 X
    rw [hv, ← expect_add_const hw.2.2]
    exact expect_le_value P ha ha1 hw _

/-- The continuation operator is 1-Lipschitz in supremum norm (C.1, second claim). -/
theorem value_lipschitz (P : Law Ω) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    {X Y : Ω → ℝ} {d : ℝ} (h : ∀ i, |X i - Y i| ≤ d) :
    |value P α X - value P α Y| ≤ d := by
  apply abs_le.mpr
  constructor
  · have hm : value P α Y ≤ value P α (fun i => X i + d) :=
      value_mono P ha ha1 fun i => by have := (abs_le.mp (h i)).1; linarith
    rw [value_add_const P ha ha1] at hm
    linarith
  · have hm : value P α X ≤ value P α (fun i => Y i + d) :=
      value_mono P ha ha1 fun i => by have := (abs_le.mp (h i)).2; linarith
    rw [value_add_const P ha ha1] at hm
    linarith

/-- Rockafellar--Uryasev finite-law threshold objective. -/
noncomputable def primal (P : Law Ω) (α : ℝ) (X : Ω → ℝ) (z : ℝ) : ℝ :=
  z + ∑ i, (P.mass i / α) * max (X i - z) 0

theorem expect_sub_const {w : Ω → ℝ} (hw : ∑ i, w i = 1)
    (X : Ω → ℝ) (z : ℝ) : expect w X = z + ∑ i, w i * (X i - z) := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw, one_mul, expect]
  ring

/-- Weak primal--dual inequality, for every real threshold. -/
theorem value_le_primal (P : Law Ω) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    (X : Ω → ℝ) (z : ℝ) : value P α X ≤ primal P α X z := by
  apply value_le P ha ha1
  intro w hw
  rw [expect_sub_const hw.2.2]
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro i _
  exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (hw.1 i)).trans
    (mul_le_mul_of_nonneg_right (hw.2.1 i) (le_max_right _ _))

private theorem optimal_saturated (P : Law Ω) {α : ℝ} {w X : Ω → ℝ}
    (hw : Envelope P α w)
    (hm : ∀ v, Envelope P α v → expect v X ≤ expect w X)
    {a b : Ω} (hab : X b < X a) (hb : 0 < w b) : w a = P.mass a / α := by
  classical
  by_contra heq
  have ha : w a < P.mass a / α := lt_of_le_of_ne (hw.2.1 a) heq
  have hne : a ≠ b := by intro h; subst a; exact (lt_irrefl _ hab)
  let δ := min (P.mass a / α - w a) (w b)
  have hd : 0 < δ := lt_min (sub_pos.mpr ha) hb
  have hda : δ ≤ P.mass a / α - w a := min_le_left _ _
  have hdb : δ ≤ w b := min_le_right _ _
  let v : Ω → ℝ := fun i => w i + (if i = a then δ else 0) -
    (if i = b then δ else 0)
  have hv : Envelope P α v := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      by_cases hia : i = a
      · subst i; simp [v, hne]; linarith [hw.1 a]
      · by_cases hib : i = b
        · subst i; simp [v, Ne.symm hne]; linarith
        · simpa [v, hia, hib] using hw.1 i
    · intro i
      by_cases hia : i = a
      · subst i; simp [v, hne]; linarith
      · by_cases hib : i = b
        · subst i; simp [v, Ne.symm hne]; linarith [hw.2.1 b]
        · simpa [v, hia, hib] using hw.2.1 i
    · simp only [v, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      simp [hw.2.2]
  have hev : expect v X = expect w X + δ * X a - δ * X b := by
    simp only [expect, v, sub_mul, add_mul, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, ite_mul, zero_mul]
    simp
  have hh := hm v hv
  rw [hev] at hh
  have : 0 < δ * (X a - X b) := mul_pos hd (sub_pos.mpr hab)
  nlinarith

/-- An optimal finite envelope supplies an optimizing real threshold. -/
theorem exists_threshold (P : Law Ω) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    (X : Ω → ℝ) : ∃ z, value P α X = primal P α X z := by
  classical
  obtain ⟨w, hw, hm⟩ := exists_maximizer P ha ha1 X
  have hpositive : ∃ i, 0 < w i := by
    by_contra h
    push_neg at h
    have hh : (∑ i, w i) ≤ 0 := Finset.sum_nonpos fun i _ => h i
    rw [hw.2.2] at hh
    norm_num at hh
  let s := Finset.univ.filter fun i => 0 < w i
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hpositive
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  obtain ⟨b, hb, hbmin⟩ := s.exists_min_image X hs
  have hwb : 0 < w b := (Finset.mem_filter.mp hb).2
  have hterm : ∀ i, w i * (X i - X b) =
      (P.mass i / α) * max (X i - X b) 0 := by
    intro i
    rcases lt_trichotomy (X i) (X b) with hi | hi | hi
    · have hw0 : w i = 0 := by
        apply le_antisymm _ (hw.1 i)
        by_contra h
        have hwi : 0 < w i := lt_of_not_ge h
        have hh := hbmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwi⟩)
        linarith
      rw [hw0, zero_mul, max_eq_right (le_of_lt (sub_neg.mpr hi)), mul_zero]
    · simp [hi]
    · rw [optimal_saturated P hw hm hi hwb,
        max_eq_left (le_of_lt (sub_pos.mpr hi))]
  have hmax : value P α X = expect w X := by
    apply le_antisymm
    · exact value_le P ha ha1 hm
    · exact expect_le_value P ha ha1 hw X
  refine ⟨X b, ?_⟩
  rw [hmax, expect_sub_const hw.2.2]
  exact congrArg (X b + ·) (Finset.sum_congr rfl fun i _ => hterm i)

/-- The defining primal infimum and the finite risk envelope have equal values. -/
theorem value_eq_primal_inf (P : Law Ω) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    (X : Ω → ℝ) : value P α X = sInf (Set.range (primal P α X)) := by
  obtain ⟨z, hz⟩ := exists_threshold P ha ha1 X
  apply le_antisymm
  · exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨t, rfl⟩; exact value_le_primal P ha ha1 X t)
  · exact csInf_le ⟨value P α X, by rintro _ ⟨t, rfl⟩; exact value_le_primal P ha ha1 X t⟩
      ⟨z, hz.symm⟩

/-- The density form used in equation (2.2) of the paper. -/
def DensityEnvelope (P : Law Ω) (α : ℝ) (ξ : Ω → ℝ) : Prop :=
  (∀ i, 0 ≤ ξ i) ∧ (∀ i, ξ i ≤ 1/α) ∧ expect P.mass ξ = 1

theorem density_envelope (P : Law Ω) {α : ℝ} {ξ : Ω → ℝ}
    (hξ : DensityEnvelope P α ξ) : Envelope P α (fun i => P.mass i*ξ i) := by
  refine ⟨fun i => mul_nonneg (P.nonneg i) (hξ.1 i), ?_, hξ.2.2⟩
  intro i
  have hh := mul_le_mul_of_nonneg_left (hξ.2.1 i) (P.nonneg i)
  simpa only [mul_one_div] using hh

theorem envelope_has_density (P : Law Ω) {α : ℝ} (ha : 0 < α)
    {w : Ω → ℝ} (hw : Envelope P α w) :
    ∃ ξ, DensityEnvelope P α ξ ∧ ∀ i, P.mass i*ξ i = w i := by
  classical
  let ξ : Ω → ℝ := fun i => if P.mass i = 0 then 0 else w i / P.mass i
  have he : ∀ i, P.mass i*ξ i = w i := by
    intro i
    by_cases hi : P.mass i = 0
    · have hw0 : w i = 0 := le_antisymm (by simpa [hi] using hw.2.1 i) (hw.1 i)
      simp [ξ, hi, hw0]
    · simp only [ξ, hi, if_false]
      field_simp
  refine ⟨ξ, ⟨?_, ?_, ?_⟩, he⟩
  · intro i
    by_cases hi : P.mass i = 0
    · simp [ξ, hi]
    · exact by simpa [ξ, hi] using div_nonneg (hw.1 i) (P.nonneg i)
  · intro i
    by_cases hi : P.mass i = 0
    · simp only [ξ, hi, if_true]
      exact div_nonneg (by norm_num) ha.le
    · have hp : 0 < P.mass i := lt_of_le_of_ne (P.nonneg i) (Ne.symm hi)
      simp only [ξ, hi, if_false]
      apply (div_le_iff₀ hp).2
      have hh := hw.2.1 i
      simpa only [one_div_mul_eq_div] using hh
  · unfold expect
    simp only [he]
    exact hw.2.2

/-- Equation (2.2)'s density envelope and our distorted-mass envelope are identical. -/
theorem value_eq_density_sup (P : Law Ω) {α : ℝ} (ha : 0 < α) (X : Ω → ℝ) :
    value P α X = sSup ((fun ξ => expect P.mass (fun i => ξ i*X i)) ''
      {ξ | DensityEnvelope P α ξ}) := by
  unfold value
  congr 1
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨ξ, hξ, he⟩ := envelope_has_density P ha hw
    refine ⟨ξ, hξ, ?_⟩
    unfold expect
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc, he]
  · rintro ⟨ξ, hξ, rfl⟩
    refine ⟨fun i => P.mass i*ξ i, density_envelope P hξ, ?_⟩
    unfold expect
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Finite tail mass; the non-strict version differs only at finitely many thresholds. -/
noncomputable def tail (w X : Ω → ℝ) (t : ℝ) : ℝ :=
  ∑ i, if t ≤ X i then w i else 0

theorem tail_nonneg {w X : Ω → ℝ} (hw : ∀ i, 0 ≤ w i) (t : ℝ) : 0 ≤ tail w X t := by
  exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp_all

theorem tail_le_total {w X : Ω → ℝ} (hw : ∀ i, 0 ≤ w i) (t : ℝ) :
    tail w X t ≤ ∑ i, w i := by
  exact Finset.sum_le_sum fun i _ => by split_ifs <;> simp_all

/-- One finite optimizer simultaneously maximizes every upper level set. -/
theorem exists_tail_optimizer (P : Law Ω) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    (X : Ω → ℝ) : ∃ w, Envelope P α w ∧ value P α X = expect w X ∧
      ∀ t, tail w X t = min 1 (tail P.mass X t / α) := by
  classical
  obtain ⟨w, hw, hm⟩ := exists_maximizer P ha ha1 X
  have hp : ∃ i, 0 < w i := by
    by_contra h
    push_neg at h
    have hh : (∑ i, w i) ≤ 0 := Finset.sum_nonpos fun i _ => h i
    rw [hw.2.2] at hh
    norm_num at hh
  let s := Finset.univ.filter fun i => 0 < w i
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hp
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  obtain ⟨b, hb, hbmin⟩ := s.exists_min_image X hs
  have hwb : 0 < w b := (Finset.mem_filter.mp hb).2
  have hz : ∀ i, X i < X b → w i = 0 := by
    intro i hi
    apply le_antisymm _ (hw.1 i)
    by_contra h
    have hh := hbmin i (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, lt_of_not_ge h⟩)
    linarith
  have hmax : value P α X = expect w X := by
    exact le_antisymm (value_le P ha ha1 hm) (expect_le_value P ha ha1 hw X)
  refine ⟨w, hw, hmax, ?_⟩
  intro t
  have hdom : tail w X t ≤ tail P.mass X t / α := by
    unfold tail
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : t ≤ X i
    · simpa [hi] using hw.2.1 i
    · simp [hi]
  by_cases ht : t ≤ X b
  · have he : tail w X t = 1 := by
      rw [← hw.2.2]
      unfold tail
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : t ≤ X i
      · simp [hi]
      · simp [hi, hz i (by linarith)]
    rw [he] at hdom ⊢
    exact (min_eq_left hdom).symm
  · have he : tail w X t = tail P.mass X t / α := by
      unfold tail
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : t ≤ X i
      · simp only [hi, if_true]
        exact optimal_saturated P hw hm (by linarith) hwb
      · simp [hi]
    have hle := tail_le_total (X := X) hw.1 t
    rw [hw.2.2, he] at hle
    rw [he]
    exact (min_eq_right hle).symm

/-- Exact CVaR of a finite indicator loss, including Bernoulli losses. -/
theorem value_indicator (P : Law Ω) {α d : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    (hd : 0 ≤ d) (e : Ω → Prop) [DecidablePred e] :
    value P α (fun i => if e i then d else 0) =
      d * min ((∑ i, if e i then P.mass i else 0)/α) 1 := by
  classical
  rcases hd.eq_or_lt with hd | hd
  · subst d
    simp [value_const P ha ha1]
  · let X : Ω → ℝ := fun i => if e i then d else 0
    obtain ⟨w, hw, hv, ht⟩ := exists_tail_optimizer P ha ha1 X
    have htail : ∀ v : Ω → ℝ, tail v X d = ∑ i, if e i then v i else 0 := by
      intro v
      unfold tail X
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : e i <;> simp [hi, not_le.mpr hd]
    have he : expect w X = d * tail w X d := by
      rw [htail, Finset.mul_sum]
      unfold expect X
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : e i <;> simp [hi, mul_comm]
    change value P α X = _
    rw [hv, he, ht, htail, min_comm]

/-- Squared Hellinger distance uses exactly the one-half convention of (5.1). -/
noncomputable def hellingerSq (P Q : Law Ω) : ℝ :=
  (∑ i, (Real.sqrt (P.mass i) - Real.sqrt (Q.mass i)) ^ 2) / 2

noncomputable def hellinger (P Q : Law Ω) : ℝ := Real.sqrt (hellingerSq P Q)

theorem hellingerSq_nonneg (P Q : Law Ω) : 0 ≤ hellingerSq P Q := by
  exact div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (by norm_num)

/-- Hellinger contraction to an event, in square-root probability coordinates. -/
theorem event_sqrt_difference (P Q : Law Ω) (E : Finset Ω) :
    |Real.sqrt (∑ i ∈ E, P.mass i) - Real.sqrt (∑ i ∈ E, Q.mass i)| ≤
      Real.sqrt 2 * hellinger P Q := by
  let p := ∑ i ∈ E, P.mass i
  let q := ∑ i ∈ E, Q.mass i
  let c := ∑ i ∈ E, Real.sqrt (P.mass i) * Real.sqrt (Q.mass i)
  have hp : 0 ≤ p := Finset.sum_nonneg fun i _ => P.nonneg i
  have hq : 0 ≤ q := Finset.sum_nonneg fun i _ => Q.nonneg i
  have hc : 0 ≤ c := Finset.sum_nonneg fun i _ =>
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq E
    (fun i => Real.sqrt (P.mass i)) (fun i => Real.sqrt (Q.mass i))
  simp only [Real.sq_sqrt (P.nonneg _), Real.sq_sqrt (Q.nonneg _)] at hcs
  have hcp : c ≤ Real.sqrt p * Real.sqrt q := by
    have hpq : (Real.sqrt p * Real.sqrt q)^2 = p*q := by
      rw [mul_pow, Real.sq_sqrt hp, Real.sq_sqrt hq]
    nlinarith [mul_nonneg (Real.sqrt_nonneg p) (Real.sqrt_nonneg q)]
  have he : (∑ i ∈ E, (Real.sqrt (P.mass i)-Real.sqrt (Q.mass i))^2) = p+q-2*c := by
    simp only [sub_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Real.sq_sqrt (P.nonneg _), Real.sq_sqrt (Q.nonneg _)]
    have hc2 : (∑ i ∈ E, 2*Real.sqrt (P.mass i)*Real.sqrt (Q.mass i)) = 2*c := by
      unfold c
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hc2]
    unfold p q
    ring
  have hsub : (∑ i ∈ E, (Real.sqrt (P.mass i)-Real.sqrt (Q.mass i))^2) ≤
      ∑ i, (Real.sqrt (P.mass i)-Real.sqrt (Q.mass i))^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E) (fun i _ _ => sq_nonneg _)
  have hsum : (∑ i, (Real.sqrt (P.mass i)-Real.sqrt (Q.mass i))^2) =
      2*hellingerSq P Q := by unfold hellingerSq; ring
  rw [he, hsum] at hsub
  have hroots : (Real.sqrt p-Real.sqrt q)^2 ≤ 2*hellingerSq P Q := by
    nlinarith [Real.sq_sqrt hp, Real.sq_sqrt hq]
  have hd : (Real.sqrt 2 * hellinger P Q)^2 = 2*hellingerSq P Q := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    unfold hellinger
    rw [Real.sq_sqrt (hellingerSq_nonneg P Q)]
  have hn : 0 ≤ Real.sqrt 2 * hellinger P Q := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  change |Real.sqrt p-Real.sqrt q| ≤ _
  nlinarith [sq_abs (Real.sqrt p-Real.sqrt q), abs_nonneg (Real.sqrt p-Real.sqrt q)]

private theorem cap_sqrt_lipschitz {p q α d : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (ha : 0 ≤ α) (hd : 0 ≤ d) (h : |Real.sqrt p-Real.sqrt q| ≤ d) :
    |min α p-min α q| ≤ 2*Real.sqrt α*d := by
  wlog hpq : p ≤ q generalizing p q
  · rw [abs_sub_comm]
    exact this hq hp (by simpa only [abs_sub_comm] using h) (le_of_not_ge hpq)
  have hroot : Real.sqrt p ≤ Real.sqrt q := Real.sqrt_le_sqrt hpq
  have hdiff : Real.sqrt q-Real.sqrt p ≤ d := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hroot)] at h
    exact h
  by_cases hαp : α ≤ p
  · rw [min_eq_left hαp, min_eq_left (hαp.trans hpq), sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hd
  · have hpα : p ≤ α := le_of_not_ge hαp
    rw [min_eq_right hpα]
    by_cases hqα : q ≤ α
    · rw [min_eq_right hqα, abs_of_nonpos (sub_nonpos.mpr hpq)]
      have hqa := Real.sqrt_le_sqrt hqα
      have hpa := Real.sqrt_le_sqrt hpα
      nlinarith [Real.sq_sqrt hp, Real.sq_sqrt hq, Real.sqrt_nonneg p,
        Real.sqrt_nonneg q, Real.sqrt_nonneg α,
        mul_nonneg (sub_nonneg.mpr hroot) (sub_nonneg.mpr hqa),
        mul_nonneg (sub_nonneg.mpr hroot) (sub_nonneg.mpr hpa)]
    · have hαq : α ≤ q := le_of_not_ge hqα
      rw [min_eq_left hαq, abs_of_nonpos (sub_nonpos.mpr hpα)]
      have hpa := Real.sqrt_le_sqrt hpα
      have haq := Real.sqrt_le_sqrt hαq
      have hadd : Real.sqrt α-Real.sqrt p ≤ d := by linarith
      nlinarith [Real.sq_sqrt hp, Real.sq_sqrt ha, Real.sqrt_nonneg p,
        Real.sqrt_nonneg α,
        mul_nonneg (sub_nonneg.mpr hpa) (sub_nonneg.mpr hpa)]

/-- Support-size-independent capped-event bound used in the proof of Lemma 5.1. -/
theorem capped_event_difference (P Q : Law Ω) {α : ℝ} (ha : 0 ≤ α) (E : Finset Ω) :
    |min α (∑ i ∈ E, P.mass i)-min α (∑ i ∈ E, Q.mass i)| ≤
      2*Real.sqrt α*(Real.sqrt 2*hellinger P Q) :=
  cap_sqrt_lipschitz (Finset.sum_nonneg fun i _ => P.nonneg i)
    (Finset.sum_nonneg fun i _ => Q.nonneg i) ha
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (event_sqrt_difference P Q E)

private theorem tail_indicator_integrable (w X : Ω → ℝ) (i : Ω) (l u : ℝ) :
    IntervalIntegrable (fun t => if t ≤ X i then w i else 0)
      MeasureTheory.volume l u := by
  have h : IntervalIntegrable (fun _ : ℝ => w i) MeasureTheory.volume l u :=
    intervalIntegrable_const
  exact ⟨h.1.indicator measurableSet_Iic, h.2.indicator measurableSet_Iic⟩

theorem tail_intervalIntegrable (w X : Ω → ℝ) (l u : ℝ) :
    IntervalIntegrable (tail w X) MeasureTheory.volume l u := by
  classical
  unfold tail
  simpa only [Finset.sum_fn] using
    (IntervalIntegrable.sum (f := fun i t => if t ≤ X i then w i else 0)
      Finset.univ fun i _ => tail_indicator_integrable w X i l u)

set_option maxHeartbeats 800000 in
/-- Finite layer-cake formula, proved by integrating the finitely many indicators. -/
theorem integral_tail (w X : Ω → ℝ) {l u : ℝ}
    (hl : ∀ i, l ≤ X i) (hu : ∀ i, X i ≤ u) :
    (∫ t in l..u, tail w X t) = expect w X-l*(∑ i, w i) := by
  classical
  unfold tail
  rw [intervalIntegral.integral_finset_sum
    (s := Finset.univ) (f := fun i t => if t ≤ X i then w i else 0)
    (fun i _ => tail_indicator_integrable w X i l u)]
  have hi : ∀ i, (∫ t in l..u, if t ≤ X i then w i else 0) = (X i-l)*w i := by
    intro i
    change (∫ t in l..u, Set.indicator {t : ℝ | t ≤ X i} (fun _ => w i) t) = _
    rw [intervalIntegral.integral_indicator ⟨hl i, hu i⟩,
      intervalIntegral.integral_const, smul_eq_mul]
  simp only [hi, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, expect]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem min_one_div {α : ℝ} (ha : 0 < α) (p : ℝ) :
    min 1 (p/α) = min α p / α := by
  by_cases hp : p ≤ α
  · rw [min_eq_right ((div_le_iff₀ ha).2 (by simpa using hp)), min_eq_right hp]
  · have hp' : α ≤ p := le_of_not_ge hp
    rw [min_eq_left ((le_div_iff₀ ha).2 (by simpa using hp')),
      min_eq_left hp', div_self (ne_of_gt ha)]

/-- Lemma 5.1: support-size-independent CVaR--Hellinger stability for any loss interval. -/
theorem value_hellinger (P Q : Law Ω) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    {X : Ω → ℝ} {l u : ℝ} (hlu : l ≤ u)
    (hl : ∀ i, l ≤ X i) (hu : ∀ i, X i ≤ u) :
    |value P α X-value Q α X| ≤
      (2*Real.sqrt 2*(u-l)/Real.sqrt α)*hellinger P Q := by
  classical
  obtain ⟨wP, hwP, hvP, htP⟩ := exists_tail_optimizer P ha ha1 X
  obtain ⟨wQ, hwQ, hvQ, htQ⟩ := exists_tail_optimizer Q ha ha1 X
  have he : value P α X-value Q α X =
      ∫ t in l..u, (tail wP X t-tail wQ X t) := by
    rw [intervalIntegral.integral_sub (tail_intervalIntegrable _ _ _ _)
      (tail_intervalIntegrable _ _ _ _), integral_tail wP X hl hu,
      integral_tail wQ X hl hu, hwP.2.2, hwQ.2.2, ← hvP, ← hvQ]
    ring
  let C := 2*Real.sqrt α*(Real.sqrt 2*hellinger P Q)/α
  have hb : ∀ t, |tail wP X t-tail wQ X t| ≤ C := by
    intro t
    rw [htP, htQ, min_one_div ha, min_one_div ha, ← sub_div,
      abs_div, abs_of_pos ha]
    let E := Finset.univ.filter fun i => t ≤ X i
    have hp : tail P.mass X t = ∑ i ∈ E, P.mass i := by
      simp [E, tail, Finset.sum_filter]
    have hq : tail Q.mass X t = ∑ i ∈ E, Q.mass i := by
      simp [E, tail, Finset.sum_filter]
    rw [hp, hq]
    exact div_le_div_of_nonneg_right (capped_event_difference P Q ha.le E) ha.le
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := l) (b := u) (f := fun t => tail wP X t-tail wQ X t)
    (C := C) (fun t _ => by simpa only [Real.norm_eq_abs] using hb t)
  rw [Real.norm_eq_abs, ← he, abs_of_nonneg (sub_nonneg.mpr hlu)] at hh
  have heq : C*(u-l) = (2*Real.sqrt 2*(u-l)/Real.sqrt α)*hellinger P Q := by
    have hs : Real.sqrt α ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
    have hs2 := Real.sq_sqrt ha.le
    have hrat : Real.sqrt α / α = 1 / Real.sqrt α := by
      calc
        Real.sqrt α / α = Real.sqrt α / (Real.sqrt α)^2 := by rw [hs2]
        _ = 1 / Real.sqrt α := by field_simp
    calc
      C*(u-l) = (2*Real.sqrt 2*(u-l)*hellinger P Q)*(Real.sqrt α/α) := by
        dsimp [C]
        ring
      _ = (2*Real.sqrt 2*(u-l)/Real.sqrt α)*hellinger P Q := by
        rw [hrat]
        ring
  rw [heq] at hh
  exact hh

/-- Total variation uses the paper's one-half L1 convention. -/
noncomputable def tv (P Q : Law Ω) : ℝ := (∑ i, |P.mass i - Q.mass i|) / 2

theorem tv_nonneg (P Q : Law Ω) : 0 ≤ tv P Q := by
  exact div_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) (by norm_num)

/-- Bounded-span expectation perturbation, with the sharp total-variation coefficient. -/
theorem expect_difference_le_tv (P Q : Law Ω) {X : Ω → ℝ} {l u : ℝ}
    (hl : ∀ i, l ≤ X i) (hu : ∀ i, X i ≤ u) :
    |expect P.mass X - expect Q.mass X| ≤ (u - l) * tv P Q := by
  have hsum : (∑ i, (P.mass i - Q.mass i)) = 0 := by
    rw [Finset.sum_sub_distrib, P.total, Q.total, sub_self]
  have heq : expect P.mass X - expect Q.mass X =
      ∑ i, (P.mass i - Q.mass i) * (X i - (l + u) / 2) := by
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      P.total, Q.total, one_mul, expect]
    ring
  rw [heq]
  calc
    |∑ i, (P.mass i - Q.mass i) * (X i - (l + u) / 2)| ≤
        ∑ i, |(P.mass i - Q.mass i) * (X i - (l + u) / 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |P.mass i - Q.mass i| * ((u - l) / 2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact abs_le.mpr ⟨by linarith [hl i], by linarith [hu i]⟩
    _ = (u - l) * tv P Q := by
      rw [← Finset.sum_mul]
      unfold tv
      ring

private theorem max_span {x l u z : ℝ} (hl : l ≤ x) (hu : x ≤ u) :
    max (l-z) 0 ≤ max (x-z) 0 ∧ max (x-z) 0 ≤ max (u-z) 0 :=
  ⟨max_le_max_right _ (sub_le_sub_right hl _),
   max_le_max_right _ (sub_le_sub_right hu _)⟩

private theorem max_span_width {l u z : ℝ} (h : l ≤ u) :
    max (u-z) 0 - max (l-z) 0 ≤ u-l := by
  by_cases hzl : z ≤ l
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    linarith
  · by_cases hzu : z ≤ u
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
      linarith
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]
      linarith

theorem primal_eq (P : Law Ω) (α : ℝ) (X : Ω → ℝ) (z : ℝ) :
    primal P α X z = z + expect P.mass (fun i => max (X i-z) 0) / α := by
  unfold primal expect
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]

/-- Uniform threshold perturbations transfer to CVaR without any assumed stability axiom. -/
theorem value_difference_of_primal (P Q : Law Ω) {α : ℝ}
    (ha : 0 < α) (ha1 : α ≤ 1) (X : Ω → ℝ) {d : ℝ}
    (h : ∀ z, |primal P α X z - primal Q α X z| ≤ d) :
    |value P α X - value Q α X| ≤ d := by
  obtain ⟨zP, hzP⟩ := exists_threshold P ha ha1 X
  obtain ⟨zQ, hzQ⟩ := exists_threshold Q ha ha1 X
  apply abs_le.mpr
  constructor
  · have hh := (abs_le.mp (h zP)).1
    have hhQ := value_le_primal Q ha ha1 X zP
    linarith
  · have hh := (abs_le.mp (h zQ)).2
    have hhP := value_le_primal P ha ha1 X zQ
    linarith

/-- Finite-law CVaR is Lipschitz in TV with the loss span divided by tail mass. -/
theorem value_tv (P Q : Law Ω) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    {X : Ω → ℝ} {l u : ℝ} (hlu : l ≤ u)
    (hl : ∀ i, l ≤ X i) (hu : ∀ i, X i ≤ u) :
    |value P α X - value Q α X| ≤ ((u-l)/α) * tv P Q := by
  apply value_difference_of_primal P Q ha ha1 X
  intro z
  rw [primal_eq, primal_eq]
  have heq : z + expect P.mass (fun i => max (X i-z) 0) / α -
      (z + expect Q.mass (fun i => max (X i-z) 0) / α) =
      (expect P.mass (fun i => max (X i-z) 0) -
       expect Q.mass (fun i => max (X i-z) 0)) / α := by ring
  rw [heq, abs_div, abs_of_pos ha]
  apply (div_le_iff₀ ha).2
  have hh := expect_difference_le_tv P Q
    (fun i => (max_span (z := z) (hl i) (hu i)).1)
    (fun i => (max_span (z := z) (hl i) (hu i)).2)
  have hh' := mul_le_mul_of_nonneg_right (max_span_width (z := z) hlu) (tv_nonneg P Q)
  have hα : ((u-l)/α) * tv P Q * α = (u-l)*tv P Q := by field_simp
  rw [hα]
  exact hh.trans hh'

section Mixtures
variable {A : Type*} [Fintype A]

/-- Joint action--successor law: policy randomization is inside CVaR. -/
def joint (π : Law A) (P : A → Law Ω) : Law (A × Ω) where
  mass x := π.mass x.1 * (P x.1).mass x.2
  nonneg x := mul_nonneg (π.nonneg _) ((P _).nonneg _)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, Law.total, mul_one]

theorem expect_joint (π : Law A) (P : A → Law Ω) (X : A × Ω → ℝ) :
    expect (joint π P).mass X = ∑ a, π.mass a * expect (P a).mass (fun i => X (a,i)) := by
  simp only [expect, joint, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

/-- Local perturbation (Lemma C.1): current action cost does not enlarge the transition span. -/
theorem value_joint_tv (π : Law A) (P Q : A → Law Ω) {α R : ℝ}
    (ha : 0 < α) (ha1 : α ≤ 1) (hR : 0 ≤ R) (c : A → ℝ) (f : Ω → ℝ)
    (hf0 : ∀ i, 0 ≤ f i) (hfR : ∀ i, f i ≤ R) :
    |value (joint π P) α (fun x => c x.1 + f x.2) -
     value (joint π Q) α (fun x => c x.1 + f x.2)| ≤
      (R/α) * ∑ a, π.mass a * tv (P a) (Q a) := by
  apply value_difference_of_primal (joint π P) (joint π Q) ha ha1
  intro z
  rw [primal_eq, primal_eq, expect_joint, expect_joint]
  let Y : A → Ω → ℝ := fun a i => max (c a + f i-z) 0
  have hr : ∀ a, |expect (P a).mass (Y a) - expect (Q a).mass (Y a)| ≤
      R * tv (P a) (Q a) := by
    intro a
    have hh := expect_difference_le_tv (P a) (Q a)
      (fun i => (max_span (z := z) (show c a ≤ c a + f i by linarith [hf0 i])
        (show c a + f i ≤ c a + R by linarith [hfR i])).1)
      (fun i => (max_span (z := z) (show c a ≤ c a + f i by linarith [hf0 i])
        (show c a + f i ≤ c a + R by linarith [hfR i])).2)
    have hh' := mul_le_mul_of_nonneg_right
      (max_span_width (l := c a) (u := c a+R) (z := z) (by linarith))
      (tv_nonneg (P a) (Q a))
    have he : c a + R - c a = R := by ring
    rw [he] at hh'
    exact hh.trans hh'
  have heq : z + (∑ a, π.mass a * expect (P a).mass (Y a)) / α -
      (z + (∑ a, π.mass a * expect (Q a).mass (Y a)) / α) =
      (∑ a, π.mass a * (expect (P a).mass (Y a)-expect (Q a).mass (Y a))) / α := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  change |z + (∑ a, π.mass a * expect (P a).mass (Y a)) / α -
      (z + (∑ a, π.mass a * expect (Q a).mass (Y a)) / α)| ≤ _
  rw [heq, abs_div, abs_of_pos ha]
  apply (div_le_iff₀ ha).2
  have hh : |∑ a, π.mass a * (expect (P a).mass (Y a)-expect (Q a).mass (Y a))| ≤
      R * ∑ a, π.mass a * tv (P a) (Q a) := by
    calc
      _ ≤ ∑ a, |π.mass a * (expect (P a).mass (Y a)-expect (Q a).mass (Y a))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, π.mass a * (R * tv (P a) (Q a)) := by
        apply Finset.sum_le_sum
        intro a _
        rw [abs_mul, abs_of_nonneg (π.nonneg a)]
        exact mul_le_mul_of_nonneg_left (hr a) (π.nonneg a)
      _ = R * ∑ a, π.mass a * tv (P a) (Q a) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
  have he : (R/α) * (∑ a, π.mass a * tv (P a) (Q a)) * α =
      R * ∑ a, π.mass a * tv (P a) (Q a) := by field_simp
  rw [he]
  exact hh

theorem tv_self (P : Law Ω) : tv P P = 0 := by simp [tv]

theorem hellingerSq_self (P : Law Ω) : hellingerSq P P = 0 := by simp [hellingerSq]

/-- Hellinger distance of the joint law splits exactly over the shared action law. -/
theorem hellingerSq_joint (π : Law A) (P Q : A → Law Ω) :
    hellingerSq (joint π P) (joint π Q) = ∑ a, π.mass a * hellingerSq (P a) (Q a) := by
  have hi : ∀ a i,
      (Real.sqrt (π.mass a*(P a).mass i)-Real.sqrt (π.mass a*(Q a).mass i))^2 =
      π.mass a*(Real.sqrt ((P a).mass i)-Real.sqrt ((Q a).mass i))^2 := by
    intro a i
    rw [Real.sqrt_mul (π.nonneg _), Real.sqrt_mul (π.nonneg _),
      ← mul_sub, mul_pow, Real.sq_sqrt (π.nonneg _)]
  unfold hellingerSq
  simp only [joint, Fintype.sum_prod_type, hi, ← Finset.mul_sum,
    Finset.sum_div, mul_div_assoc]

theorem hellinger_joint (π : Law A) (P Q : A → Law Ω) :
    hellinger (joint π P) (joint π Q) =
      Real.sqrt (∑ a, π.mass a * hellingerSq (P a) (Q a)) := by
  unfold hellinger
  rw [hellingerSq_joint]

/-- Lemma 5.2, with R=H-h. Arbitrary I splits low-count TV rows and Hellinger rows. -/
theorem value_joint_hybrid [DecidableEq A] (π : Law A) (P Q : A → Law Ω) {α R : ℝ}
    (ha : 0 < α) (ha1 : α ≤ 1) (hR : 0 ≤ R)
    (c : A → ℝ) (f : Ω → ℝ) (hc0 : ∀ a, 0 ≤ c a) (hc1 : ∀ a, c a ≤ 1)
    (hf0 : ∀ i, 0 ≤ f i) (hfR : ∀ i, f i ≤ R) (I : Finset A) :
    |value (joint π P) α (fun x => c x.1+f x.2)-
      value (joint π Q) α (fun x => c x.1+f x.2)| ≤
      (R/α)*(∑ a, if a ∈ I then 0 else π.mass a*tv (P a) (Q a)) +
      (2*Real.sqrt 2*(R+1)/Real.sqrt α)*
        Real.sqrt (∑ a, if a ∈ I then π.mass a*hellingerSq (P a) (Q a) else 0) := by
  classical
  let M : A → Law Ω := fun a => if a ∈ I then P a else Q a
  let X : A × Ω → ℝ := fun x => c x.1+f x.2
  have htv := value_joint_tv π P M ha ha1 hR c f hf0 hfR
  have hhe := value_hellinger (joint π M) (joint π Q) ha ha1
    (l := 0) (u := R+1) (by linarith) (X := X)
    (fun x => add_nonneg (hc0 _) (hf0 _))
    (fun x => by dsimp [X]; linarith [hc1 x.1, hfR x.2])
  have hlow : (∑ a, π.mass a*tv (P a) (M a)) =
      ∑ a, if a ∈ I then 0 else π.mass a*tv (P a) (Q a) := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases hi : a ∈ I <;> simp [M, hi, tv_self]
  have hhigh : hellinger (joint π M) (joint π Q) =
      Real.sqrt (∑ a, if a ∈ I then π.mass a*hellingerSq (P a) (Q a) else 0) := by
    rw [hellinger_joint]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    by_cases hi : a ∈ I <;> simp [M, hi, hellingerSq_self]
  rw [hlow] at htv
  rw [hhigh] at hhe
  have hh := abs_sub_le (value (joint π P) α X) (value (joint π M) α X)
    (value (joint π Q) α X)
  exact hh.trans (add_le_add htv (by simpa using hhe))

/-- Mixing optimizing row envelopes is feasible for the joint law. -/
theorem envelope_joint (π : Law A) (P : A → Law Ω) {α : ℝ}
    (w : A → Ω → ℝ) (hw : ∀ a, Envelope (P a) α (w a)) :
    Envelope (joint π P) α (fun x => π.mass x.1 * w x.1 x.2) := by
  refine ⟨fun x => mul_nonneg (π.nonneg _) ((hw _).1 _), ?_, ?_⟩
  · intro x
    change π.mass x.1 * w x.1 x.2 ≤ (π.mass x.1 * (P x.1).mass x.2) / α
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ((hw _).2.1 _) (π.nonneg _)
  · simp only [Fintype.sum_prod_type, ← Finset.mul_sum, fun a => (hw a).2.2, mul_one]
    exact π.total

/-- CVaR is concave in the probability law, including action mixing (Lemma 4.1 ingredient). -/
theorem value_joint_ge (π : Law A) (P : A → Law Ω) {α : ℝ}
    (ha : 0 < α) (ha1 : α ≤ 1) (X : A × Ω → ℝ) :
    (∑ a, π.mass a * value (P a) α (fun s => X (a, s))) ≤
      value (joint π P) α X := by
  classical
  choose w hw hval using fun a => exists_optimizer (P a) ha ha1 (fun s => X (a,s))
  have hh := expect_le_value (joint π P) ha ha1 (envelope_joint π P w hw) X
  convert hh using 1
  simp only [hval, expect, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

/-- Any common lower bound on pure-action CVaR also bounds mixed-action CVaR. -/
theorem value_joint_ge_of_forall (π : Law A) (P : A → Law Ω) {α : ℝ}
    (ha : 0 < α) (ha1 : α ≤ 1) (X : A × Ω → ℝ) {l : ℝ}
    (hl : ∀ a, l ≤ value (P a) α (fun s => X (a,s))) :
    l ≤ value (joint π P) α X := by
  have hh : (∑ a, π.mass a * l) ≤
      ∑ a, π.mass a * value (P a) α (fun s => X (a,s)) :=
    Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hl a) (π.nonneg a)
  rw [← Finset.sum_mul, π.total, one_mul] at hh
  exact hh.trans (value_joint_ge π P ha ha1 X)

end Mixtures
end Paper36.CVaR

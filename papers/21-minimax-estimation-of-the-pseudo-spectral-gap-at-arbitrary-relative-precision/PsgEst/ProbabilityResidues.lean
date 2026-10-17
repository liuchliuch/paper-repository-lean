import PsgEst.ProbabilityShift
import PsgEst.AppendixScalar

/-!
# Finite residue partitions and their actual Markov laws

The division/remainder bijection partitions an observation window into its
residues. The shifted thinning law is proved from finite path marginalization,
so no residue distribution or partition identity is taken as an assumption.
-/

open Matrix BigOperators Real Finset Classical
namespace PsgEst

/-- Number of indices `r + b*t` among `0,...,m-1`. Empty residues have length zero. -/
def residueLength (m b : ℕ) (r : Fin b) : ℕ :=
  if r.val < m then (m - 1 - r.val) / b + 1 else 0

/-- Exact membership criterion for a residue index. -/
lemma residue_index_iff {m b : ℕ} (hb : 0 < b) (r : Fin b) (t : ℕ) :
    r.val + b * t < m ↔ t < residueLength m b r := by
  unfold residueLength
  by_cases hr : r.val < m
  · rw [if_pos hr, Nat.lt_succ_iff, Nat.le_div_iff_mul_le hb, Nat.mul_comm t b]
    omega
  · rw [if_neg hr]
    omega

/-- Embed a residue position into the original observation window. -/
def residueIndex {m b : ℕ} (hb : 0 < b) (r : Fin b)
    (t : Fin (residueLength m b r)) : Fin m :=
  ⟨r.val + b * t.val, (residue_index_iff hb r t.val).mpr t.isLt⟩

/-- Division and remainder give a genuine finite bijection, including empty residues. -/
noncomputable def residueEquiv {m b : ℕ} (hb : 0 < b) :
    (Σ r : Fin b, Fin (residueLength m b r)) ≃ Fin m :=
  Equiv.ofBijective (fun z => residueIndex hb z.1 z.2) (by
    constructor
    · rintro ⟨r, t⟩ ⟨s, u⟩ h
      have hv : r.val + b * t.val = s.val + b * u.val := congrArg Fin.val h
      have hrs : r = s := by
        apply Fin.ext
        have hh := congrArg (fun x : ℕ => x % b) hv
        simpa only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt,
          Nat.mod_eq_of_lt s.isLt] using hh
      cases hrs
      have htu : t = u := by
        apply Fin.ext
        have hh := congrArg (fun x : ℕ => x / b) hv
        simpa only [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt r.isLt,
          Nat.zero_add] using hh
      cases htu
      rfl
    · intro i
      let r : Fin b := ⟨i.val % b, Nat.mod_lt i.val hb⟩
      have hi : r.val + b * (i.val / b) < m := by
        dsimp [r]
        rw [Nat.mod_add_div]
        exact i.isLt
      refine ⟨⟨r, ⟨i.val / b, (residue_index_iff hb r _).mp hi⟩⟩, ?_⟩
      apply Fin.ext
      exact Nat.mod_add_div i.val b)

/-- The lengths of all residues sum exactly to the number of observations. -/
theorem sum_residueLength {m b : ℕ} (hb : 0 < b) :
    ∑ r : Fin b, residueLength m b r = m := by
  have hh := Fintype.card_congr (residueEquiv (m := m) hb)
  simpa only [Fintype.card_sigma, Fintype.card_fin] using hh

/-- Reorder any finite sum by its actual residue positions. -/
theorem sum_residueIndex {m b : ℕ} {A : Type*} [AddCommMonoid A]
    (hb : 0 < b) (f : Fin m → A) :
    (∑ r : Fin b, ∑ t : Fin (residueLength m b r), f (residueIndex hb r t)) =
      ∑ i : Fin m, f i := by
  have hh := Equiv.sum_comp (residueEquiv (m := m) hb) f
  change (∑ z : (Σ r : Fin b, Fin (residueLength m b r)),
    f (residueIndex hb z.1 z.2)) = _ at hh
  rw [Fintype.sum_sigma] at hh
  exact hh

/-- Every residue has at least the quotient `m/b` observations. -/
theorem residueLength_ge_div {m b : ℕ} (hb : 0 < b) (r : Fin b) :
    m / b ≤ residueLength m b r := by
  let q := m / b
  by_cases hq : q = 0
  · change q ≤ residueLength m b r
    rw [hq]
    exact Nat.zero_le _
  · have hqpos : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq
    have hprod : b * q ≤ m := Nat.mul_div_le m b
    have he : b * (q - 1) + b = b * q := by
      calc
        _ = b * ((q - 1) + 1) := by ring
        _ = _ := by rw [Nat.sub_add_cancel hqpos]
    have hi : r.val + b * (q - 1) < m := by have hr := r.isLt; omega
    have hh := (residue_index_iff hb r (q - 1)).mp hi
    change q ≤ residueLength m b r
    omega

/-- Nonempty windows of at least one full block have no empty residue. -/
theorem residueLength_pos {m b : ℕ} (_hb : 0 < b) (hm : b ≤ m) (r : Fin b) :
    0 < residueLength m b r := by
  unfold residueLength
  rw [if_pos (lt_of_lt_of_le r.isLt hm)]
  exact Nat.succ_pos _

/-- The lower bound on residue sizes used in Appendix A. -/
theorem residueLength_ge_half_ratio {m b : ℕ} (hb : 0 < b)
    (hm : 2 * b ≤ m) (r : Fin b) :
    (m : ℝ) / (2 * (b : ℝ)) ≤ (residueLength m b r : ℝ) := by
  let q := m / b
  have hq : 2 ≤ q := (Nat.le_div_iff_mul_le hb).mpr hm
  have hdiv : b * q + m % b = m := Nat.div_add_mod m b
  have hmod := Nat.mod_lt m hb
  have hbq : b ≤ b * q := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left b (by omega : 1 ≤ q)
  have hnat : m ≤ 2 * b * q := by nlinarith
  have hreal : (m : ℝ) ≤ 2 * (b : ℝ) * (q : ℝ) := by exact_mod_cast hnat
  have hlen : (q : ℝ) ≤ (residueLength m b r : ℝ) := by
    exact_mod_cast residueLength_ge_div hb r
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (b : ℝ))).mpr
  nlinarith

/-- The observations in a single residue, in their original order. -/
def residueSequence {d m b : ℕ} (hb : 0 < b) (r : Fin b)
    (Y : Fin m → Fin d) : Fin (residueLength m b r) → Fin d :=
  fun t => Y (residueIndex hb r t)

/-- Visit count on an arbitrary observation window, including an empty one. -/
noncomputable def observationVisitCount {d m : ℕ} (i : Fin d) (Y : Fin m → Fin d) : ℝ :=
  ∑ t, stateIndicator i (Y t)

/-- Visit count in a residue. -/
noncomputable def residueVisitCount {d m b : ℕ} (hb : 0 < b) (r : Fin b)
    (i : Fin d) (Y : Fin m → Fin d) : ℝ :=
  observationVisitCount i (residueSequence hb r Y)

/-- The full count is exactly the sum of the counts of the disjoint residues. -/
theorem observationVisitCount_eq_sum_residues {d m b : ℕ} (hb : 0 < b)
    (i : Fin d) (Y : Fin m → Fin d) :
    observationVisitCount i Y = ∑ r : Fin b, residueVisitCount hb r i Y := by
  exact (sum_residueIndex hb (fun t => stateIndicator i (Y t))).symm

/-- A nonempty residue as a conventional path of `ell-1` transitions. -/
def residuePath {d m b : ℕ} (hb : 0 < b) (r : Fin b)
    (hpos : 0 < residueLength m b r) (Y : Fin m → Fin d) :
    Fin (residueLength m b r - 1 + 1) → Fin d :=
  fun t => residueSequence hb r Y ⟨t.val, by have ht := t.isLt; omega⟩

/-- The pure residue count agrees with the actual Appendix scalar count. -/
theorem residueVisitCount_eq_appendixVisitCount {d m b : ℕ} (hb : 0 < b)
    (r : Fin b) (hpos : 0 < residueLength m b r) (i : Fin d) (Y : Fin m → Fin d) :
    residueVisitCount hb r i Y = appendixVisitCount i (residuePath hb r hpos Y) := by
  let he : residueLength m b r - 1 + 1 = residueLength m b r := by omega
  have hh := Equiv.sum_comp (finCongr he)
    (fun t : Fin (residueLength m b r) => stateIndicator i (residueSequence hb r Y t))
  exact hh.symm

/-- Appendix's full count is exactly the sum of its actual scalar residue counts. -/
theorem observationVisitCount_eq_sum_appendix {d m b : ℕ} (hb : 0 < b)
    (hm : b ≤ m) (i : Fin d) (Y : Fin m → Fin d) :
    observationVisitCount i Y = ∑ r : Fin b,
      appendixVisitCount i (residuePath hb r (residueLength_pos hb hm r) Y) := by
  rw [observationVisitCount_eq_sum_residues hb]
  apply Finset.sum_congr rfl
  intro r _
  exact residueVisitCount_eq_appendixVisitCount hb r _ i Y

/-- A window of `m` observations starting at time `s` in a longer trajectory. -/
def trajectoryWindow {d n : ℕ} (s m : ℕ) (h : s + m ≤ n + 1)
    (X : Fin (n + 1) → Fin d) : Fin m → Fin d :=
  fun t => X ⟨s + t.val, by have ht := t.isLt; omega⟩

lemma residue_last_le {m b n : ℕ} (hb : 0 < b) (r : Fin b)
    (hpos : 0 < residueLength m b r) (s : ℕ) (h : s + m ≤ n + 1) :
    s + r.val + b * (residueLength m b r - 1) ≤ n := by
  have hi := (residue_index_iff (m := m) hb r (residueLength m b r - 1)).mpr (by omega)
  omega

/-- The residue sequence in any observation window is exactly an offset-thinned path. -/
lemma residuePath_eq_offsetSkip {d m b n : ℕ} (hb : 0 < b) (r : Fin b)
    (hpos : 0 < residueLength m b r) (s : ℕ) (h : s + m ≤ n + 1)
    (X : Fin (n + 1) → Fin d) :
    residuePath hb r hpos (trajectoryWindow s m h X) =
      offsetSkip (s + r.val) b (residueLength m b r - 1) (residue_last_le hb r hpos s h) X := by
  funext t
  unfold residuePath residueSequence residueIndex trajectoryWindow offsetSkip
    offsetBlockSkip blockSkip pathShift pathPrefix
  congr 1
  apply Fin.ext
  exact (Nat.add_assoc s r.val (b * t.val)).symm

/-- Genuine Markov path law of an actual residue: the transition is `P^b` and
its start law is `mu P^(s+r)`. -/
theorem residuePath_sum {d m b n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (mu : Fin d → ℝ) (hrow : ∀ i, ∑ j, P i j = 1)
    (hb : 0 < b) (r : Fin b) (hpos : 0 < residueLength m b r)
    (s : ℕ) (h : s + m ≤ n + 1)
    (f : (Fin (residueLength m b r - 1 + 1) → Fin d) → ℝ) :
    (∑ X : Fin (n + 1) → Fin d, pathProb P mu X *
      f (residuePath hb r hpos (trajectoryWindow s m h X))) =
      ∑ Y, pathProb (P ^ b) (shiftedLaw P mu (s + r.val)) Y * f Y := by
  simp_rw [residuePath_eq_offsetSkip hb r hpos s h]
  exact offsetSkip_sum P mu hrow (s + r.val) b (residueLength m b r - 1)
    (residue_last_le hb r hpos s h) f

/-- Event-probability form of the actual residue path distribution. -/
theorem residuePath_eventProb {d m b n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (mu : Fin d → ℝ) (hrow : ∀ i, ∑ j, P i j = 1)
    (hb : 0 < b) (r : Fin b) (hpos : 0 < residueLength m b r)
    (s : ℕ) (h : s + m ≤ n + 1)
    (E : (Fin (residueLength m b r - 1 + 1) → Fin d) → Prop) :
    eventProb P mu (fun X : Fin (n + 1) → Fin d =>
      E (residuePath hb r hpos (trajectoryWindow s m h X))) =
      eventProb (P ^ b) (shiftedLaw P mu (s + r.val)) E := by
  classical
  have hh := residuePath_sum P mu hrow hb r hpos s h (fun Y => if E Y then 1 else 0)
  simpa only [eventProb, pathMeasure, Finset.sum_filter, mul_ite, mul_one, mul_zero] using hh

end PsgEst

import PsgEst.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Order.Ring.GeomSum
set_option maxHeartbeats 800000

/-!
# The hard pair `P_s` for the minimax lower bound (Section 4)

A rare state coupled to a well-mixed reservoir.  Varying the exchange rate `s`
changes the gap without changing the stationary law.

State `0` is the rare state (paper's state `1`).
-/

open Matrix BigOperators Real Polynomial

namespace PsgEst

variable {d : ℕ}

/-- Stationary law of the hard family: `π_0 = p`, remaining mass uniform. -/
noncomputable def hardMu (d : ℕ) (p : ℝ) : Fin d → ℝ := fun i =>
  if i.val = 0 then p else (1 - p) / ((d - 1 : ℕ) : ℝ)

/-- Transition matrix `P_s` of the hard family (0-indexed: state 0 is the rare state). -/
noncomputable def hardP (d : ℕ) (p s : ℝ) : Matrix (Fin d) (Fin d) ℝ := fun i j =>
  if d = 0 then 0
  else if i.val = 0 ∧ j.val = 0 then 1 - (1 - p) * s
  else if i.val = 0 then (1 - p) * s / ((d - 1 : ℕ) : ℝ)
  else if j.val = 0 then p * s
  else (1 - p * s) / ((d - 1 : ℕ) : ℝ)

/-! ### Numerical facts about the parameter range -/

lemma cast_d_sub_one {d : ℕ} (hd : 2 ≤ d) : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
  rw [Nat.cast_sub (by omega : 1 ≤ d)]
  simp

lemma cast_d_sub_one_pos {d : ℕ} (hd : 2 ≤ d) : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by
  rw [cast_d_sub_one hd]
  have h : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  linarith

lemma cast_d_sub_one_ne {d : ℕ} (hd : 2 ≤ d) : ((d - 1 : ℕ) : ℝ) ≠ 0 :=
  ne_of_gt (cast_d_sub_one_pos hd)

lemma p_lt_one {d : ℕ} {p : ℝ} (hd : 2 ≤ d) (hp : 0 < p) (hp' : p ≤ 1 / (d : ℝ)) : p < 1 := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have : (1 / (d : ℝ)) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  nlinarith

lemma one_sub_p_pos {d : ℕ} {p : ℝ} (hd : 2 ≤ d) (hp : 0 < p) (hp' : p ≤ 1 / (d : ℝ)) : 0 < 1 - p := by
  linarith [p_lt_one hd hp hp']

lemma ps_lt_one {d : ℕ} {p s : ℝ} (hd : 2 ≤ d) (hp : 0 < p) (hp' : p ≤ 1 / (d : ℝ))
    (hs : 0 < s) (hs' : s < 1) : p * s < 1 := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have h1 : p * s ≤ (1 / (d : ℝ)) * 1 :=
    mul_le_mul hp' (le_of_lt hs') (le_of_lt hs) (le_of_lt (div_pos one_pos hdpos))
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h2 : (1 / (d : ℝ)) ≤ 1 / 2 := by
    rw [div_le_iff₀ hdpos]
    nlinarith
  nlinarith

lemma one_sub_ps_pos {d : ℕ} {p s : ℝ} (hd : 2 ≤ d) (hp : 0 < p) (hp' : p ≤ 1 / (d : ℝ))
    (hs : 0 < s) (hs' : s < 1) : 0 < 1 - p * s :=
  sub_pos.mpr (ps_lt_one hd hp hp' hs hs')

lemma one_sub_1mps_nonneg {d : ℕ} {p s : ℝ} (hd : 2 ≤ d) (hp : 0 < p) (hp' : p ≤ 1 / (d : ℝ))
    (hs : 0 < s) (hs' : s < 1) : 0 ≤ 1 - (1 - p) * s := by
  have h : (1 - p) * s < 1 := by
    have h1 : 1 - p < 1 := sub_lt_self _ hp
    nlinarith [one_sub_p_pos hd hp hp']
  linarith

lemma card_val_zero (d : ℕ) [NeZero d] :
    (Finset.univ.filter (fun i : Fin d => i.val = 0)).card = 1 := by
  have h : (Finset.univ.filter (fun i : Fin d => i.val = 0)) = {⟨0, Nat.pos_of_neZero d⟩} := by
    ext i
    constructor
    · intro hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_singleton]
      exact Fin.ext hi
    · intro hi
      simp only [Finset.mem_singleton] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hi]
  rw [h, Finset.card_singleton]

lemma card_val_ne_zero (d : ℕ) [NeZero d] :
    (Finset.univ.filter (fun i : Fin d => i.val ≠ 0)).card = d - 1 := by
  have h1 : (Finset.univ.filter (fun i : Fin d => i.val = 0)).card = 1 := card_val_zero d
  have h2 : (Finset.univ.filter (fun i : Fin d => i.val ≠ 0))
      = (Finset.univ.filter (fun i : Fin d => i.val = 0))ᶜ := by
    ext i; simp
  rw [h2, Finset.card_compl, h1, Fintype.card_fin]

lemma sum_ite_val_zero {α : Type*} [AddCommMonoid α] (d : ℕ) [NeZero d] (a : α) :
    ∑ i : Fin d, (if i.val = 0 then a else 0) = a := by
  have h : ∑ i : Fin d, (if i.val = 0 then a else 0)
      = ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val = 0), a := by
    have key := Finset.sum_filter (s := (Finset.univ : Finset (Fin d)))
      (p := fun i : Fin d => i.val = 0) (f := fun _ => a)
    refine key.symm.trans ?_
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val = 0
    · simp [hi]
    · simp [hi]
  rw [h, Finset.sum_const, card_val_zero d]
  simp

lemma sum_ite_val_ne_zero {α : Type*} [AddCommMonoid α] (d : ℕ) [NeZero d] (f : Fin d → α) :
    ∑ i : Fin d, (if i.val = 0 then 0 else f i)
      = ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val ≠ 0), f i := by
  have h : ∑ i : Fin d, (if i.val = 0 then 0 else f i)
      = ∑ i : Fin d, (if i.val ≠ 0 then f i else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val = 0
    · simp [hi]
    · simp [hi]
  rw [h]
  have key := Finset.sum_filter (s := (Finset.univ : Finset (Fin d)))
    (p := fun i : Fin d => i.val ≠ 0) (f := f)
  exact key.symm

lemma sum_split {α : Type*} [AddCommMonoid α] (d : ℕ) [NeZero d] (f : Fin d → α) (a : α) :
    ∑ i, (if i.val = 0 then a else f i)
      = a + ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val ≠ 0), f i := by
  have hadd : ∀ i : Fin d,
      (if i.val = 0 then a else f i) = (if i.val = 0 then a else 0) + (if i.val = 0 then 0 else f i) := by
    intro i
    by_cases hi : i.val = 0
    · simp [hi]
    · simp [hi]
  conv_lhs => simp only [hadd]
  rw [Finset.sum_add_distrib, sum_ite_val_zero, sum_ite_val_ne_zero]

/-! ### Entrywise facts -/

theorem hardP_nonneg {d : ℕ} (hd : 2 ≤ d) (p s : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / d) (hs : 0 < s) (hs' : s < 1) :
    ∀ i j, 0 ≤ hardP d p s i j := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := cast_d_sub_one_pos hd
  intro i j
  unfold hardP
  have hdne : d ≠ 0 := by omega
  simp only [hdne, if_false, ite_and]
  by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
  · -- both at rare state: 0 ≤ 1 - (1-p)*s
    simp [hi, hj]
    linarith [one_sub_1mps_nonneg hd hp hp' hs hs']
  · -- rare → reservoir: 0 ≤ (1-p)*s/(d-1)
    simp [hi, hj]
    exact div_nonneg (mul_nonneg (le_of_lt (one_sub_p_pos hd hp hp')) hs.le) (le_of_lt hd1)
  · -- reservoir → rare: 0 ≤ p*s
    simp [hi, hj]
    exact mul_nonneg hp.le hs.le
  · -- reservoir → reservoir: 0 ≤ (1-p*s)/(d-1)
    simp [hi, hj]
    exact div_nonneg (le_of_lt (one_sub_ps_pos hd hp hp' hs hs')) (le_of_lt hd1)

theorem hardP_stoch {d : ℕ} (hd : 2 ≤ d) (p s : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / d) (hs : 0 < s) (hs' : s < 1) :
    ∀ i, ∑ j, hardP d p s i j = 1 := by
  haveI : NeZero d := ⟨by omega⟩
  have hdne : d ≠ 0 := by omega
  have hd1ne : ((d - 1 : ℕ) : ℝ) ≠ 0 := cast_d_sub_one_ne hd
  intro i
  unfold hardP
  simp only [hdne, if_false]
  have hentry : ∀ j : Fin d,
      (if i.val = 0 ∧ j.val = 0 then 1 - (1 - p) * s
       else if i.val = 0 then (1 - p) * s / ((d - 1 : ℕ) : ℝ)
       else if j.val = 0 then p * s
       else (1 - p * s) / ((d - 1 : ℕ) : ℝ))
      = (if i.val = 0 then (if j.val = 0 then 1 - (1 - p) * s else (1 - p) * s / ((d - 1 : ℕ) : ℝ))
        else (if j.val = 0 then p * s else (1 - p * s) / ((d - 1 : ℕ) : ℝ))) := by
    intro j
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0 <;> simp [hi, hj]
  simp only [hentry]
  by_cases hi : i.val = 0
  · -- rare-state row
    simp only [hi, if_true]
    have hsum : ∑ j : Fin d, (if j.val = 0 then 1 - (1 - p) * s else (1 - p) * s / ((d - 1 : ℕ) : ℝ))
        = (1 - (1 - p) * s) + ((d - 1 : ℕ) : ℝ) * ((1 - p) * s / ((d - 1 : ℕ) : ℝ)) := by
      rw [sum_split d (fun j => (1 - p) * s / ((d - 1 : ℕ) : ℝ)) (1 - (1 - p) * s)]
      rw [Finset.sum_const, card_val_ne_zero d, nsmul_eq_mul]
    rw [hsum]
    rw [mul_div_cancel₀ _ hd1ne]
    ring
  · -- reservoir row
    simp only [hi, if_false]
    have hsum : ∑ j : Fin d, (if j.val = 0 then p * s else (1 - p * s) / ((d - 1 : ℕ) : ℝ))
        = p * s + ((d - 1 : ℕ) : ℝ) * ((1 - p * s) / ((d - 1 : ℕ) : ℝ)) := by
      rw [sum_split d (fun j => (1 - p * s) / ((d - 1 : ℕ) : ℝ)) (p * s)]
      rw [Finset.sum_const, card_val_ne_zero d, nsmul_eq_mul]
    rw [hsum]
    rw [mul_div_cancel₀ _ hd1ne]
    ring

/-! ### Reversibility and stationary minimum -/

theorem hardP_reversible {d : ℕ} (hd : 2 ≤ d) (p s : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / d) (hs : 0 < s) (hs' : s < 1) :
    (∀ i j, hardMu d p i * hardP d p s i j = hardMu d p j * hardP d p s j i)
    ∧ (⨅ i, hardMu d p i) = p := by
  haveI : NeZero d := ⟨by omega⟩
  have hdne : d ≠ 0 := by omega
  have hd1ne : ((d - 1 : ℕ) : ℝ) ≠ 0 := cast_d_sub_one_ne hd
  have hd1pos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := cast_d_sub_one_pos hd
  constructor
  · -- detailed balance
    intro i j
    unfold hardMu hardP
    simp only [hdne, if_false]
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
    · simp [hi, hj]
    · simp [hi, hj, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
    · simp [hi, hj, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
    · simp [hi, hj]
  · -- min mu = p
    have h0 : hardMu d p ⟨0, by omega⟩ = p := by
      unfold hardMu; simp
    have hle : ∀ i : Fin d, p ≤ hardMu d p i := by
      intro i
      unfold hardMu
      by_cases hi : i.val = 0
      · simp [hi]
      · simp only [hi, if_false]
        have hpm : p * ((d - 1 : ℕ) : ℝ) ≤ 1 - p := by
          have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
          have h1 : p * (d : ℝ) ≤ 1 := (le_div_iff₀ hdpos).mp hp'
          rw [cast_d_sub_one hd]
          nlinarith
        rw [le_div_iff₀ hd1pos]
        linarith
    haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    have hbdd : BddBelow (Set.range (hardMu d p)) := by
      use p
      rintro _ ⟨i, rfl⟩
      exact hle i
    refine le_antisymm ?_ ?_
    · have h := ciInf_le hbdd ⟨0, by omega⟩
      rw [h0] at h
      exact h
    · exact le_ciInf fun i => hle i

/-! ### Stationary package -/

theorem hardMu_pos {d : ℕ} (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp' : p ≤ 1 / d) :
    ∀ i : Fin d, 0 < hardMu d p i := by
  have h1mp : 0 < 1 - p := one_sub_p_pos hd hp hp'
  intro i
  unfold hardMu
  by_cases hi : i.val = 0
  · simp [hi]; exact hp
  · simp only [hi, if_false]
    exact div_pos h1mp (cast_d_sub_one_pos hd)

theorem hardMu_sum {d : ℕ} (hd : 2 ≤ d) (p : ℝ) :
    ∑ i, hardMu d p i = 1 := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1ne : ((d - 1 : ℕ) : ℝ) ≠ 0 := cast_d_sub_one_ne hd
  unfold hardMu
  rw [sum_split d (fun _ => (1 - p) / ((d - 1 : ℕ) : ℝ)) p]
  rw [Finset.sum_const, card_val_ne_zero d, nsmul_eq_mul]
  rw [mul_div_cancel₀ _ hd1ne]
  ring

theorem hardMu_station {d : ℕ} (hd : 2 ≤ d) (p s : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / d) (hs : 0 < s) (hs' : s < 1) :
    ∀ j, ∑ i, hardMu d p i * hardP d p s i j = hardMu d p j := by
  intro j
  have hbal : ∀ i j, hardMu d p i * hardP d p s i j = hardMu d p j * hardP d p s j i :=
    (hardP_reversible hd p s hp hp' hs hs').1
  have hstoch : ∀ i, ∑ j, hardP d p s i j = 1 := hardP_stoch hd p s hp hp' hs hs'
  calc ∑ i, hardMu d p i * hardP d p s i j
      = ∑ i, hardMu d p j * hardP d p s j i := by
        apply Finset.sum_congr rfl; intro i _; exact hbal i j
    _ = hardMu d p j * ∑ i, hardP d p s j i := by rw [← Finset.mul_sum]
    _ = hardMu d p j * 1 := by rw [hstoch]
    _ = hardMu d p j := by rw [mul_one]

noncomputable def hardP_isStoch {d : ℕ} (hd : 2 ≤ d) (p s : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / d) (hs : 0 < s) (hs' : s < 1) : Stoch d where
  P := hardP d p s
  nonneg := hardP_nonneg hd p s hp hp' hs hs'
  row_stoch := hardP_stoch hd p s hp hp' hs hs'

noncomputable def hardMu_isStationary {d : ℕ} (hd : 2 ≤ d) (p s : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / d) (hs : 0 < s) (hs' : s < 1) :
    Stationary (hardP_isStoch hd p s hp hp' hs hs') where
  mu := hardMu d p
  pos := hardMu_pos hd p hp hp'
  sum_one := hardMu_sum hd p
  station := hardMu_station hd p s hp hp' hs hs'

/-! ### Disjoint intervals for the hard pair -/

theorem hardPair_disjoint (g ε : ℝ) (hg : 0 < g) (hg' : g ≤ 1 / 8) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    let s0 := 1 - sqrt (1 - g)
    let s1 := (1 + 8 * ε) * s0
    let g0 := s0 * (2 - s0)
    let g1 := s1 * (2 - s1)
    g0 = g ∧ g ≤ g1 ∧ g1 ≤ 5 * g
      ∧ (1 + ε) * g0 < (1 - ε) * g1 := by
  intro s0 s1 g0 g1
  change s0 * (2 - s0) = g ∧ g ≤ s1 * (2 - s1) ∧ s1 * (2 - s1) ≤ 5 * g
    ∧ (1 + ε) * (s0 * (2 - s0)) < (1 - ε) * (s1 * (2 - s1))
  have hs0_def : s0 = 1 - sqrt (1 - g) := rfl
  have hs1_def : s1 = (1 + 8 * ε) * s0 := rfl
  have h1mg : 0 ≤ 1 - g := by linarith
  have hsq : Real.sqrt (1 - g) ^ 2 = 1 - g := Real.sq_sqrt h1mg
  have hr : 0 ≤ Real.sqrt (1 - g) := Real.sqrt_nonneg _
  have hs0_le_g : s0 ≤ g := by rw [hs0_def]; nlinarith
  have hs0_eq : s0 * (2 - s0) = g := by
    rw [hs0_def]
    have : (1 - Real.sqrt (1 - g)) * (2 - (1 - Real.sqrt (1 - g)))
        = 1 - Real.sqrt (1 - g) ^ 2 := by ring
    rw [this, hsq]; ring
  have hs0_pos : 0 < s0 := by
    rw [hs0_def]
    have hlt : Real.sqrt (1 - g) < 1 := by
      have h1 : 1 - g < 1 := by linarith
      have := Real.sqrt_lt_sqrt h1mg h1
      rwa [Real.sqrt_one] at this
    linarith
  have hs0 : s0 = g / (2 - s0) := by
    have h2 : 0 < 2 - s0 := by linarith [hr, hs0_def]
    rw [eq_div_iff (ne_of_gt h2)]
    exact hs0_eq
  have hs0_le15 : s0 ≤ 1 / 15 := by
    have h2g : 0 < 2 - g := by linarith
    have hden : 2 - g ≤ 2 - s0 := by nlinarith [hs0_le_g]
    have hs0_bd : s0 ≤ g / (2 - g) := by
      rw [hs0]
      exact div_le_div_of_nonneg_left hg.le (by linarith) (by linarith)
    have hgb : g / (2 - g) ≤ 1 / 15 := by
      rw [div_le_iff₀ h2g]
      nlinarith [hg']
    linarith
  have hs1_pos : 0 < s1 := by
    rw [hs1_def]
    exact mul_pos (by linarith) hs0_pos
  have hs1_lt : s1 < 1 / 3 := by
    rw [hs1_def]
    nlinarith [hs0_le15]
  have hmono : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → s * (2 - s) ≤ t * (2 - t) := by
    intro s t hs hst ht
    have : t * (2 - t) - s * (2 - s) = (t - s) * (2 - t - s) := by ring
    nlinarith
  have hs01 : s0 ≤ 1 := by nlinarith [hs0_le_g, hg']
  have hs11 : s1 ≤ 1 := by linarith [hs1_lt]
  have hst : s0 ≤ s1 := by rw [hs1_def]; nlinarith
  refine ⟨hs0_eq, ?_, ?_, ?_⟩
  · rw [← hs0_eq]
    exact hmono s0 s1 (le_of_lt hs0_pos) hst hs11
  · have hg1_le2 : s1 * (2 - s1) ≤ (1 + 8 * ε) * (s0 * (2 - s0)) := by
      rw [hs1_def]
      have : (2 - (1 + 8 * ε) * s0) ≤ 2 - s0 := by nlinarith
      nlinarith [hs0_pos]
    have h : (1 + 8 * ε) * (s0 * (2 - s0)) ≤ 5 * (s0 * (2 - s0)) := by
      nlinarith [hs0_pos, hs0_eq]
    nlinarith
  · -- (1+ε) s0 (2-s0) < (1-ε) s1 (2-s1)
    rw [hs1_def]
    have hs0p : 0 < s0 := hs0_pos
    have hnum_lb : 2 - (2 + 8 * ε) * s0 ≥ 8 / 5 := by
      have ha : (2 + 8 * ε) * s0 = 2 * s0 * (1 + 4 * ε) := by ring
      have hb : 2 * s0 * (1 + 4 * ε) ≤ 2 * (1 / 15) * (1 + 4 * (1 / 2 : ℝ)) := by
        have a1 : s0 ≤ 1 / 15 := hs0_le15
        have a2 : 1 + 4 * ε ≤ 1 + 4 * (1 / 2 : ℝ) := by linarith
        nlinarith
      have hc : (2 * (1 / 15) * (1 + 4 * (1 / 2 : ℝ)) : ℝ) = 2 / 5 := by norm_num
      nlinarith
    have hpos : 0 < 8 * ε * s0 := by nlinarith
    have hε11 : ε < (11:ℝ)/16 := by linarith
    have hbr : (64 / 5 : ℝ) * (1 - ε) > 4 := by
      have heq : (64 / 5 : ℝ) * (1 - ε) = 64 / 5 - (64 / 5) * ε := by ring
      rw [heq]
      have hlt : (64 / 5 : ℝ) * ε < 44 / 5 := by nlinarith
      have h44 : (64 / 5 : ℝ) - 4 = 44 / 5 := by norm_num
      linarith
    have h4 : 8 * ε * s0 * (2 - (2 + 8 * ε) * s0) ≥ 8 * ε * s0 * (8 / 5) :=
      mul_le_mul_of_nonneg_left hnum_lb (le_of_lt hpos)
    have h5 : s0 * (2 - s0) ≤ s0 * 2 := by nlinarith
    have h6 : 2 * ε * (s0 * (2 - s0)) ≤ 4 * ε * s0 := by
      have : 2 * ε * (s0 * (2 - s0)) ≤ 2 * ε * (s0 * 2) := by
        have : 0 ≤ 2 * ε := by nlinarith
        exact mul_le_mul_of_nonneg_left h5 this
      nlinarith
    have h7 : (64 / 5) * ε * s0 * (1 - ε) ≥ 4 * ε * s0 := by
      have hpos2 : 0 ≤ ε * s0 := by nlinarith
      nlinarith
    have h8 : 8 * ε * s0 * (2 - (2 + 8 * ε) * s0) * (1 - ε) ≥ 4 * ε * s0 := by
      have : 8 * ε * s0 * (2 - (2 + 8 * ε) * s0) * (1 - ε)
          ≥ 8 * ε * s0 * (8 / 5) * (1 - ε) := by
        have h1e : 0 ≤ 1 - ε := by linarith
        have := mul_le_mul_of_nonneg_left h4 h1e
        nlinarith
      have : 8 * ε * s0 * (8 / 5) * (1 - ε) = (64 / 5) * ε * s0 * (1 - ε) := by ring
      nlinarith
    have hform : (1 + 8 * ε) * s0 * (2 - (1 + 8 * ε) * s0)
        = 8 * ε * s0 * (2 - (2 + 8 * ε) * s0) + s0 * (2 - s0) := by ring
    rw [hform]
    nlinarith



/-! ### Maximizing `(1-r^k)/k` -/

lemma one_sub_pow_le {r : ℝ} (k : ℕ) (hk : 0 < k) (hr : 0 ≤ r) (hr' : r ≤ 1) :
    1 - r ^ k ≤ k * (1 - r) := by
  have hsum : (∑ j ∈ Finset.range k, r ^ j) * (1 - r) = 1 - r ^ k :=
    geom_sum_mul_of_le_one hr' k
  have hsum_le : (∑ j ∈ Finset.range k, r ^ j) ≤ (k : ℝ) := by
    have : ∀ j ∈ Finset.range k, r ^ j ≤ 1 := fun j _ => pow_le_one₀ hr hr'
    calc ∑ j ∈ Finset.range k, r ^ j ≤ ∑ j ∈ Finset.range k, 1 :=
      Finset.sum_le_sum (fun j hj => this j hj)
      _ = k := by simp
  have h1r : 0 ≤ 1 - r := by linarith
  have : (∑ j ∈ Finset.range k, r ^ j) * (1 - r) ≤ (k : ℝ) * (1 - r) :=
    mul_le_mul_of_nonneg_right hsum_le h1r
  linarith

lemma one_sub_pow_div_le {r : ℝ} (k : ℕ) (hk : 0 < k) (hr : 0 ≤ r) (hr' : r ≤ 1) :
    (1 - r ^ k) / k ≤ 1 - r := by
  have h := one_sub_pow_le k hk hr hr'
  rw [div_le_iff₀ (by exact_mod_cast hk)]
  nlinarith

lemma geom_max {r : ℝ} (hr : 0 < r) (hr' : r < 1) :
    (⨆ k : ℕ, if 0 < k then (1 - r ^ k) / k else 0) = 1 - r := by
  haveI : Nonempty ℕ := ⟨1⟩
  have hbdd : BddAbove (Set.range (fun k : ℕ => if 0 < k then (1 - r ^ k) / k else 0)) := by
    use 1 - r
    rintro _ ⟨k, rfl⟩
    by_cases hk : 0 < k
    · simp [hk]
      exact one_sub_pow_div_le k hk (le_of_lt hr) (le_of_lt hr')
    · simp [hk]
      nlinarith
  refine le_antisymm ?_ ?_
  · apply ciSup_le
    intro k
    by_cases hk : 0 < k
    · simp [hk]
      exact one_sub_pow_div_le k hk (le_of_lt hr) (le_of_lt hr')
    · simp [hk]
      nlinarith
  · have h2 := le_ciSup hbdd (1 : ℕ)
    rw [show (if (0:ℕ) < (1:ℕ) then (1 - r ^ (1:ℕ)) / (1:ℕ) else 0) = 1 - r by simp] at h2
    exact h2

/-! ### Pseudo-spectral gap of the hard family

`γ_ps(P_s) = s(2-s)`.  On functions constant on the reservoir, `P_s` acts as a
2×2 matrix with eigenvalues `1` and `1-s`; it annihilates the reservoir-balanced
subspace, so the remaining eigenvalues vanish.  Reversibility identifies singular
values with absolute eigenvalues, whence `a_k = 1-(1-s)^{2k}` and the maximum of
`a_k/k` is attained at `k=1`.

The ordered identification uses `eigenvalues₀` directly: the Gram characteristic
polynomial has roots `1`, `(1-s)^(2k)`, and `d-2` zeros, and the spectral theorem
identifies its decreasingly sorted roots with `eigenvalues₀`.  Both `gammaPS₀`
and `Basic.gammaPS` use this sorted spectrum.
-/

/-- Sorted Gram eigenvalue `j` (index `0` is largest), local to HardPair
(indexed by `Fin d` rather than `Fin (card (Fin d))`). -/
noncomputable def gramEigD {d : ℕ} [DecidableEq (Fin d)] (L : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) : ℝ :=
  (gram_isHermitian L).eigenvalues₀ ⟨j.val, by rw [Fintype.card_fin]; exact j.isLt⟩

/-- Second singular value via sorted eigenvalues. -/
noncomputable def sigma2₀ {d : ℕ} [DecidableEq (Fin d)] (L : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  if h : 1 < d then Real.sqrt (max 0 (gramEigD L ⟨1, h⟩)) else 0

/-- Spectral deficit via sorted eigenvalues. -/
noncomputable def aOf₀ {d : ℕ} [DecidableEq (Fin d)] (L : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  1 - (sigma2₀ L) ^ 2

noncomputable def aK₀ {d : ℕ} [DecidableEq (Fin d)] (S : Stoch d) (st : Stationary S) (k : ℕ) : ℝ :=
  aOf₀ (Lk S st k)

noncomputable def gammaPS₀ {d : ℕ} [DecidableEq (Fin d)] (S : Stoch d) (st : Stationary S) : ℝ :=
  ⨆ k : ℕ, if 0 < k then aK₀ S st k / k else 0

/-- The hard stationary law, packaged. -/
noncomputable def hardSt {d : ℕ} (hd : 2 ≤ d) (p s : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / (d : ℝ)) (hs : 0 < s) (hs' : s < 1) :
    Stationary (hardP_isStoch hd p s hp hp' hs hs') :=
  hardMu_isStationary hd p s hp hp' hs hs'

set_option maxHeartbeats 200000

/-- Composition within the two-block hard family. -/
lemma hardP_mul {d : ℕ} (hd : 2 ≤ d) (p s t : ℝ) :
    hardP d p s * hardP d p t = hardP d p (s + t - s * t) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  have hn : ((d - 1 : ℕ) : ℝ) ≠ 0 := cast_d_sub_one_ne hd
  have hdne : d ≠ 0 := by omega
  ext i j
  rw [Matrix.mul_apply]
  have hsplit : (∑ a : Fin d, hardP d p s i a * hardP d p t a j) =
      hardP d p s i ⟨0, by omega⟩ * hardP d p t ⟨0, by omega⟩ j +
      ((d - 1 : ℕ) : ℝ) *
        (hardP d p s i ⟨1, by omega⟩ * hardP d p t ⟨1, by omega⟩ j) := by
    have hf : ∀ a : Fin d, hardP d p s i a * hardP d p t a j =
        if a.val = 0 then
          hardP d p s i ⟨0, by omega⟩ * hardP d p t ⟨0, by omega⟩ j
        else hardP d p s i ⟨1, by omega⟩ * hardP d p t ⟨1, by omega⟩ j := by
      intro a
      by_cases ha : a.val = 0
      · have he : a = ⟨0, by omega⟩ := Fin.ext ha
        simp [he]
      · simp [hardP, hdne, ha]
    rw [Finset.sum_congr rfl (fun a _ => hf a)]
    rw [sum_split]
    simp only [Finset.sum_const, card_val_ne_zero, nsmul_eq_mul]
  rw [hsplit]
  by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0 <;>
    simp [hardP, hdne, hi, hj] <;> field_simp <;> ring

/-- Positive powers stay in the hard family. -/
lemma hardP_pow {d : ℕ} (hd : 2 ≤ d) (p s : ℝ) (k : ℕ) (hk : 0 < k) :
    hardP d p s ^ k = hardP d p (1 - (1 - s) ^ k) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih (by omega), hardP_mul hd]
    congr 1
    simp only [pow_succ]
    ring

lemma hard_rpow_half_cancel (x : ℝ) (hx : 0 < x) :
    x ^ (-(1 / 2 : ℝ)) * x ^ (1 / 2 : ℝ) = 1 := by
  rw [← Real.rpow_add hx]
  norm_num

lemma hard_rpow_half_sq (x : ℝ) (hx : 0 < x) :
    x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
  rw [← Real.rpow_add hx]
  norm_num

lemma hard_simil_mul {d : ℕ} (mu : Fin d → ℝ) (hmu : ∀ i, 0 < mu i)
    (A B : Matrix (Fin d) (Fin d) ℝ) :
    simil mu A * simil mu B = simil mu (A * B) := by
  have hi : diagonal (fun i => mu i ^ (-(1 / 2 : ℝ))) *
      diagonal (fun i => mu i ^ (1 / 2 : ℝ)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    have hf : (fun i => mu i ^ (-(1 / 2 : ℝ)) * mu i ^ (1 / 2 : ℝ)) =
        fun _ => (1 : ℝ) := by
      funext i
      exact hard_rpow_half_cancel _ (hmu i)
    rw [hf, Matrix.diagonal_one]
  unfold simil
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (diagonal (fun i => mu i ^ (-(1 / 2 : ℝ)))), hi]
  simp

lemma hard_inv_half_cancel_matrix {d : ℕ} (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 < mu i) (A : Matrix (Fin d) (Fin d) ℝ) :
    (diagonal (fun i => mu i ^ (-(1 / 2 : ℝ))) *
      diagonal (fun i => mu i ^ (1 / 2 : ℝ))) * A = A := by
  have hf : (fun i => mu i ^ (-(1 / 2 : ℝ)) * mu i ^ (1 / 2 : ℝ)) =
      fun _ => (1 : ℝ) := by
    funext i
    exact hard_rpow_half_cancel _ (hmu i)
  rw [Matrix.diagonal_mul_diagonal, hf, Matrix.diagonal_one, one_mul]

lemma hard_simil_charpoly {d : ℕ} [DecidableEq (Fin d)]
    (mu : Fin d → ℝ) (hmu : ∀ i, 0 < mu i)
    (A : Matrix (Fin d) (Fin d) ℝ) : (simil mu A).charpoly = A.charpoly := by
  unfold simil
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc]
  exact congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M.charpoly)
    (hard_inv_half_cancel_matrix mu hmu A)

lemma hard_simil_symmetric {d : ℕ} (mu : Fin d → ℝ) (hmu : ∀ i, 0 < mu i)
    (A : Matrix (Fin d) (Fin d) ℝ) (hbal : ∀ i j, mu i * A i j = mu j * A j i) :
    (simil mu A).transpose = simil mu A := by
  ext i j
  simp only [simil, Matrix.transpose_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [Real.rpow_neg (hmu i).le, Real.rpow_neg (hmu j).le]
  have hi := hard_rpow_half_sq _ (hmu i)
  have hj := hard_rpow_half_sq _ (hmu j)
  have hni : mu i ^ (1 / 2 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (hmu i) _)
  have hnj : mu j ^ (1 / 2 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (hmu j) _)
  field_simp
  rw [pow_two, pow_two, hi, hj]
  exact (hbal i j).symm

/-- The characteristic polynomial of the rank-two hard family. -/
lemma hardP_charpoly {d : ℕ} [DecidableEq (Fin d)] (hd : 2 ≤ d) (p s : ℝ) :
    (hardP d p s).charpoly = X ^ (d - 2) * ((X - C 1) * (X - C (1 - s))) := by
  haveI : NeZero d := ⟨by omega⟩
  have hn : ((d - 1 : ℕ) : ℝ) ≠ 0 := cast_d_sub_one_ne hd
  have hdne : d ≠ 0 := by omega
  let A : Matrix (Fin d) (Fin 2) ℝ := fun i a =>
    if a = 0 then (if i.val = 0 then 1 else 0) else (if i.val = 0 then 0 else 1)
  let B : Matrix (Fin 2) (Fin d) ℝ := fun a j =>
    if a = 0 then
      (if j.val = 0 then 1 - (1 - p) * s else (1 - p) * s / ((d - 1 : ℕ) : ℝ))
    else (if j.val = 0 then p * s else (1 - p * s) / ((d - 1 : ℕ) : ℝ))
  have hAB : A * B = hardP d p s := by
    ext i j
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, A, B, hardP, hdne, hi, hj]
  have hsum (a b : ℝ) : (∑ i : Fin d, if i = 0 then a else b) =
      a + ((d - 1 : ℕ) : ℝ) * b := by
    have hsplit := sum_split d (fun _ : Fin d => b) a
    simp only [Finset.sum_const, card_val_ne_zero, nsmul_eq_mul] at hsplit
    simpa using hsplit
  have hBA : B * A = !![1 - (1 - p) * s, (1 - p) * s; p * s, 1 - p * s] := by
    ext a b
    rw [Matrix.mul_apply]
    have he : (∑ i, B a i * A i b) =
        B a ⟨0, by omega⟩ * A ⟨0, by omega⟩ b +
        ((d - 1 : ℕ) : ℝ) * (B a ⟨1, by omega⟩ * A ⟨1, by omega⟩ b) := by
      calc
        _ = ∑ i : Fin d, if i = 0 then
            B a ⟨0, by omega⟩ * A ⟨0, by omega⟩ b
            else B a ⟨1, by omega⟩ * A ⟨1, by omega⟩ b := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i = 0 <;> simp [A, B, hi]
        _ = _ := hsum _ _
    rw [he]
    fin_cases a <;> fin_cases b <;> simp [A, B] <;> field_simp
  rw [← hAB, Matrix.charpoly_mul_comm_of_le A B (by simpa using hd), hBA]
  simp only [Fintype.card_fin]
  congr 1
  rw [Matrix.charpoly_fin_two]
  simp
  ring

/-- Read the second sorted eigenvalue from the two nonzero roots. -/
lemma hard_second_eigenvalue {d : ℕ} [DecidableEq (Fin d)] (hd : 2 ≤ d)
    (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.IsHermitian) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hpoly : G.charpoly = X ^ (d - 2) * ((X - C 1) * (X - C q)))
    (h : 1 < d) :
    hG.eigenvalues₀ ⟨1, by simpa using h⟩ = q := by
  have hroots : G.charpoly.roots.map RCLike.re =
      ((1 :: q :: List.replicate (d - 2) (0 : ℝ)) : Multiset ℝ) := by
    rw [hpoly]
    change Multiset.map id (X ^ (d - 2) * ((X - C 1) * (X - C q))).roots = _
    rw [Multiset.map_id]
    rw [Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (mul_ne_zero (Polynomial.X_sub_C_ne_zero 1) (Polynomial.X_sub_C_ne_zero q))),
      Polynomial.roots_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero 1)
        (Polynomial.X_sub_C_ne_zero q)), Polynomial.roots_X_pow,
      Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
    simp only [Multiset.nsmul_singleton, ← Multiset.cons_coe,
      Multiset.coe_replicate, ← Multiset.singleton_add]
    exact (Multiset.add_comm _ _).trans (Multiset.add_assoc _ _ _)
  have hs : List.Sorted (· ≥ ·) (1 :: q :: List.replicate (d - 2) (0 : ℝ)) := by
    simp [List.sorted_cons, List.sorted_replicate, hq0, hq1]
  have he := hG.sort_roots_charpoly_eq_eigenvalues₀
  rw [hroots, Multiset.coe_sort, List.mergeSort_eq_self _ hs] at he
  have he1 := congrArg (fun l : List ℝ => l[1]?) he
  have hh : 1 < Fintype.card (Fin d) := by simpa using h
  have he2 : some (hG.eigenvalues₀ ⟨1, hh⟩) = some q := by
    simpa only [List.getElem?_cons_succ, List.getElem?_cons_zero,
      List.getElem?_ofFn, dif_pos hh] using he1.symm
  exact Option.some.inj he2

/-- Spectral identity of the hard family: `σ_2(L_k) = (1-s)^k`.
The spectrum of `P_s` is `{1, 1-s, 0, …, 0}` (2×2 reservoir block + kernel of dimension `d-2`);
reversibility makes `L` symmetric with the same eigenvalues, so singular values are absolute
eigenvalues and `σ_2(L^k) = (1-s)^k`. -/
theorem hardP_gramEig₀ {d : ℕ} [DecidableEq (Fin d)] (hd : 2 ≤ d) (p s : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / (d : ℝ)) (hs : 0 < s) (hs' : s < 1) :
    ∀ k : ℕ, 0 < k → ∀ h : 1 < d,
      gramEigD (Lk (hardP_isStoch hd p s hp hp' hs hs') (hardSt hd p s hp hp' hs hs') k) ⟨1, h⟩
        = (1 - s) ^ (2 * k) := by
  intro k hk h
  let t := 1 - (1 - s) ^ k
  have hqpos : 0 < (1 - s) ^ k := pow_pos (by linarith) _
  have hqlt : (1 - s) ^ k < 1 :=
    pow_lt_one₀ (by linarith) (by linarith) (Nat.ne_of_gt hk)
  have ht0 : 0 < t := by dsimp [t]; linarith
  have ht1 : t < 1 := by dsimp [t]; linarith
  have hmu : ∀ i, 0 < hardMu d p i := hardMu_pos hd p hp hp'
  have hL : Lk (hardP_isStoch hd p s hp hp' hs hs')
      (hardSt hd p s hp hp' hs hs') k = simil (hardMu d p) (hardP d p t) := by
    simpa only [Lk, hardSt, hardMu_isStationary, hardP_isStoch] using
      congrArg (simil (hardMu d p)) (hardP_pow hd p s k hk)
  have hbal := (hardP_reversible hd p t hp hp' ht0 ht1).1
  have hsym := hard_simil_symmetric (hardMu d p) hmu (hardP d p t) hbal
  have hparam : 1 - (t + t - t * t) = (1 - s) ^ (2 * k) := by
    dsimp [t]
    rw [show 2 * k = k + k by omega, pow_add]
    ring
  have hpoly : (gram (Lk (hardP_isStoch hd p s hp hp' hs hs')
      (hardSt hd p s hp hp' hs hs') k)).charpoly =
      X ^ (d - 2) * ((X - C 1) * (X - C ((1 - s) ^ (2 * k)))) := by
    rw [hL, gram, hsym, hard_simil_mul _ hmu, hardP_mul hd, hard_simil_charpoly _ hmu,
      hardP_charpoly hd]
    rw [hparam]
  have hq0 : 0 ≤ (1 - s) ^ (2 * k) := pow_nonneg (by linarith) _
  have hq1 : (1 - s) ^ (2 * k) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  exact hard_second_eigenvalue hd _ (gram_isHermitian _) _ hq0 hq1 hpoly h

theorem hardP_sigma2₀ {d : ℕ} [DecidableEq (Fin d)] (hd : 2 ≤ d) (p s : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / (d : ℝ)) (hs : 0 < s) (hs' : s < 1) :
    ∀ k : ℕ, 0 < k →
      sigma2₀ (Lk (hardP_isStoch hd p s hp hp' hs hs') (hardSt hd p s hp hp' hs hs') k)
        = (1 - s) ^ k := by
  intro k hk
  have hd2 : 1 < d := by omega
  have hpos : 0 < 1 - s := by linarith
  unfold sigma2₀
  simp only [dif_pos hd2]
  have hge : gramEigD (Lk (hardP_isStoch hd p s hp hp' hs hs') (hardSt hd p s hp hp' hs hs') k)
      ⟨1, hd2⟩ = (1 - s) ^ (2 * k) := hardP_gramEig₀ hd p s hp hp' hs hs' k hk hd2
  rw [hge]
  have h2 : 0 ≤ (1 - s) ^ (2 * k) := pow_nonneg (le_of_lt hpos) _
  rw [max_eq_right h2]
  have h3 : ((1 - s) ^ (2 * k) : ℝ) = ((1 - s) ^ k) ^ 2 := by
    rw [← pow_mul, mul_comm]
  rw [h3, Real.sqrt_sq (pow_nonneg (le_of_lt hpos) k)]

/-- **Hard-pair gap.** `a_k = 1-(1-s)^{2k}`. -/
theorem hardP_aK₀ {d : ℕ} [DecidableEq (Fin d)] (hd : 2 ≤ d) (p s : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / (d : ℝ)) (hs : 0 < s) (hs' : s < 1) :
    ∀ k : ℕ, 0 < k →
      aK₀ (hardP_isStoch hd p s hp hp' hs hs') (hardSt hd p s hp hp' hs hs') k
        = 1 - (1 - s) ^ (2 * k) := by
  intro k hk
  have hsig := hardP_sigma2₀ hd p s hp hp' hs hs' k hk
  unfold aK₀ aOf₀
  rw [hsig]
  have h2 : ((1 - s) ^ k) ^ 2 = (1 - s) ^ (2 * k) := by
    rw [← pow_mul, mul_comm]
  rw [h2]

theorem hardP_gamma₀ {d : ℕ} [DecidableEq (Fin d)] (hd : 2 ≤ d) (p s : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / (d : ℝ)) (hs : 0 < s) (hs' : s < 1) :
    gammaPS₀ (hardP_isStoch hd p s hp hp' hs hs') (hardSt hd p s hp hp' hs hs')
      = s * (2 - s) := by
  have hk := hardP_aK₀ hd p s hp hp' hs hs'
  have hpos : 0 < 1 - s := by linarith
  have hlt : (1 - s) ^ 2 < 1 := by
    have : (1 - s) ^ 2 = (1 - s) * (1 - s) := by ring
    nlinarith
  have hgt0 : 0 < (1 - s) ^ 2 := sq_pos_of_ne_zero (by linarith)
  -- gammaPS₀ = ⨆ k, (if 0<k then aK₀ k / k else 0) = ⨆ k, (if 0<k then (1-(1-s)^{2k})/k else 0)
  have hform : ∀ k : ℕ, (if 0 < k then aK₀ (hardP_isStoch hd p s hp hp' hs hs')
        (hardSt hd p s hp hp' hs hs') k / k else 0)
      = (if 0 < k then (1 - ((1 - s) ^ 2) ^ k) / k else 0) := by
    intro k
    by_cases hk0 : 0 < k
    · simp [hk0]
      have := hk k hk0
      rw [this]
      have h2 : (1 - s) ^ (2 * k) = ((1 - s) ^ 2) ^ k := by
        rw [← pow_mul]
      rw [h2]
    · simp [hk0]
  have : gammaPS₀ (hardP_isStoch hd p s hp hp' hs hs') (hardSt hd p s hp hp' hs hs')
      = ⨆ k : ℕ, (if 0 < k then (1 - ((1 - s) ^ 2) ^ k) / k else 0) := by
    unfold gammaPS₀
    congr 1
    ext k
    exact hform k
  rw [this]
  have hmax := geom_max hgt0 hlt
  -- s*(2-s) = 1 - (1-s)^2
  have hsq : 1 - (1 - s) ^ 2 = s * (2 - s) := by ring
  linarith

/-- Stationary package used in `hardP_gamma` (fills the `Stationary` fields). -/
theorem hardP_stationary_fields {d : ℕ} (hd : 2 ≤ d) (p s : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / (d : ℝ)) (hs : 0 < s) (hs' : s < 1) :
    (∀ i : Fin d, 0 < hardMu d p i)
    ∧ (∑ i, hardMu d p i = 1)
    ∧ (∀ j, ∑ i, hardMu d p i * hardP d p s i j = hardMu d p j) :=
  ⟨hardMu_pos hd p hp hp', hardMu_sum hd p, hardMu_station hd p s hp hp' hs hs'⟩

/-- **Hard-pair gap** in the `Basic.gammaPS` normalization.
Stated with the stationary fields provided explicitly.
Follows from `hardP_gamma₀` because `Basic.sigma2` and `sigma2₀` both use the
sorted Gram spectrum `eigenvalues₀` (see `gramEigD` vs `gramEig₀`). -/
theorem hardP_gamma {d : ℕ} [DecidableEq (Fin d)] (hd : 2 ≤ d) (p s : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / (d : ℝ)) (hs : 0 < s) (hs' : s < 1) :
    gammaPS ⟨hardP d p s, hardP_nonneg hd p s hp hp' hs hs', hardP_stoch hd p s hp hp' hs hs'⟩
      ⟨hardMu d p, hardMu_pos hd p hp hp', hardMu_sum hd p,
        hardMu_station hd p s hp hp' hs hs'⟩
      = s * (2 - s) := by
  -- Identify `gammaPS` with `gammaPS₀` via `sigma2 = sigma2₀`.
  have hEq : gammaPS ⟨hardP d p s, hardP_nonneg hd p s hp hp' hs hs', hardP_stoch hd p s hp hp' hs hs'⟩
      ⟨hardMu d p, hardMu_pos hd p hp hp', hardMu_sum hd p,
        hardMu_station hd p s hp hp' hs hs'⟩
      = gammaPS₀ (hardP_isStoch hd p s hp hp' hs hs') (hardSt hd p s hp hp' hs hs') := by
    unfold gammaPS gammaPS₀ aK aK₀ aOf aOf₀
    -- Both sides are ⨆ k, (if 0 < k then (1 - (sigma2 (Lk ...))^2)/k else 0)
    -- and sigma2 = sigma2₀ by definition (sorted eigenvalues₀).
    congr 1
  rw [hEq]
  exact hardP_gamma₀ hd p s hp hp' hs hs'

end PsgEst

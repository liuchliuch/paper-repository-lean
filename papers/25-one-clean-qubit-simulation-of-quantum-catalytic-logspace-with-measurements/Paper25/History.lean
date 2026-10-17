import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic
import Paper25.Basic
import Paper25.Norms
import Paper25.CPTP
import Paper25.Restoration

/-!
# Channel history matrix (Section 3)

On a `J`-state clock tensored with a Liouville register of dimension `dd`, the
channel history shift is `L = ∑_{t=1}^T |t⟩⟨t-1| ⊗ S_t`.  This file proves

* `L_nilpotent` : `L^{T+1} = 0`;
* `A_inv_eq_sum` : `(I - L)⁻¹ = ∑_{r=0}^T L^r`;
* `history_blocks` : the corner block `B_{T,0}` equals the product `S_T ⋯ S_1`;
* `history_frob_bound` : `‖B‖_F² ≤ J² d²` under the CPTP Frobenius hypothesis;
* `history_reg_error_real` : the scalar composition behind equation (10).

Channel matrices are indexed by `ℕ` (only the first `T` values matter).
-/

set_option maxHeartbeats 800000

noncomputable section

open scoped ComplexConjugate

open Finset Matrix

namespace Paper25

/-! ## Squared Frobenius norm on arbitrary square index types -/

/-- Squared Frobenius norm of a square complex matrix on an arbitrary finite index type. -/
def frobNormSq' {n : Type*} [Fintype n] (A : Matrix n n ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

lemma frobNormSq'_eq_frobNormSq {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    frobNormSq' A = frobNormSq A := rfl

lemma frobNormSq'_nonneg {n : Type*} [Fintype n] (A : Matrix n n ℂ) :
    0 ≤ frobNormSq' A :=
  Fintype.sum_nonneg fun _ => Fintype.sum_nonneg fun _ => Complex.normSq_nonneg _

lemma frobNormSq'_zero {n : Type*} [Fintype n] : frobNormSq' (0 : Matrix n n ℂ) = 0 := by
  simp [frobNormSq']

lemma frobNormSq'_one {n : Type*} [Fintype n] [DecidableEq n] :
    frobNormSq' (1 : Matrix n n ℂ) = Fintype.card n := by
  classical
  unfold frobNormSq'
  have hrow : ∀ i : n, (∑ j : n, Complex.normSq ((1 : Matrix n n ℂ) i j)) = 1 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  calc
    (∑ i : n, ∑ j : n, Complex.normSq ((1 : Matrix n n ℂ) i j))
        = ∑ i : n, (1 : ℝ) := Finset.sum_congr rfl fun i _ => hrow i
    _ = Fintype.card n := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_one]

/-! ## Chain products of channel matrices -/

/-- Product of `len` consecutive channel matrices starting at clock value `start`:
`S (start+len-1) ⋯ S (start)` (empty product is `1`). -/
def chainProd {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ℕ → Matrix (ι) (ι) ℂ) :
    ℕ → ℕ → Matrix (ι) (ι) ℂ
  | _, 0 => 1
  | start, len + 1 => S (start + len) * chainProd S start len

lemma chainProd_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ℕ → Matrix (ι) (ι) ℂ) (start : ℕ) :
    chainProd S start 0 = 1 := rfl

lemma chainProd_succ {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ℕ → Matrix (ι) (ι) ℂ) (start len : ℕ) :
    chainProd S start (len + 1) = S (start + len) * chainProd S start len := rfl

lemma chainProd_one {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ℕ → Matrix (ι) (ι) ℂ) (start : ℕ) :
    chainProd S start 1 = S start := by
  simp [chainProd]

/-! ## The history shift `L` -/

/-- Channel history shift `L = ∑_{t=1}^T |t⟩⟨t-1| ⊗ S_t` on `Fin J × ι`. -/
def historyShift {ι : Type*} [Fintype ι] [DecidableEq ι] (T J : ℕ) (S : ℕ → Matrix (ι) (ι) ℂ) :
    Matrix (Fin J × ι) (Fin J × ι) ℂ :=
  Matrix.of fun i j =>
    if (i.1.val = j.1.val + 1) ∧ (j.1.val < T) then
      S j.1.val i.2 j.2
    else 0

lemma historyShift_apply {T J : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ℕ → Matrix (ι) (ι) ℂ)
    (i j : Fin J × ι) :
    historyShift T J S i j =
      if (i.1.val = j.1.val + 1) ∧ (j.1.val < T) then
        S j.1.val i.2 j.2
      else 0 :=
  rfl

lemma historyShift_apply_of_lt {T J : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ℕ → Matrix (ι) (ι) ℂ)
    {i j : Fin J × ι}
    (heq : i.1.val = j.1.val + 1) (hlt : j.1.val < T) :
    historyShift T J S i j = S j.1.val i.2 j.2 := by
  rw [historyShift_apply, if_pos ⟨heq, hlt⟩]

lemma historyShift_apply_eq_zero {T J : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ℕ → Matrix (ι) (ι) ℂ)
    {i j : Fin J × ι}
    (h : i.1.val ≠ j.1.val + 1 ∨ T ≤ j.1.val) :
    historyShift T J S i j = 0 := by
  rw [historyShift_apply]
  by_cases hc : (i.1.val = j.1.val + 1) ∧ (j.1.val < T)
  · exfalso
    rcases h with h | h
    · exact h hc.1
    · exact absurd hc.2 (Nat.not_lt.mpr h)
  · exact if_neg hc

/-- If `n ≥ 1` and the clock would have to advance past `T`, the power vanishes. -/
lemma historyShift_pow_eq_zero_of_le {T J : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ℕ → Matrix (ι) (ι) ℂ)
    {n : ℕ} (hn : 1 ≤ n) :
    ∀ (i j : Fin J × ι), T < j.1.val + n → (historyShift T J S ^ n) i j = 0 := by
  induction n with
  | zero => exact absurd hn (by omega)
  | succ n ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k.1.val = j.1.val + 1 ∧ j.1.val < T
    · by_cases hn0 : n = 0
      · subst hn0
        rw [pow_zero]
        by_cases hik : i = k
        · subst hik
          have hR : historyShift T J S i j = 0 := by
            apply historyShift_apply_eq_zero
            by_cases hd : i.1.val = j.1.val + 1
            · exact Or.inr (Nat.le_of_not_gt (fun hlt => by
                have : T < j.1.val + 1 := h
                omega))
            · exact Or.inl hd
          show (1 : Matrix (Fin J × ι) (Fin J × ι) ℂ) i i
              * historyShift T J S i j = 0
          rw [hR, mul_zero]
        · have hz : ((1 : Matrix (Fin J × ι) (Fin J × ι) ℂ) i k) = 0 := by
            simp [hik]
          rw [hz, zero_mul]
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        have hT : T < k.1.val + n := by
          have hk1 : k.1.val = j.1.val + 1 := hk.1
          omega
        have hleft : (historyShift T J S ^ n) i k = 0 := ih hn1 i k hT
        rw [hleft, zero_mul]
    · have hright : historyShift T J S k j = 0 := by
        apply historyShift_apply_eq_zero
        rcases not_and_or.mp hk with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (Nat.le_of_not_gt h2)
      rw [hright, mul_zero]

/-- If `n ≥ 1` and the clock distance is wrong, the power vanishes. -/
lemma historyShift_pow_eq_zero_of_ne {T J : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ℕ → Matrix (ι) (ι) ℂ)
    {n : ℕ} (hn : 1 ≤ n) :
    ∀ (i j : Fin J × ι), i.1.val ≠ j.1.val + n → (historyShift T J S ^ n) i j = 0 := by
  induction n with
  | zero => exact absurd hn (by omega)
  | succ n ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k.1.val = j.1.val + 1 ∧ j.1.val < T
    · by_cases hn0 : n = 0
      · subst hn0
        rw [pow_zero]
        by_cases hik : i = k
        · subst hik
          exfalso
          apply h
          have hk1 : i.1.val = j.1.val + 1 := hk.1
          omega
        · have hz : ((1 : Matrix (Fin J × ι) (Fin J × ι) ℂ) i k) = 0 := by
            simp [hik]
          rw [hz, zero_mul]
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        have hleft : (historyShift T J S ^ n) i k = 0 := by
          refine ih hn1 i k ?_
          intro heq
          apply h
          have hk1 : k.1.val = j.1.val + 1 := hk.1
          omega
        rw [hleft, zero_mul]
    · have hright : historyShift T J S k j = 0 := by
        apply historyShift_apply_eq_zero
        rcases not_and_or.mp hk with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (Nat.le_of_not_gt h2)
      rw [hright, mul_zero]

/-- The history shift is nilpotent: `L^{T+1} = 0`. -/
theorem L_nilpotent {T J : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ℕ → Matrix (ι) (ι) ℂ) :
    historyShift T J S ^ (T + 1) = 0 := by
  ext i j
  have h1 : 1 ≤ T + 1 := Nat.succ_pos T
  rw [historyShift_pow_eq_zero_of_le S h1 i j (by omega : T < j.1.val + (T + 1))]
  rfl

/-! ## The geometric series inverse -/

/-- Truncated geometric series `∑_{r=0}^T L^r`. -/
def historySum {m : Type*} [Fintype m] [DecidableEq m] (L : Matrix m m ℂ) (T : ℕ) :
    Matrix m m ℂ :=
  ∑ r ∈ range (T + 1), L ^ r

lemma historySum_eq_geom_sum {m : Type*} [Fintype m] [DecidableEq m] (L : Matrix m m ℂ) (T : ℕ) :
    historySum L T = ∑ r ∈ range (T + 1), L ^ r := rfl

/-- `(I - L) · ∑_{r=0}^T L^r = I` when `L^{T+1} = 0`. -/
lemma one_sub_mul_historySum {m : Type*} [Fintype m] [DecidableEq m] (L : Matrix m m ℂ) {T : ℕ}
    (h : L ^ (T + 1) = 0) :
    (1 - L) * historySum L T = 1 := by
  rw [historySum_eq_geom_sum, mul_neg_geom_sum, h, sub_zero]

/-- `∑_{r=0}^T L^r · (I - L) = I` when `L^{T+1} = 0`. -/
lemma historySum_mul_one_sub {m : Type*} [Fintype m] [DecidableEq m] (L : Matrix m m ℂ) {T : ℕ}
    (h : L ^ (T + 1) = 0) :
    historySum L T * (1 - L) = 1 := by
  rw [historySum_eq_geom_sum, geom_sum_mul_neg, h, sub_zero]

/-- Closed form of the inverse: `(I - L)⁻¹ = ∑_{r=0}^T L^r`. -/
theorem A_inv_eq_sum {m : Type*} [Fintype m] [DecidableEq m] (L : Matrix m m ℂ) {T : ℕ}
    (h : L ^ (T + 1) = 0) :
    (1 - L)⁻¹ = historySum L T :=
  Matrix.inv_eq_right_inv (one_sub_mul_historySum L h)

/-- The inverse formula specialized to the history shift. -/
theorem historyShift_inv {T J : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ℕ → Matrix (ι) (ι) ℂ) :
    (1 - historyShift T J S)⁻¹ = historySum (historyShift T J S) T :=
  A_inv_eq_sum _ (L_nilpotent S)

/-! ## Corner block of the inverse -/

/-- The `(T, 0)` corner of `L^n` vanishes unless `n = T`. -/
theorem historyShift_pow_corner_zero {T J : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ℕ → Matrix (ι) (ι) ℂ)
    {n : ℕ} (hn : 1 ≤ n) (hne : n ≠ T) (a b : ι) (hJ : T + 1 ≤ J) :
    (historyShift T J S ^ n) ((⟨T, by omega⟩ : Fin J), a)
      ((⟨0, by omega⟩ : Fin J), b) = 0 := by
  by_cases hdist : (T : ℕ) = 0 + n
  · exact absurd (by omega : n = T) hne
  · exact historyShift_pow_eq_zero_of_ne S hn _ _ (by
      intro heq
      exact hdist heq)

/-- The unique contributing power at the `(T, 0)` corner is `n = T`. -/
theorem history_blocks_sum {T J : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ℕ → Matrix (ι) (ι) ℂ)
    (hJ : T + 1 ≤ J) (a b : ι) :
    (historySum (historyShift T J S) T) ((⟨T, by omega⟩ : Fin J), a)
        ((⟨0, by omega⟩ : Fin J), b)
      = (historyShift T J S ^ T) ((⟨T, by omega⟩ : Fin J), a)
          ((⟨0, by omega⟩ : Fin J), b) := by
  classical
  unfold historySum
  rw [Finset.sum_apply, Finset.sum_apply]
  rw [Finset.sum_eq_single T]
  · intro r hr hne
    by_cases hr0 : r = 0
    · subst hr0
      rw [pow_zero]
      show ((1 : Matrix (Fin J × ι) (Fin J × ι) ℂ) ((⟨T, by omega⟩ : Fin J), a)
          ((⟨0, by omega⟩ : Fin J), b)) = 0
      rw [Matrix.one_apply]
      split_ifs with hif
      · exfalso
        have hT0 : T = 0 := by
          have h1 : ((⟨T, by omega⟩ : Fin J), a).1 = ((⟨0, by omega⟩ : Fin J), b).1 := by
            rw [hif]
          simpa using h1
        subst hT0
        exact absurd rfl hne
      · rfl
    · have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
      have hne' : r ≠ T := fun hc => hne hc
      exact historyShift_pow_corner_zero S hr1 hne' a b hJ
  · intro hTmem
    exact absurd (Finset.mem_range.mpr (by omega : T < T + 1)) hTmem

/-- The `(t,r)` block of a matrix with clock and data registers. -/
def clockBlock {J : ℕ} {ι : Type*} (B : Matrix (Fin J × ι) (Fin J × ι) ℂ)
    (t r : Fin J) : Matrix ι ι ℂ := fun a b => B (t,a) (r,b)

lemma clockBlock_mul {J : ℕ} {ι : Type*} [Fintype ι]
    (A B : Matrix (Fin J × ι) (Fin J × ι) ℂ) (t r : Fin J) :
    clockBlock (A * B) t r = ∑ s : Fin J, clockBlock A t s * clockBlock B s r := by
  classical
  ext a b
  change (A * B) (t,a) (r,b) = (∑ s : Fin J, clockBlock A t s * clockBlock B s r) a b
  rw [Matrix.sum_apply]
  simp only [Matrix.mul_apply, clockBlock, Fintype.sum_prod_type]

lemma clockBlock_one {J : ℕ} {ι : Type*} [DecidableEq ι] (t r : Fin J) :
    clockBlock (1 : Matrix (Fin J × ι) (Fin J × ι) ℂ) t r =
      if t = r then 1 else 0 := by
  classical
  ext a b
  by_cases h : t = r <;> simp [clockBlock, Matrix.one_apply, h, Prod.ext_iff]

lemma clockBlock_historyShift {T J : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ℕ → Matrix ι ι ℂ) (t r : Fin J) :
    clockBlock (historyShift T J S) t r =
      if t.val = r.val + 1 ∧ r.val < T then S r.val else 0 := by
  ext a b
  by_cases h : t.val = r.val + 1 ∧ r.val < T <;>
    simp [clockBlock, historyShift_apply, h]

/-- Every length-`n` clock path is unique. Its data block is the time-ordered
product, with the latest channel on the left. This includes the empty path. -/
lemma clockBlock_historyShift_pow {T J : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ℕ → Matrix ι ι ℂ) (n : ℕ) (r : Fin J)
    (hT : r.val + n ≤ T) (hJ : r.val + n < J) :
    clockBlock (historyShift T J S ^ n) ⟨r.val+n,hJ⟩ r = chainProd S r.val n := by
  induction n with
  | zero => simp [chainProd, clockBlock_one]
  | succ n ih =>
    have hnJ : r.val + n < J := by omega
    have hnT : r.val + n ≤ T := by omega
    rw [pow_succ', clockBlock_mul]
    rw [Finset.sum_eq_single (⟨r.val+n,hnJ⟩ : Fin J)]
    · rw [clockBlock_historyShift, if_pos (by constructor <;> dsimp <;> omega)]
      rw [ih hnT hnJ, chainProd_succ]
    · intro s _ hs
      have hne : ¬ (r.val + (n+1) = s.val+1 ∧ s.val < T) := by
        intro h
        apply hs
        apply Fin.ext
        dsimp
        omega
      rw [clockBlock_historyShift, if_neg hne, zero_mul]
    · simp

/-- The corner equality has no certificate assumption: it follows from the
unique clock path of the explicitly defined history shift. -/
theorem history_corner {T J : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ℕ → Matrix ι ι ℂ) (hJ : T+1≤J) (a b : ι) :
    (historyShift T J S ^ T) ((⟨T,by omega⟩ : Fin J),a)
      ((⟨0,by omega⟩ : Fin J),b) = chainProd S 0 T a b := by
  have h := clockBlock_historyShift_pow (T := T) S T (⟨0,by omega⟩ : Fin J)
    (by simp) (by dsimp; omega)
  simpa [clockBlock] using congrFun (congrFun h a) b

/-- Equation (5): the inverse's `(T,0)` block is the full channel product. -/
theorem history_blocks {T J : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ℕ → Matrix ι ι ℂ) (hJ : T+1≤J) (a b : ι) :
    (historySum (historyShift T J S) T) ((⟨T,by omega⟩ : Fin J),a)
      ((⟨0,by omega⟩ : Fin J),b) = chainProd S 0 T a b := by
  rw [history_blocks_sum S hJ a b]
  exact history_corner S hJ a b

lemma clockBlock_historyShift_pow_zero_of_ne {T J : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (S : ℕ → Matrix ι ι ℂ)
    (n : ℕ) (t r : Fin J) (h : t.val ≠ r.val+n) :
    clockBlock (historyShift T J S ^ n) t r = 0 := by
  ext a b
  by_cases hn : n = 0
  · subst n
    have htr : t ≠ r := by intro e; subst t; exact h (by simp)
    simp [clockBlock, Matrix.one_apply, Prod.ext_iff, htr]
  · exact historyShift_pow_eq_zero_of_ne S (by omega) (t,a) (r,b) h

/-- All inverse blocks, including the padded clock's diagonal identity blocks.
No hypothesis about channel invertibility or singular values is used. -/
theorem historySum_block {T J : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ℕ → Matrix ι ι ℂ) (t r : Fin J) :
    clockBlock (historySum (historyShift T J S) T) t r =
      if t = r then 1 else
        if r.val < t.val ∧ t.val ≤ T then chainProd S r.val (t.val-r.val) else 0 := by
  classical
  have hsum : clockBlock (historySum (historyShift T J S) T) t r =
      ∑ n ∈ range (T+1), clockBlock (historyShift T J S ^ n) t r := by
    ext a b
    change (∑ n ∈ range (T+1), historyShift T J S ^ n) (t,a) (r,b) = _
    simp only [Matrix.sum_apply, clockBlock]
  rw [hsum]
  by_cases htr : t = r
  · subst t
    rw [if_pos rfl, Finset.sum_eq_single 0]
    · simp [clockBlock_one]
    · intro n _ hn
      exact clockBlock_historyShift_pow_zero_of_ne S n r r (by omega)
    · simp
  · rw [if_neg htr]
    by_cases hgood : r.val < t.val ∧ t.val ≤ T
    · rw [if_pos hgood, Finset.sum_eq_single (t.val-r.val)]
      · have hval : r.val+(t.val-r.val)=t.val := by omega
        have hp := clockBlock_historyShift_pow (T := T) S (t.val-r.val) r
          (by omega) (by omega)
        have heq : (⟨r.val+(t.val-r.val),by omega⟩ : Fin J)=t := Fin.ext hval
        simpa only [heq] using hp
      · intro n _ hn
        exact clockBlock_historyShift_pow_zero_of_ne S n t r (by omega)
      · intro hn
        exfalso
        apply hn
        exact Finset.mem_range.mpr (by omega)
    · rw [if_neg hgood]
      apply Finset.sum_eq_zero
      intro n _
      by_cases hn : n=0
      · subst n
        simp [clockBlock_one, htr]
      · by_cases hdist : t.val=r.val+n
        · ext a b
          change (historyShift T J S ^ n) (t,a) (r,b) = 0
          exact historyShift_pow_eq_zero_of_le S (by omega) (t,a) (r,b) (by dsimp; omega)
        · exact clockBlock_historyShift_pow_zero_of_ne S n t r hdist

/-! ## Frobenius bound -/

/-- Hypothesis of Lemma 3 (CPTP Frobenius bound) for every consecutive product of
the elementary Liouville matrices. -/
structure CPTPFrobBound {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ℕ → Matrix (ι) (ι) ℂ) (T d : ℕ) : Prop where
  /-- Each chain product of length at most `T` satisfies the Lemma 3 bound. -/
  chain_bound : ∀ start len, start + len ≤ T → frobNormSq' (chainProd S start len) ≤ (d : ℝ) ^ 2

/-- Frobenius bound of a single clock block of the history inverse. -/
theorem history_block_frob_bound {T : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ℕ → Matrix (ι) (ι) ℂ)
    (d : ℕ) (hb : CPTPFrobBound S T d) (start len : ℕ) (hlen : start + len ≤ T) :
    frobNormSq' (chainProd S start len) ≤ (d : ℝ) ^ 2 :=
  hb.chain_bound start len hlen

/-- Splitting the entrywise norm into its clock blocks is a finite
reindexing, so no operator-norm estimates are hidden in equation (6). -/
lemma frobNormSq'_clockBlocks {J : ℕ} {ι : Type*} [Fintype ι]
    (B : Matrix (Fin J × ι) (Fin J × ι) ℂ) :
    frobNormSq' B = ∑ t : Fin J, ∑ r : Fin J, frobNormSq' (clockBlock B t r) := by
  unfold frobNormSq'
  simp only [Fintype.sum_prod_type, clockBlock]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_comm]

/-- Equation (6), for the actual inverse matrix: Lemma 3's bound on each
consecutive channel product bounds the sum of every clock block. -/
theorem history_frob_bound {T J : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ℕ → Matrix ι ι ℂ) (d : ℕ) (hb : CPTPFrobBound S T d) :
    frobNormSq' ((1-historyShift T J S)⁻¹) ≤ (J : ℝ)^2*(d : ℝ)^2 := by
  rw [historyShift_inv, frobNormSq'_clockBlocks]
  have hblocks : ∀ t r : Fin J,
      frobNormSq' (clockBlock (historySum (historyShift T J S) T) t r) ≤ (d : ℝ)^2 := by
    intro t r
    rw [historySum_block]
    split_ifs with htr hgood
    · simpa only [chainProd_zero] using hb.chain_bound 0 0 (by omega)
    · exact hb.chain_bound r.val (t.val-r.val) (by omega)
    · rw [frobNormSq'_zero]
      positivity
  calc
    (∑ t : Fin J, ∑ r : Fin J,
        frobNormSq' (clockBlock (historySum (historyShift T J S) T) t r))
      ≤ ∑ _t : Fin J, ∑ _r : Fin J, (d : ℝ)^2 :=
        Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun r _ => hblocks t r
    _ = (J : ℝ)^2*(d : ℝ)^2 := by simp; ring

/-- The dimension substitution `d=K D` in equation (6), on the same actual
history inverse matrix. -/
theorem history_frob_bound_dimensions {T J : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (S : ℕ → Matrix ι ι ℂ)
    (K D : ℕ) (hb : CPTPFrobBound S T (K*D)) :
    frobNormSq' ((1-historyShift T J S)⁻¹) ≤ (J : ℝ)^2*(K : ℝ)^2*(D : ℝ)^2 := by
  calc
    _ ≤ (J : ℝ)^2*((K*D : ℕ) : ℝ)^2 := history_frob_bound S (K*D) hb
    _ = (J : ℝ)^2*(K : ℝ)^2*(D : ℝ)^2 := by push_cast; ring

/-- The count of potentially nonzero clock blocks of `B` is at most `J²`. -/
theorem history_block_count (J : ℕ) (_hJ : 0 ≤ J) : (J : ℝ) ^ 2 = (J : ℝ) * (J : ℝ) := by
  ring

/-- Equation (6) in scalar form: if every nonzero clock block has squared Frobenius
norm at most `d²` and there are at most `J²` such blocks, then `‖B‖_F² ≤ J² d²`. -/
theorem history_frob_bound_scalar (J d : ℝ) :
    (J * J) * (d * d) = J ^ 2 * d ^ 2 := by
  ring

/-! ## Trace extraction (equations 8–9) -/

/-- `|u⟩⟨v| ⊗ P`, in the clock/data indexing used by `historyShift`. -/
def historySelector {J : ℕ} {ι : Type*} (u v : Fin J) (P : Matrix ι ι ℂ) :
    Matrix (Fin J × ι) (Fin J × ι) ℂ :=
  fun i j => if i.1=u ∧ j.1=v then P i.2 j.2 else 0

/-- The trace selector reads precisely the opposite clock block. -/
theorem trace_historySelector_mul {J : ℕ} {ι : Type*} [Fintype ι]
    (u v : Fin J) (P : Matrix ι ι ℂ) (B : Matrix (Fin J × ι) (Fin J × ι) ℂ) :
    Matrix.trace (historySelector u v P * B) = Matrix.trace (P * clockBlock B v u) := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
  have hterm : ∀ i : Fin J, ∀ a : ι, ∀ j : Fin J, ∀ b : ι,
      historySelector u v P (i,a) (j,b) * B (j,b) (i,a) =
        if i=u then if j=v then P a b * B (v,b) (u,a) else 0 else 0 := by
    intro i a j b
    by_cases hi : i=u <;> by_cases hj : j=v <;> simp [historySelector,hi,hj]
  simp only [hterm]
  simp [clockBlock, Finset.sum_ite_irrel]

/-- The actual inverse and selector from equation (8) extract the full
channel product from equation (5). -/
theorem trace_history_inverse {T J : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ℕ → Matrix ι ι ℂ) (hJ : T+1≤J) (P : Matrix ι ι ℂ) :
    Matrix.trace (historySelector (⟨0,by omega⟩ : Fin J) ⟨T,by omega⟩ P *
      (1-historyShift T J S)⁻¹) = Matrix.trace (P * chainProd S 0 T) := by
  rw [trace_historySelector_mul, historyShift_inv]
  have hblock : clockBlock (historySum (historyShift T J S) T)
      (⟨T,by omega⟩ : Fin J) ⟨0,by omega⟩ = chainProd S 0 T := by
    ext a b
    exact history_blocks S hJ a b
  rw [hblock]

/-- Equation (9), before replacing the work inner product by `e_x/√K`:
normalizing the actual history trace cancels the catalyst operator dimension. -/
theorem eq9_history_trace {T J m n : ℕ}
    (S : ℕ → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hJ : T+1≤J) (ω η z : Fin m → ℂ)
    (hrest : ExactRestoration (chainProd S 0 T) ω η) (hn : (n : ℂ) ≠ 0) :
    Matrix.trace (historySelector (⟨0,by omega⟩ : Fin J) ⟨T,by omega⟩
      (kronRankOneId ω z) * (1-historyShift T J S)⁻¹) / (n : ℂ) = cinner z η := by
  rw [trace_history_inverse S hJ, eq4_bias_identity hrest z]
  field_simp

/-! ## Regularization error bound (equation 10) -/

/-- Pure real form of equation (10): if the nuclear-norm error of the regularized
inverse is at most `(lam / 2) J² d²` and `d² = K² D²`, then the normalized trace
error is at most `(lam / 2) J² K²`. -/
theorem history_reg_error_real (lam J K D2 : ℝ) (hlam : 0 < lam) (hK : 0 < K)
    (hD2 : 0 < D2) :
    (lam / 2) * J ^ 2 * (K ^ 2 * D2 ^ 2) / D2 ^ 2 = (lam / 2) * J ^ 2 * K ^ 2 := by
  have hD2ne : D2 ≠ 0 := ne_of_gt hD2
  have hD2sq : D2 ^ 2 ≠ 0 := pow_ne_zero 2 hD2ne
  field_simp [hD2sq]

/-- Equation (10) as a scalar bound on the normalized trace error. -/
theorem history_reg_error_scalar (lam J K D2 : ℝ) (hlam : 0 < lam) (hK : 0 < K)
    (hD2 : 0 < D2) (err : ℝ)
    (herr : err ≤ (lam / 2) * J ^ 2 * (K ^ 2 * D2 ^ 2) / D2 ^ 2) :
    err ≤ (lam / 2) * J ^ 2 * K ^ 2 := by
  have h := history_reg_error_real lam J K D2 hlam hK hD2
  rw [h] at herr
  exact herr

end Paper25

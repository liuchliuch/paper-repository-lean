import Paper14.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
/-!
# Lemma 2: self-induction and time scaling

Paper anchors: Thmtheorem2 (φ_r a.e. bijection, `(φ_r)_* m = m_r`, `B_r φ_r = φ_r B`,
`φ_r → id` in measure, `H_{r,n}(φ_r x) = r^{-2} H_n(x)`).

Proved here: coordinate unfolds of `φ_r`, `φ_r^{-1}`; first-coordinate bound
`(φ_r x).1 ∈ (0, r]`; `φ_r(Ω) ⊆ Y_r`; the floor/ceil inequalities of paper S2.p6;
both algebraic inverse identities; `φ_r = (r·, r·)` on `{a+b > r^{-1}}`; and the
matrix identity `h_u g_r = g_r h_{r^2 u}`.
-/
open MeasureTheory Filter Topology Set Matrix
namespace Paper14

/-! ## Coordinate unfolds -/

theorem phiR_eq' (r a b : ℝ) :
    phiR r (a, b) = (r * a, r * (b + ((phiJ r a b : ℤ) : ℝ) * a)) := rfl

theorem phiR_fst (r a b : ℝ) : (phiR r (a, b)).1 = r * a := rfl

theorem phiR_snd (r a b : ℝ) :
    (phiR r (a, b)).2 = r * (b + ((phiJ r a b : ℤ) : ℝ) * a) := rfl

theorem phiRInv_fst (r s t : ℝ) : (phiRInv r (s, t)).1 = s / r := rfl

theorem phiRInv_snd (r s t : ℝ) :
    (phiRInv r (s, t)).2
      = (t - ((Int.ceil ((t - r) / s) : ℤ) : ℝ) * s) / r := rfl

theorem phiJ_apply (r a b : ℝ) : phiJ r a b = ⌊(r⁻¹ - b) / a⌋ := rfl

/-! ## `j = 0` when `a + b > r^{-1}` (paper S2.p7) -/

theorem phiJ_eq_zero {r a b : ℝ} (ha : 0 < a) (hb : b ≤ r⁻¹) (h : r⁻¹ - b < a) :
    phiJ r a b = 0 := by
  rw [phiJ_apply, Int.floor_eq_zero_iff]
  exact ⟨div_nonneg (by linarith) (le_of_lt ha), (div_lt_one ha).2 h⟩

theorem phiJ_eq_zero_of_sum {r a b : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hx : (a, b) ∈ Omega) (hsum : r⁻¹ < a + b) : phiJ r a b = 0 := by
  rcases mem_Omega.1 hx with ⟨ha0, ha1, hb0, hb1, _⟩
  have hinv : (1 : ℝ) < r⁻¹ := (one_lt_inv₀ hr).2 hr1
  have hb : b ≤ r⁻¹ := le_of_lt (lt_of_le_of_lt hb1 hinv)
  exact phiJ_eq_zero ha0 hb (by linarith)

theorem phiR_eq_smul_of_sum {r a b : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hx : (a, b) ∈ Omega) (hsum : r⁻¹ < a + b) :
    phiR r (a, b) = (r * a, r * b) := by
  have hj := phiJ_eq_zero_of_sum hr hr1 hx hsum
  rw [phiR_eq', hj]
  simp

/-! ## First coordinate of `φ_r` -/

theorem phiR_fst_mem_Ioc {r a b : ℝ} (hr : 0 < r) (hx : (a, b) ∈ Omega) :
    (phiR r (a, b)).1 ∈ Ioc (0 : ℝ) r := by
  rcases mem_Omega.1 hx with ⟨ha0, ha1, _, _, _⟩
  rw [phiR_fst]
  exact ⟨mul_pos hr ha0, by nlinarith [le_of_lt hr]⟩

theorem phiR_fst_pos {r a b : ℝ} (hr : 0 < r) (hx : (a, b) ∈ Omega) :
    0 < (phiR r (a, b)).1 :=
  (phiR_fst_mem_Ioc hr hx).1

theorem phiR_fst_le {r a b : ℝ} (hr : 0 < r) (hx : (a, b) ∈ Omega) :
    (phiR r (a, b)).1 ≤ r :=
  (phiR_fst_mem_Ioc hr hx).2

/-! ## Floor bounds behind `φ_r(Ω) ⊆ Y_r` -/

theorem phiJ_mul_le {r a b : ℝ} (ha : 0 < a) :
    ((phiJ r a b : ℤ) : ℝ) * a ≤ r⁻¹ - b := by
  have h := Int.floor_le ((r⁻¹ - b) / a)
  have := mul_le_mul_of_nonneg_right h (le_of_lt ha)
  rw [div_mul_cancel₀ _ (ne_of_gt ha)] at this
  simpa [phiJ_apply] using this

theorem phiJ_mul_lt {r a b : ℝ} (ha : 0 < a) :
    r⁻¹ - b < (((phiJ r a b : ℤ) : ℝ) + 1) * a := by
  have h := Int.lt_floor_add_one ((r⁻¹ - b) / a)
  have := mul_lt_mul_of_pos_right h ha
  rw [div_mul_cancel₀ _ (ne_of_gt ha)] at this
  simpa [phiJ_apply] using this

theorem phiJ_mul_gt {r a b : ℝ} (ha : 0 < a) :
    r⁻¹ - b - a < ((phiJ r a b : ℤ) : ℝ) * a := by
  have hfloor := Int.lt_floor_add_one ((r⁻¹ - b) / a)
  have hlt : (r⁻¹ - b) / a - 1 < ((⌊(r⁻¹ - b) / a⌋ : ℤ) : ℝ) :=
    sub_lt_iff_lt_add.mpr hfloor
  have := mul_lt_mul_of_pos_right hlt ha
  have heq : ((r⁻¹ - b) / a - 1) * a = r⁻¹ - b - a := by
    have hne : a ≠ 0 := ne_of_gt ha
    calc ((r⁻¹ - b) / a - 1) * a = ((r⁻¹ - b) / a) * a - a := by ring
      _ = (r⁻¹ - b) - a := by rw [div_mul_cancel₀ _ hne]
  rw [heq] at this
  simpa [phiJ_apply] using this

/-- Floor bounds: `0 < b + j a`, `b + j a ≤ r^{-1}`, `r^{-1} < a + b + j a`. -/
theorem phiJ_add_bounds {r a b : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (ha1 : a ≤ 1) (ha : 0 < a) :
    0 < b + ((phiJ r a b : ℤ) : ℝ) * a ∧
      b + ((phiJ r a b : ℤ) : ℝ) * a ≤ r⁻¹ ∧
        r⁻¹ < a + b + ((phiJ r a b : ℤ) : ℝ) * a := by
  have hinv : (1 : ℝ) < r⁻¹ := (one_lt_inv₀ hr).2 hr1
  have ha_lt : a < r⁻¹ := lt_of_le_of_lt ha1 hinv
  refine ⟨?_, ?_, ?_⟩
  · have h := phiJ_mul_gt (r := r) (a := a) (b := b) ha
    linarith only [h, ha_lt]
  · have h := phiJ_mul_le (r := r) (a := a) (b := b) ha
    linarith only [h]
  · have h := phiJ_mul_lt (r := r) (a := a) (b := b) ha
    have heq : (((phiJ r a b : ℤ) : ℝ) + 1) * a
        = ((phiJ r a b : ℤ) : ℝ) * a + a := by ring
    linarith only [h, heq]

/-! ## `φ_r` maps `Ω` into `Y_r` -/

theorem phiR_mem_Omega {r a b : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hx : (a, b) ∈ Omega) : phiR r (a, b) ∈ Omega := by
  rcases mem_Omega.1 hx with ⟨ha0, ha1, hb0, hb1, hsum⟩
  obtain ⟨hj0, hj1, hj2⟩ := phiJ_add_bounds hr hr1 ha1 ha0
  have hri : r * r⁻¹ = (1:ℝ) := mul_inv_cancel₀ (ne_of_gt hr)
  rw [phiR_eq', mem_Omega]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact mul_pos hr ha0
  · calc r * a ≤ r * 1 := mul_le_mul_of_nonneg_left ha1 hr.le
         _ ≤ 1 := by simpa using hr1.le
  · exact mul_pos hr hj0
  · have h := mul_le_mul_of_nonneg_left hj1 (le_of_lt hr)
    rw [hri] at h
    exact h
  · have h := mul_lt_mul_of_pos_left hj2 hr
    rw [hri] at h
    have heq : r * (a + b + ((phiJ r a b : ℤ) : ℝ) * a)
        = r * a + r * (b + ((phiJ r a b : ℤ) : ℝ) * a) := by ring
    rw [heq] at h
    exact h

theorem phiR_mem_Yr {r a b : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hx : (a, b) ∈ Omega) : phiR r (a, b) ∈ Yr r := by
  have h1 : phiR r (a, b) ∈ Omega := phiR_mem_Omega hr hr1 hx
  have h2 : (phiR r (a, b)).1 ≤ r := phiR_fst_le hr hx
  exact ⟨h1, h2⟩

/-! ## Floor/ceil inequalities for `φ_r^{-1}` (paper S2.p6) -/

theorem ceil_sub_one_lt (x : ℝ) : ((Int.ceil x : ℤ) : ℝ) - 1 < x :=
  (Int.ceil_eq_iff (a := x) (z := Int.ceil x)).mp rfl |>.1

theorem ceil_sub_bounds {s t r : ℝ} (hs : 0 < s) :
    r - s < t - ((Int.ceil ((t - r) / s) : ℤ) : ℝ) * s ∧
      t - ((Int.ceil ((t - r) / s) : ℤ) : ℝ) * s ≤ r := by
  set x : ℝ := (t - r) / s with hx
  have hle : x ≤ (Int.ceil x : ℤ) := Int.le_ceil _
  have hgt : ((Int.ceil x : ℤ) : ℝ) - 1 < x := ceil_sub_one_lt _
  have hmul_le : t - r ≤ ((Int.ceil x : ℤ) : ℝ) * s := by
    have := mul_le_mul_of_nonneg_right hle (le_of_lt hs)
    rwa [hx, div_mul_cancel₀ _ (ne_of_gt hs)] at this
  have hmul_gt : (((Int.ceil x : ℤ) : ℝ) - 1) * s < t - r := by
    have := mul_lt_mul_of_pos_right hgt hs
    rwa [hx, div_mul_cancel₀ _ (ne_of_gt hs)] at this
  have heq : (((Int.ceil x : ℤ) : ℝ) - 1) * s
      = ((Int.ceil x : ℤ) : ℝ) * s - s := by ring
  constructor
  · linarith only [hmul_gt, heq]
  · linarith only [hmul_le]

theorem Yr_coord_bounds {r s t : ℝ} (h : (s, t) ∈ Yr r) :
    1 - s < t ∧ t ≤ 1 ∧ s ≤ r ∧ 0 < s ∧ 0 < t ∧ s ≤ 1 ∧ 1 < s + t := by
  rcases mem_Yr.1 h with ⟨hΩ, hs⟩
  rcases mem_Omega.1 hΩ with ⟨hs0, hs1, ht0, ht1, hsum⟩
  exact ⟨by linarith, ht1, hs, hs0, ht0, hs1, hsum⟩

/-- The inverse inequalities of paper S2.p6. -/
theorem phiRInv_inequalities {r s t : ℝ} (_hr : 0 < r) (_hr1 : r < 1)
    (h : (s, t) ∈ Yr r) :
    r - s < t - ((Int.ceil ((t - r) / s) : ℤ) : ℝ) * s ∧
      t - ((Int.ceil ((t - r) / s) : ℤ) : ℝ) * s ≤ r ∧ 1 - s < t ∧ t ≤ 1 := by
  obtain ⟨h1, h2, _, hs0, _, _, _⟩ := Yr_coord_bounds h
  have hb := ceil_sub_bounds (s := s) (t := t) (r := r) hs0
  exact ⟨hb.1, hb.2, h1, h2⟩

/-- From the inverse inequalities, `(a,b) = (s/r, (t-js)/r)` lies in `Ω`. -/
theorem phiRInv_mem_Omega {r s t : ℝ} (hr : 0 < r) (_hr1 : r < 1)
    (h : (s, t) ∈ Yr r) :
    (s / r, (t - ((Int.ceil ((t - r) / s) : ℤ) : ℝ) * s) / r) ∈ Omega := by
  obtain ⟨h1, ht1, hs, hs0, ht0, hs1, hsum⟩ := Yr_coord_bounds h
  have hb := ceil_sub_bounds (s := s) (t := t) (r := r) hs0
  have hne : r ≠ 0 := ne_of_gt hr
  rw [mem_Omega]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact div_pos hs0 hr
  · exact (div_le_one hr).2 hs
  · exact div_pos (by linarith) hr
  · exact (div_le_one hr).2 hb.2
  · have hadd :
        s / r + (t - ((Int.ceil ((t - r) / s) : ℤ) : ℝ) * s) / r
          = (s + t - ((Int.ceil ((t - r) / s) : ℤ) : ℝ) * s) / r := by
      field_simp [hne]
      ring
    rw [hadd]
    have hnum : r < s + t - ((Int.ceil ((t - r) / s) : ℤ) : ℝ) * s := by linarith
    exact (one_lt_div hr).2 hnum

/-! ## Algebraic inverse identities -/

theorem phiRInv_phiR {r a b : ℝ} (hr : 0 < r) (_hr1 : r < 1)
    (hx : (a, b) ∈ Omega) : phiRInv r (phiR r (a, b)) = (a, b) := by
  rcases mem_Omega.1 hx with ⟨ha0, ha1, hb0, hb1, hsum⟩
  have ha : 0 < a := ha0
  have hne : r ≠ 0 := ne_of_gt hr
  have hdiv :
      (r * (b + ((phiJ r a b : ℤ) : ℝ) * a) - r) / (r * a)
        = ((phiJ r a b : ℤ) : ℝ) + (b - 1) / a := by
    field_simp [hne, ne_of_gt ha]
    ring
  have hz : ⌈(b - 1) / a⌉ = 0 := by
    rw [Int.ceil_eq_zero_iff, mem_Ioc]
    refine ⟨?_, ?_⟩
    · have ha0 : a ≠ 0 := ne_of_gt ha
      have h : (-1 : ℝ) * a < b - 1 := by linarith
      have hdiv' : ((-1 : ℝ) * a) / a < (b - 1) / a :=
        (div_lt_div_iff_of_pos_right ha).2 h
      have heq : ((-1 : ℝ) * a) / a = -1 := by field_simp [ha0]
      rw [heq] at hdiv'
      exact hdiv'
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt ha)
  have hceil : Int.ceil ((r * (b + ((phiJ r a b : ℤ) : ℝ) * a) - r) / (r * a))
      = phiJ r a b := by
    rw [hdiv]
    have hswap : ((phiJ r a b : ℤ) : ℝ) + (b - 1) / a
        = (b - 1) / a + ((phiJ r a b : ℤ) : ℝ) := add_comm _ _
    have hadd : ⌈((phiJ r a b : ℤ) : ℝ) + (b - 1) / a⌉
        = (phiJ r a b : ℤ) + ⌈(b - 1) / a⌉ := by
      rw [hswap, Int.ceil_add_intCast, add_comm]
    rw [hadd, hz, add_zero]
  have hform :
      phiRInv r (phiR r (a, b))
        = ((r * a) / r,
          (r * (b + ((phiJ r a b : ℤ) : ℝ) * a)
            - ((Int.ceil ((r * (b + ((phiJ r a b : ℤ) : ℝ) * a) - r) / (r * a)) : ℤ) : ℝ)
              * (r * a)) / r) := rfl
  rw [hform, hceil]
  refine Prod.ext ?_ ?_
  · field_simp [hne]
  · field_simp [hne, ne_of_gt ha]
    ring

theorem phiR_phiRInv {r s t : ℝ} (hr : 0 < r) (_hr1 : r < 1)
    (h : (s, t) ∈ Yr r) : phiR r (phiRInv r (s, t)) = (s, t) := by
  obtain ⟨h1, ht1, hs, hs0, ht0, hs1, hsum⟩ := Yr_coord_bounds h
  have hne : r ≠ 0 := ne_of_gt hr
  have hsne : s ≠ 0 := ne_of_gt hs0
  have hdiv :
      (r⁻¹ - (t - ((Int.ceil ((t - r) / s) : ℤ) : ℝ) * s) / r) / (s / r)
        = ((Int.ceil ((t - r) / s) : ℤ) : ℝ) + (1 - t) / s := by
    field_simp [hne, hsne]
    ring
  have hfloor : ⌊(r⁻¹ - (t - ((Int.ceil ((t - r) / s) : ℤ) : ℝ) * s) / r) / (s / r)⌋
      = Int.ceil ((t - r) / s) := by
    rw [hdiv]
    have hz : ⌊(1 - t) / s⌋ = 0 := by
      rw [Int.floor_eq_zero_iff, mem_Ico]
      exact ⟨div_nonneg (by linarith) (le_of_lt hs0), (div_lt_one hs0).2 (by linarith)⟩
    have hadd : ⌊((Int.ceil ((t - r) / s) : ℤ) : ℝ) + (1 - t) / s⌋
        = (Int.ceil ((t - r) / s) : ℤ) + ⌊(1 - t) / s⌋ :=
      Int.floor_intCast_add _ _
    rw [hadd, hz]
    exact add_zero _
  have hinv :
      phiRInv r (s, t)
        = (s / r, (t - ((Int.ceil ((t - r) / s) : ℤ) : ℝ) * s) / r) := rfl
  have hjphi : phiJ r (s / r) ((t - ((Int.ceil ((t - r) / s) : ℤ) : ℝ) * s) / r)
      = Int.ceil ((t - r) / s) := by
    rw [phiJ_apply, hfloor]
  rw [hinv, phiR_eq', hjphi]
  refine Prod.ext ?_ ?_
  · field_simp [hne]
  · field_simp [hne, hsne]
    ring

/-! ## Statement forms (Lemma 2) -/

/-- Lemma 2, first half: `φ_r : Ω → Y_r` is an almost-everywhere bijection. -/
def Lemma2BijectionStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1 →
    (∀ x ∈ Omega, phiR r x ∈ Yr r) ∧
      (∀ x ∈ Omega, phiRInv r (phiR r x) = x) ∧
        (∀ y ∈ Yr r, phiR r (phiRInv r y) = y)

theorem Lemma2Bijection : Lemma2BijectionStatement := by
  intro r hr hr1
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hx' : (x.1, x.2) ∈ Omega := by rwa [← Prod.eta x]
    have := phiR_mem_Yr hr hr1 hx'
    rwa [← Prod.eta x]
  · intro x hx
    have hx' : (x.1, x.2) ∈ Omega := by rwa [← Prod.eta x]
    have := phiRInv_phiR hr hr1 hx'
    rwa [← Prod.eta x]
  · intro y hy
    have hy' : (y.1, y.2) ∈ Yr r := by rwa [← Prod.eta y]
    have := phiR_phiRInv hr hr1 hy'
    rwa [← Prod.eta y]

/-- Lemma 2: pushforward `(φ_r)_* m = m_r`. -/
def Lemma2PushforwardStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1 →
    MeasurePreserving (phiR r) m (mr r)

/-- Lemma 2: conjugacy `B_r ∘ φ_r = φ_r ∘ B`. -/
def Lemma2ConjugacyStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1 → ∀ x ∈ Omega,
    inducedMap B (Yr r) (phiR r x) = phiR r (B x)

/-- Lemma 2: `φ_r → id` in `m`-measure as `r ↑ 1`. -/
def Lemma2ConvergenceStatement : Prop :=
  TendstoInMeasure m phiR (𝓝[<] (1 : ℝ)) id

/-- Lemma 2, equation (3): `H_{r,n}(φ_r x) = r^{-2} H_n(x)`. -/
def Lemma2TimeScalingStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1 → ∀ n : ℕ, ∀ x ∈ Omega,
    Hr r n (phiR r x) = r⁻¹ ^ 2 * H n x

/-! ## Time scaling: `h_u g_r = g_r h_{r^2 u}` (paper S2.p7) -/

/-- Diagonal map `g_r = diag(r, r^{-1})` on `ℝ²`. -/
noncomputable def gMap (r : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (r * x.1, r⁻¹ * x.2)

/-- Horocycle map `h_u = [[1,0],[-u,1]]` on `ℝ²`. -/
def hMap (u : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (x.1, x.2 - u * x.1)

theorem gMap_apply (r x1 x2 : ℝ) : gMap r (x1, x2) = (r * x1, r⁻¹ * x2) := rfl

theorem hMap_apply (u x1 x2 : ℝ) : hMap u (x1, x2) = (x1, x2 - u * x1) := rfl

/-- Pointwise identity `h_u ∘ g_r = g_r ∘ h_{r^2 u}`. -/
theorem hMap_gMap (u r : ℝ) (hr : r ≠ 0) (x : ℝ × ℝ) :
    hMap u (gMap r x) = gMap r (hMap (r ^ 2 * u) x) := by
  rcases x with ⟨x1, x2⟩
  simp only [gMap_apply, hMap_apply]
  refine Prod.ext ?_ ?_
  · ring
  · field_simp [hr]

/-- Matrix `g_r = diag(r, r^{-1})`. -/
noncomputable def gMat (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![r, 0; 0, r⁻¹]

/-- Matrix `h_u = [[1,0],[-u,1]]`. -/
def hMat (u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; -u, 1]

/-- Matrix identity `h_u · g_r = g_r · h_{r^2 u}`. -/
theorem hMat_mul_gMat (u r : ℝ) (hr : r ≠ 0) :
    hMat u * gMat r = gMat r * hMat (r ^ 2 * u) := by
  have h1 : hMat u * gMat r = !![r, 0; -u * r, r⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, hMat, gMat]
  have h2 : gMat r * hMat (r ^ 2 * u) = !![r, 0; -u * r, r⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, hMat, gMat, sq, mul_assoc, mul_comm,
        mul_inv_cancel₀ hr]
  rw [h1, h2]

/-- Determinant of `g_r` is `1`. -/
theorem gMat_det (r : ℝ) (hr : r ≠ 0) : (gMat r).det = 1 := by
  unfold gMat
  rw [Matrix.det_fin_two_of]
  rw [mul_inv_cancel₀ hr]
  ring

/-- Determinant of `h_u` is `1`. -/
theorem hMat_det (u : ℝ) : (hMat u).det = 1 := by
  unfold hMat
  rw [Matrix.det_fin_two_of]
  ring

end Paper14

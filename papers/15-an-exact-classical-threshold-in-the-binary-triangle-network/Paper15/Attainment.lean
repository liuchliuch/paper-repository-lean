import Paper15.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Section 2: Attainment of the threshold

We verify the attaining construction of the paper: the exceptional table `F`
together with the i.i.d. ternary source law `(x, y, z)` of (8), where `y` is
the unique root in `(3/8, 2/5)` of the quartic `4y⁴ - 8y + 3 = 0`.

Main results:
* `exists_unique_y`, `yRoot`: existence and uniqueness of the quartic root;
* positivity `xAtt_pos`, `yAtt_pos`, `zAtt_pos` of the source law;
* `detMoments_exceptional_iid` / `detMoments_exceptional_simplex`: the finite
  moments of `DetTriangle.exceptional` match equations (10);
* substitution identities of (11) and (12);
* `thresholdPoly_of_yQuartic`: the attained value `t = 1/y + 2y - 3` is a root
  of the threshold polynomial (13), and lies in `(9/25, 37/100) = (0.36, 0.37)`;
* `AggregateMoments.scaleSigns`: independent sign noise of mean `η` scales the
  aggregate moments by `η, η², η³`, which yields `p_t` for all `t ∈ [0, t*]`.
-/

noncomputable section

namespace Paper15

open Finset Real Polynomial BigOperators

/-! ## Equation (7): the quartic root -/

/-- Equation (7): `4y⁴ - 8y + 3 = 0`. -/
def yQuartic (y : ℝ) : ℝ := 4 * y ^ 4 - 8 * y + 3

lemma yQuartic_eq (y : ℝ) : yQuartic y = 4 * y ^ 4 - 8 * y + 3 := rfl

lemma continuous_yQuartic : Continuous yQuartic := by
  have h : yQuartic = fun y => 4 * y ^ 4 - 8 * y + 3 := rfl
  rw [h]; continuity

lemma hasDerivAt_yQuartic (x : ℝ) : HasDerivAt yQuartic (16 * x ^ 3 - 8) x := by
  have d1 := (hasDerivAt_pow 4 x).const_mul (4:ℝ)
  have d2 := (hasDerivAt_id x).const_mul (-8:ℝ)
  have d3 := hasDerivAt_const x (3:ℝ)
  have d := d1.add (d2.add d3)
  norm_num at d
  -- `d` has derivative `4 * (4 * x ^ 3) + -8`
  have ederiv : (4 * (4 * x ^ 3) + (-8 : ℝ)) = 16 * x ^ 3 - 8 := by ring
  have efun : (fun y : ℝ => 4 * y ^ 4) + ((fun y => -(8 * y)) + fun _ => (3:ℝ))
      = yQuartic := by
    funext y
    simp only [Pi.add_apply]
    rw [yQuartic]
    ring
  rw [ederiv] at d
  rw [← efun]
  exact d

lemma deriv_yQuartic (x : ℝ) : deriv yQuartic x = 16 * x ^ 3 - 8 :=
  (hasDerivAt_yQuartic x).deriv

lemma yQuartic_at_three_div_eight : yQuartic (3 / 8) = 81 / 1024 := by
  norm_num [yQuartic]

lemma yQuartic_at_two_div_five : yQuartic (2 / 5) = -61 / 625 := by
  norm_num [yQuartic]

lemma yQuartic_strictAntiOn : StrictAntiOn yQuartic (Set.Ioo (3 / 8 : ℝ) (2 / 5)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _) continuous_yQuartic.continuousOn
  intro x hx
  rw [interior_Ioo] at hx
  rw [deriv_yQuartic]
  have hx1 : x < 2 / 5 := hx.2
  have hx0 : (0:ℝ) < x := lt_trans (by norm_num) hx.1
  have hlt : x ^ 3 < (2 / 5 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hx1 hx0.le (by norm_num)
  have h16 : (16:ℝ) * x ^ 3 < 16 * (2 / 5) ^ 3 := by gcongr
  have hval : (16:ℝ) * (2 / 5) ^ 3 = 128 / 125 := by norm_num
  rw [hval] at h16
  have : (128 / 125 : ℝ) < 8 := by norm_num
  linarith

lemma yQuartic_exists : ∃ y ∈ Set.Ioo (3 / 8 : ℝ) (2 / 5), yQuartic y = 0 := by
  have hle : (3 / 8 : ℝ) ≤ 2 / 5 := by norm_num
  have hcont : ContinuousOn yQuartic (Set.Icc (3 / 8 : ℝ) (2 / 5)) :=
    continuous_yQuartic.continuousOn
  have hy : (0:ℝ) ∈ Set.Icc (yQuartic (2 / 5)) (yQuartic (3 / 8)) := by
    rw [yQuartic_at_two_div_five, yQuartic_at_three_div_eight]
    norm_num
  have hmem : (0:ℝ) ∈ yQuartic '' Set.Icc (3 / 8 : ℝ) (2 / 5) :=
    intermediate_value_Icc' hle hcont hy
  obtain ⟨y, hy_mem, hey⟩ : ∃ y ∈ Set.Icc (3 / 8 : ℝ) (2 / 5), yQuartic y = 0 := by
    simpa [Set.mem_image] using hmem
  have y_ne_lo : y ≠ 3 / 8 := by
    rintro rfl
    rw [yQuartic_at_three_div_eight] at hey
    norm_num at hey
  have y_ne_hi : y ≠ 2 / 5 := by
    rintro rfl
    rw [yQuartic_at_two_div_five] at hey
    norm_num at hey
  exact ⟨y, ⟨lt_of_le_of_ne hy_mem.1 y_ne_lo.symm, lt_of_le_of_ne hy_mem.2 y_ne_hi⟩, hey⟩

/-- Equation (7): there is a unique root of `yQuartic` in `(3/8, 2/5)`. -/
theorem exists_unique_y : ∃! y : ℝ, y ∈ Set.Ioo (3 / 8) (2 / 5) ∧ yQuartic y = 0 := by
  obtain ⟨y, hy, hey⟩ := yQuartic_exists
  refine ⟨y, ⟨hy, hey⟩, ?_⟩
  intro y' hy'
  exact (yQuartic_strictAntiOn.injOn hy hy'.1 (hey.trans hy'.2.symm)).symm

/-- The unique root of (7) in `(3/8, 2/5)`. -/
def yRoot : ℝ := Exists.choose exists_unique_y

lemma yRoot_spec' :
    (yRoot ∈ Set.Ioo (3 / 8 : ℝ) (2 / 5) ∧ yQuartic yRoot = 0) ∧
      ∀ y', y' ∈ Set.Ioo (3 / 8 : ℝ) (2 / 5) ∧ yQuartic y' = 0 → y' = yRoot :=
  Exists.choose_spec exists_unique_y

lemma yRoot_mem_Ioo : yRoot ∈ Set.Ioo (3 / 8 : ℝ) (2 / 5) := yRoot_spec'.1.1

lemma yRoot_quartic : yQuartic yRoot = 0 := yRoot_spec'.1.2

lemma yRoot_pos : (0:ℝ) < yRoot := lt_trans (by norm_num) yRoot_mem_Ioo.1

lemma yRoot_ne_zero : yRoot ≠ 0 := yRoot_pos.ne'

lemma yRoot_lt_two_div_five : yRoot < 2 / 5 := yRoot_mem_Ioo.2

lemma yRoot_gt_three_div_eight : (3 / 8 : ℝ) < yRoot := yRoot_mem_Ioo.1

/-! ## Equation (8): the attaining source law -/

/-- `x = (1 - 2y²)/(4y)` of (8). -/
def xOfY (y : ℝ) : ℝ := (1 - 2 * y ^ 2) / (4 * y)

/-- Attaining source probability `x` of (8). -/
def xAtt : ℝ := xOfY yRoot

/-- Attaining source probability `y` of (8). -/
def yAtt : ℝ := yRoot

/-- Attaining source probability `z = 1 - x - y` of (8). -/
def zAtt : ℝ := 1 - xAtt - yAtt

lemma xOfY_pos {y : ℝ} (hy : y ∈ Set.Ioo (3 / 8 : ℝ) (2 / 5)) : 0 < xOfY y := by
  have hy0 : (0:ℝ) < y := lt_trans (by norm_num) hy.1
  have hy1 : y < 2 / 5 := hy.2
  have hs : (0:ℝ) < 1 - 2 * y ^ 2 := by
    have h : y ^ 2 < (2 / 5 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ hy1 hy0.le (by norm_num)
    have h2 : (2 / 5 : ℝ) ^ 2 = 4 / 25 := by norm_num
    rw [h2] at h
    have : (2:ℝ) * y ^ 2 < 8 / 25 := by nlinarith
    have : (8 / 25 : ℝ) < 1 := by norm_num
    linarith
  rw [xOfY]
  exact div_pos hs (by positivity)

lemma xAtt_pos : (0:ℝ) < xAtt := xOfY_pos yRoot_mem_Ioo

lemma yAtt_pos : (0:ℝ) < yAtt := yRoot_pos

lemma xOfY_add_y_lt_one {y : ℝ} (hy : y ∈ Set.Ioo (3 / 8 : ℝ) (2 / 5)) : xOfY y + y < 1 := by
  have hy0 : (0:ℝ) < y := lt_trans (by norm_num) hy.1
  have h : xOfY y + y = 1 / (4 * y) + y / 2 := by
    rw [xOfY]
    field_simp [hy0.ne']
    ring
  have h1 : 1 / (4 * y) < (2:ℝ) / 3 := by
    have h4y : (0:ℝ) < 4 * y := by positivity
    have h38 : (3 / 8 : ℝ) < y := hy.1
    rw [div_lt_iff₀ h4y]
    nlinarith
  have h2 : y / 2 < (1:ℝ) / 5 := by
    rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 2)]
    have : (1:ℝ) / 5 * 2 = 2 / 5 := by ring
    rw [this]
    exact hy.2
  have hsum : (2:ℝ) / 3 + 1 / 5 = 13 / 15 := by norm_num
  have h13 : (13 / 15 : ℝ) < 1 := by norm_num
  rw [h]
  linarith

lemma xAtt_add_yAtt_lt_one : xAtt + yAtt < 1 :=
  xOfY_add_y_lt_one yRoot_mem_Ioo

lemma zAtt_pos : (0:ℝ) < zAtt := by
  have h : xAtt + yAtt < 1 := xAtt_add_yAtt_lt_one
  simp only [zAtt]
  linarith

lemma xAtt_add_yAtt_add_zAtt : xAtt + yAtt + zAtt = 1 := by
  rw [zAtt]; ring

lemma xAtt_ne_zero : xAtt ≠ 0 := xAtt_pos.ne'

lemma xOfY_ne_zero {y : ℝ} (hy : y ∈ Set.Ioo (3 / 8 : ℝ) (2 / 5)) : xOfY y ≠ 0 :=
  (xOfY_pos hy).ne'

/-! ## Finite moments of the exceptional table (equations 10) -/

/-- Ternary probability law on `Fin 3` with weights `(x, y, z)`. -/
def law3 (x y z : ℝ) : Fin 3 → ℝ := fun i => if i = 0 then x else if i = 1 then y else z

@[simp] lemma law3_zero (x y z : ℝ) : law3 x y z 0 = x := by
  simp [law3]
@[simp] lemma law3_one (x y z : ℝ) : law3 x y z 1 = y := by
  simp [law3]
@[simp] lemma law3_two (x y z : ℝ) : law3 x y z 2 = z := by
  simp [law3]

/-- The exceptional table `F` on the nine pairs of `Fin 3`. -/
@[simp] lemma exceptionalTable_00 : DetTriangle.exceptionalTable 0 0 = (-1 : ℝ) := by
  simp [DetTriangle.exceptionalTable]
@[simp] lemma exceptionalTable_01 : DetTriangle.exceptionalTable 0 1 = (1 : ℝ) := by
  simp [DetTriangle.exceptionalTable]
@[simp] lemma exceptionalTable_02 : DetTriangle.exceptionalTable 0 2 = (-1 : ℝ) := by
  simp [DetTriangle.exceptionalTable]
@[simp] lemma exceptionalTable_10 : DetTriangle.exceptionalTable 1 0 = (1 : ℝ) := by
  simp [DetTriangle.exceptionalTable]
@[simp] lemma exceptionalTable_11 : DetTriangle.exceptionalTable 1 1 = (1 : ℝ) := by
  simp [DetTriangle.exceptionalTable]
@[simp] lemma exceptionalTable_12 : DetTriangle.exceptionalTable 1 2 = (-1 : ℝ) := by
  simp [DetTriangle.exceptionalTable]
@[simp] lemma exceptionalTable_20 : DetTriangle.exceptionalTable 2 0 = (-1 : ℝ) := by
  simp [DetTriangle.exceptionalTable]
@[simp] lemma exceptionalTable_21 : DetTriangle.exceptionalTable 2 1 = (-1 : ℝ) := by
  simp [DetTriangle.exceptionalTable]
@[simp] lemma exceptionalTable_22 : DetTriangle.exceptionalTable 2 2 = (-1 : ℝ) := by
  simp [DetTriangle.exceptionalTable]

/-- Unconstrained one-body expectation `E[A]` for the exceptional table
(with i.i.d. law `(x,y,z)`, no simplex constraint). -/
lemma eA_exceptional (x y z : ℝ) :
    (∑ i, ∑ j, ∑ k, law3 x y z i * law3 x y z j * law3 x y z k * DetTriangle.exceptional.A j k)
      = (x + y + z) * (-x ^ 2 + 2 * x * y - 2 * x * z + y ^ 2 - 2 * y * z - z ^ 2) := by
  simp [Fin.sum_univ_three, DetTriangle.exceptional_A, law3]
  ring

/-- Unconstrained one-body expectation `E[B]` for the exceptional table. -/
lemma eB_exceptional (x y z : ℝ) :
    (∑ i, ∑ j, ∑ k, law3 x y z i * law3 x y z j * law3 x y z k * DetTriangle.exceptional.B k i)
      = (x + y + z) * (-x ^ 2 + 2 * x * y - 2 * x * z + y ^ 2 - 2 * y * z - z ^ 2) := by
  simp [Fin.sum_univ_three, DetTriangle.exceptional_B, law3]
  ring

/-- Unconstrained one-body expectation `E[C]` for the exceptional table. -/
lemma eC_exceptional (x y z : ℝ) :
    (∑ i, ∑ j, ∑ k, law3 x y z i * law3 x y z j * law3 x y z k * DetTriangle.exceptional.C i j)
      = (x + y + z) * (-x ^ 2 + 2 * x * y - 2 * x * z + y ^ 2 - 2 * y * z - z ^ 2) := by
  simp [Fin.sum_univ_three, DetTriangle.exceptional_C, law3]
  ring

/-- Unconstrained pair expectation `E[AB]` for the exceptional table. -/
lemma eAB_exceptional (x y z : ℝ) :
    (∑ i, ∑ j, ∑ k, law3 x y z i * law3 x y z j * law3 x y z k *
      (DetTriangle.exceptional.A j k * DetTriangle.exceptional.B k i))
      = x ^ 3 - x ^ 2 * y + 3 * x ^ 2 * z + 3 * x * y ^ 2 - 2 * x * y * z + 3 * x * z ^ 2
        + y ^ 3 - y ^ 2 * z + 3 * y * z ^ 2 + z ^ 3 := by
  simp [Fin.sum_univ_three, DetTriangle.exceptional_A, DetTriangle.exceptional_B, law3]
  ring

/-- Unconstrained pair expectation `E[BC]` for the exceptional table. -/
lemma eBC_exceptional (x y z : ℝ) :
    (∑ i, ∑ j, ∑ k, law3 x y z i * law3 x y z j * law3 x y z k *
      (DetTriangle.exceptional.B k i * DetTriangle.exceptional.C i j))
      = x ^ 3 - x ^ 2 * y + 3 * x ^ 2 * z + 3 * x * y ^ 2 - 2 * x * y * z + 3 * x * z ^ 2
        + y ^ 3 - y ^ 2 * z + 3 * y * z ^ 2 + z ^ 3 := by
  simp [Fin.sum_univ_three, DetTriangle.exceptional_B, DetTriangle.exceptional_C, law3]
  ring

/-- Unconstrained pair expectation `E[CA]` for the exceptional table. -/
lemma eCA_exceptional (x y z : ℝ) :
    (∑ i, ∑ j, ∑ k, law3 x y z i * law3 x y z j * law3 x y z k *
      (DetTriangle.exceptional.C i j * DetTriangle.exceptional.A j k))
      = x ^ 3 - x ^ 2 * y + 3 * x ^ 2 * z + 3 * x * y ^ 2 - 2 * x * y * z + 3 * x * z ^ 2
        + y ^ 3 - y ^ 2 * z + 3 * y * z ^ 2 + z ^ 3 := by
  simp [Fin.sum_univ_three, DetTriangle.exceptional_C, DetTriangle.exceptional_A, law3]
  ring

/-- Unconstrained three-body expectation `E[ABC]` for the exceptional table. -/
lemma eABC_exceptional (x y z : ℝ) :
    (∑ i, ∑ j, ∑ k, law3 x y z i * law3 x y z j * law3 x y z k *
      (DetTriangle.exceptional.A j k * DetTriangle.exceptional.B k i * DetTriangle.exceptional.C i j))
      = -x ^ 3 - 3 * x ^ 2 * y - 3 * x ^ 2 * z + 3 * x * y ^ 2 + 6 * x * y * z - 3 * x * z ^ 2
        + y ^ 3 + 3 * y ^ 2 * z - 3 * y * z ^ 2 - z ^ 3 := by
  simp [Fin.sum_univ_three, DetTriangle.exceptional_A, DetTriangle.exceptional_B,
    DetTriangle.exceptional_C, law3]
  ring

lemma detMoments_M1' (x y z : ℝ) :
    (detMoments DetTriangle.exceptional (law3 x y z) (law3 x y z) (law3 x y z)).M1
      = ((∑ i, ∑ j, ∑ k, law3 x y z i * law3 x y z j * law3 x y z k
            * DetTriangle.exceptional.A j k)
        + (∑ i, ∑ j, ∑ k, law3 x y z i * law3 x y z j * law3 x y z k
            * DetTriangle.exceptional.B k i)
        + (∑ i, ∑ j, ∑ k, law3 x y z i * law3 x y z j * law3 x y z k
            * DetTriangle.exceptional.C i j)) / 3 := rfl

lemma detMoments_M2' (x y z : ℝ) :
    (detMoments DetTriangle.exceptional (law3 x y z) (law3 x y z) (law3 x y z)).M2
      = ((∑ i, ∑ j, ∑ k, law3 x y z i * law3 x y z j * law3 x y z k
            * (DetTriangle.exceptional.A j k * DetTriangle.exceptional.B k i))
        + (∑ i, ∑ j, ∑ k, law3 x y z i * law3 x y z j * law3 x y z k
            * (DetTriangle.exceptional.B k i * DetTriangle.exceptional.C i j))
        + (∑ i, ∑ j, ∑ k, law3 x y z i * law3 x y z j * law3 x y z k
            * (DetTriangle.exceptional.C i j * DetTriangle.exceptional.A j k))) / 3 := rfl

lemma detMoments_M3' (x y z : ℝ) :
    (detMoments DetTriangle.exceptional (law3 x y z) (law3 x y z) (law3 x y z)).M3
      = ∑ i, ∑ j, ∑ k, law3 x y z i * law3 x y z j * law3 x y z k
          * (DetTriangle.exceptional.A j k * DetTriangle.exceptional.B k i
              * DetTriangle.exceptional.C i j) := rfl

lemma detMoments_exceptional_iid (x y z : ℝ) :
    detMoments DetTriangle.exceptional (law3 x y z) (law3 x y z) (law3 x y z)
      = ⟨(x + y + z) * (-x ^ 2 + 2 * x * y - 2 * x * z + y ^ 2 - 2 * y * z - z ^ 2),
          x ^ 3 - x ^ 2 * y + 3 * x ^ 2 * z + 3 * x * y ^ 2 - 2 * x * y * z + 3 * x * z ^ 2
            + y ^ 3 - y ^ 2 * z + 3 * y * z ^ 2 + z ^ 3,
          -x ^ 3 - 3 * x ^ 2 * y - 3 * x ^ 2 * z + 3 * x * y ^ 2 + 6 * x * y * z - 3 * x * z ^ 2
            + y ^ 3 + 3 * y ^ 2 * z - 3 * y * z ^ 2 - z ^ 3⟩ := by
  have h1 : (detMoments DetTriangle.exceptional (law3 x y z) (law3 x y z) (law3 x y z)).M1
      = (x + y + z) * (-x ^ 2 + 2 * x * y - 2 * x * z + y ^ 2 - 2 * y * z - z ^ 2) := by
    rw [detMoments_M1', eA_exceptional, eB_exceptional, eC_exceptional]
    ring
  have h2 : (detMoments DetTriangle.exceptional (law3 x y z) (law3 x y z) (law3 x y z)).M2
      = x ^ 3 - x ^ 2 * y + 3 * x ^ 2 * z + 3 * x * y ^ 2 - 2 * x * y * z + 3 * x * z ^ 2
          + y ^ 3 - y ^ 2 * z + 3 * y * z ^ 2 + z ^ 3 := by
    rw [detMoments_M2', eAB_exceptional, eBC_exceptional, eCA_exceptional]
    ring
  have h3 : (detMoments DetTriangle.exceptional (law3 x y z) (law3 x y z) (law3 x y z)).M3
      = -x ^ 3 - 3 * x ^ 2 * y - 3 * x ^ 2 * z + 3 * x * y ^ 2 + 6 * x * y * z - 3 * x * z ^ 2
          + y ^ 3 + 3 * y ^ 2 * z - 3 * y * z ^ 2 - z ^ 3 := by
    rw [detMoments_M3']
    exact eABC_exceptional x y z
  have eta : detMoments DetTriangle.exceptional (law3 x y z) (law3 x y z) (law3 x y z)
      = AggregateMoments.mk
          (detMoments DetTriangle.exceptional (law3 x y z) (law3 x y z) (law3 x y z)).M1
          (detMoments DetTriangle.exceptional (law3 x y z) (law3 x y z) (law3 x y z)).M2
          (detMoments DetTriangle.exceptional (law3 x y z) (law3 x y z) (law3 x y z)).M3 := rfl
  rw [eta, h1, h2, h3]

/-- Equation (10): with i.i.d. law `(x, y, z)` and `x + y + z = 1`, the moments of
`DetTriangle.exceptional` are exactly `exceptionalM1/M2/M3`. -/
theorem detMoments_exceptional_simplex (x y z : ℝ) (hsum : x + y + z = 1) :
    detMoments DetTriangle.exceptional (law3 x y z) (law3 x y z) (law3 x y z)
      = ⟨exceptionalM1 x y, exceptionalM2 x y, exceptionalM3 x y⟩ := by
  rw [detMoments_exceptional_iid]
  have hz : z = 1 - x - y := by linarith
  subst hz
  simp only [exceptionalM1, exceptionalM2, exceptionalM3]
  ring_nf

/-- Explicit moments of the exceptional model with law `(x, y, 1 - x - y)`. -/
theorem detMoments_exceptional_of_xy (x y : ℝ) :
    detMoments DetTriangle.exceptional (law3 x y (1 - x - y)) (law3 x y (1 - x - y))
        (law3 x y (1 - x - y))
      = ⟨exceptionalM1 x y, exceptionalM2 x y, exceptionalM3 x y⟩ :=
  detMoments_exceptional_simplex x y (1 - x - y) (by ring)

/-! ## Equation (11): substitution of (8) -/

/-- After substituting `x = (1-2y²)/(4y)`, equation (11) gives `M1 = 0`. -/
lemma exceptionalM1_subst_eq_zero {y : ℝ} (hy : y ≠ 0) :
    exceptionalM1 ((1 - 2 * y ^ 2) / (4 * y)) y = 0 := by
  rw [exceptionalM1]
  field_simp [hy]
  ring

/-- After substituting `x = (1-2y²)/(4y)`, equation (11) gives
`M2 = 1/(4y) - 1 + 2y - y³`. -/
lemma exceptionalM2_subst {y : ℝ} (hy : y ≠ 0) :
    exceptionalM2 ((1 - 2 * y ^ 2) / (4 * y)) y = exceptionalM2Sub y := by
  rw [exceptionalM2, exceptionalM2Sub]
  field_simp [hy]
  ring

/-- The closed form of `M3` in (11). -/
def exceptionalM3Sub (y : ℝ) : ℝ := 2 - 3 / (4 * y) - y ^ 3

/-- After substituting `x = (1-2y²)/(4y)`, equation (11) gives
`M3 = 2 - 3/(4y) - y³`. -/
lemma exceptionalM3_subst {y : ℝ} (hy : y ≠ 0) :
    exceptionalM3 ((1 - 2 * y ^ 2) / (4 * y)) y = exceptionalM3Sub y := by
  rw [exceptionalM3, exceptionalM3Sub]
  field_simp [hy]
  ring

lemma exceptionalM1_xAtt : exceptionalM1 xAtt yAtt = 0 := by
  rw [xAtt, yAtt, xOfY]
  exact exceptionalM1_subst_eq_zero yRoot_ne_zero

lemma exceptionalM2_xAtt : exceptionalM2 xAtt yAtt = exceptionalM2Sub yAtt := by
  rw [xAtt, yAtt, xOfY]
  exact exceptionalM2_subst yRoot_ne_zero

lemma exceptionalM3_xAtt : exceptionalM3 xAtt yAtt = exceptionalM3Sub yAtt := by
  rw [xAtt, yAtt, xOfY]
  exact exceptionalM3_subst yRoot_ne_zero

lemma detMoments_attaining :
    detMoments DetTriangle.exceptional (law3 xAtt yAtt zAtt) (law3 xAtt yAtt zAtt)
        (law3 xAtt yAtt zAtt)
      = ⟨0, exceptionalM2Sub yAtt, exceptionalM3Sub yAtt⟩ := by
  have hz : zAtt = 1 - xAtt - yAtt := rfl
  rw [hz, detMoments_exceptional_of_xy, exceptionalM1_xAtt, exceptionalM2_xAtt,
    exceptionalM3_xAtt]

/-! ## Equation (12): the quartic forces `M1 = M3 = 0` -/

/-- From `4y⁴ - 8y + 3 = 0` and `y ≠ 0` one gets `3 = 4y(2 - y³)`. -/
lemma yQuartic_factor {y : ℝ} (hy : yQuartic y = 0) (_hy0 : y ≠ 0) :
    (3:ℝ) = 4 * y * (2 - y ^ 3) := by
  have h : (4:ℝ) * y ^ 4 - 8 * y + 3 = 0 := hy
  have h3 : (3:ℝ) = 8 * y - 4 * y ^ 4 := by linarith
  rw [h3]
  ring

/-- From `4y⁴ - 8y + 3 = 0` and `y ≠ 0` one gets `3/(4y) = 2 - y³`. -/
lemma yQuartic_three_div {y : ℝ} (hy : yQuartic y = 0) (hy0 : y ≠ 0) :
    (3:ℝ) / (4 * y) = 2 - y ^ 3 := by
  have h := yQuartic_factor hy hy0
  rw [h]
  field_simp [hy0]

/-- Equation (12): the substituted `M3` vanishes under the quartic. -/
lemma exceptionalM3Sub_eq_zero {y : ℝ} (hy : yQuartic y = 0) (hy0 : y ≠ 0) :
    exceptionalM3Sub y = 0 := by
  rw [exceptionalM3Sub, yQuartic_three_div hy hy0]
  ring

/-- Equation (12): the substituted `M2` equals `1/y + 2y - 3`. -/
lemma exceptionalM2Sub_eq_final {y : ℝ} (hy : yQuartic y = 0) (hy0 : y ≠ 0) :
    exceptionalM2Sub y = exceptionalM2Final y := by
  have h3 : exceptionalM3Sub y = 0 := exceptionalM3Sub_eq_zero hy hy0
  have key : exceptionalM2Sub y = exceptionalM2Final y + exceptionalM3Sub y := by
    rw [exceptionalM2Sub, exceptionalM2Final, exceptionalM3Sub]
    field_simp [hy0]
    ring
  rw [key, h3, add_zero]

lemma exceptionalM2Sub_eq_final_of_yRoot :
    exceptionalM2Sub yRoot = exceptionalM2Final yRoot :=
  exceptionalM2Sub_eq_final yRoot_quartic yRoot_ne_zero

lemma exceptionalM3Sub_eq_zero_of_yRoot : exceptionalM3Sub yRoot = 0 :=
  exceptionalM3Sub_eq_zero yRoot_quartic yRoot_ne_zero

/-- Equation (12): the attaining model has moments
`(M1, M2, M3) = (0, 1/y + 2y - 3, 0)`. -/
theorem attaining_moments :
    detMoments DetTriangle.exceptional (law3 xAtt yAtt zAtt) (law3 xAtt yAtt zAtt)
        (law3 xAtt yAtt zAtt)
      = ⟨0, exceptionalM2Final yAtt, 0⟩ := by
  have hy : yAtt = yRoot := rfl
  rw [detMoments_attaining, hy, exceptionalM2Sub_eq_final_of_yRoot,
    exceptionalM3Sub_eq_zero_of_yRoot]

/-! ## Equation (13): elimination of `y` -/

/-- Polynomial identity underlying (13):
`y⁴ · thresholdPoly(1/y + 2y - 3) = yQuartic y · (12y⁴ - 16y³ + 1)`. -/
lemma ypow4_thresholdPoly {y : ℝ} (hy0 : y ≠ 0) :
    y ^ 4 * thresholdPoly (1 / y + 2 * y - 3) = yQuartic y * (12 * y ^ 4 - 16 * y ^ 3 + 1) := by
  rw [thresholdPoly, yQuartic]
  field_simp [hy0]
  ring

/-- Equation (13): under (7), the attained value `t = 1/y + 2y - 3` is a root of
the threshold polynomial. -/
theorem thresholdPoly_of_yQuartic {y : ℝ} (hy : yQuartic y = 0) (hy0 : y ≠ 0) :
    thresholdPoly (1 / y + 2 * y - 3) = 0 := by
  have h := ypow4_thresholdPoly hy0
  rw [hy, zero_mul] at h
  have hy4 : y ^ 4 ≠ 0 := pow_ne_zero _ hy0
  exact (mul_eq_zero.mp h).resolve_left hy4

/-- The attained value at `yRoot` is a root of `thresholdPoly`. -/
theorem thresholdPoly_yRoot : thresholdPoly (1 / yRoot + 2 * yRoot - 3) = 0 :=
  thresholdPoly_of_yQuartic yRoot_quartic yRoot_ne_zero

/-- The attained value of (12) is a root of `thresholdPoly`. -/
theorem thresholdPoly_attained :
    thresholdPoly (exceptionalM2Final yRoot) = 0 := by
  rw [exceptionalM2Final]
  exact thresholdPoly_yRoot

/-! ## Numerical bounds `t ∈ (0.36, 0.37)` -/

lemma yQuartic_at_3861 : yQuartic (3861 / 10000) = 228219397041 / 2500000000000000 := by
  norm_num [yQuartic]

lemma yQuartic_at_3862 : yQuartic (3862 / 10000) = -96341404879 / 156250000000000 := by
  norm_num [yQuartic]

lemma yRoot_bnds : (3861 / 10000 : ℝ) < yRoot ∧ yRoot < 3862 / 10000 := by
  have anti := yQuartic_strictAntiOn
  have mem_lo : (3861 / 10000 : ℝ) ∈ Set.Ioo (3 / 8) (2 / 5) := by norm_num
  have mem_hi : (3862 / 10000 : ℝ) ∈ Set.Ioo (3 / 8) (2 / 5) := by norm_num
  have memR := yRoot_mem_Ioo
  have hlo : yQuartic (3861 / 10000) > 0 := by
    rw [yQuartic_at_3861]; norm_num
  have hhi : yQuartic (3862 / 10000) < 0 := by
    rw [yQuartic_at_3862]; norm_num
  constructor
  · -- `yQuartic yRoot < yQuartic (3861/10000) ↔ 3861/10000 < yRoot`
    have h := anti.lt_iff_gt memR mem_lo
    rw [yRoot_quartic] at h
    exact h.mp (by linarith)
  · -- `yQuartic (3862/10000) < yQuartic yRoot ↔ yRoot < 3862/10000`
    have h := anti.lt_iff_gt mem_hi memR
    rw [yRoot_quartic] at h
    exact h.mp (by linarith)

lemma yRoot_gt_3861 : (3861 / 10000 : ℝ) < yRoot := yRoot_bnds.1

lemma yRoot_lt_3862 : yRoot < 3862 / 10000 := yRoot_bnds.2

/-- Exact rational evaluations place the attained value in `(0.36, 0.37)`. -/
theorem attained_t_bounds :
    (9 / 25 : ℝ) < 1 / yRoot + 2 * yRoot - 3 ∧ 1 / yRoot + 2 * yRoot - 3 < 37 / 100 := by
  have hy0 : (0:ℝ) < yRoot := yRoot_pos
  have h1 : (3861 / 10000 : ℝ) < yRoot := yRoot_gt_3861
  have h2 : yRoot < 3862 / 10000 := yRoot_lt_3862
  have hlo : (1 / (3862 / 10000 : ℝ)) < 1 / yRoot :=
    one_div_lt_one_div_of_lt hy0 h2
  have hhi : 1 / yRoot < (1 / (3861 / 10000 : ℝ)) :=
    one_div_lt_one_div_of_lt (by norm_num : (0:ℝ) < 3861 / 10000) h1
  have e1 : (1 / (3862 / 10000 : ℝ)) = 10000 / 3862 := by field_simp
  have e2 : (1 / (3861 / 10000 : ℝ)) = 10000 / 3861 := by field_simp
  rw [e1] at hlo
  rw [e2] at hhi
  have h2lo : 2 * yRoot > (2 * 3861 / 10000 : ℝ) := by nlinarith
  have h2hi : 2 * yRoot < (2 * 3862 / 10000 : ℝ) := by nlinarith
  constructor
  · have : (10000 / 3862 : ℝ) + 2 * 3861 / 10000 - 3 > 9 / 25 := by norm_num
    linarith
  · have : (10000 / 3861 : ℝ) + 2 * 3862 / 10000 - 3 < 37 / 100 := by norm_num
    linarith

lemma thresholdPoly_at_nineTwentyFifths : thresholdPoly (9 / 25) = -19392 / 390625 := by
  norm_num [thresholdPoly]

lemma thresholdPoly_at_37_100 : thresholdPoly (37 / 100) = 18990883 / 100000000 := by
  norm_num [thresholdPoly]

lemma hasDerivAt_thresholdPoly_att (t : ℝ) :
    HasDerivAt thresholdPoly (12 * t ^ 3 + 84 * t ^ 2 + 132 * t - 36) t := by
  have d1 := (hasDerivAt_pow 4 t).const_mul (3:ℝ)
  have d2 := (hasDerivAt_pow 3 t).const_mul (28:ℝ)
  have d3 := (hasDerivAt_pow 2 t).const_mul (66:ℝ)
  have d4 := (hasDerivAt_id t).const_mul (-36:ℝ)
  have d5 := hasDerivAt_const t (3:ℝ)
  have d := d1.add (d2.add (d3.add (d4.add d5)))
  norm_num at d
  have ederiv : ((3:ℝ) * (4 * t ^ 3) + (28 * (3 * t ^ 2) + (66 * (2 * t) + -36)))
      = 12 * t ^ 3 + 84 * t ^ 2 + 132 * t - 36 := by ring
  have efun : (fun t : ℝ => 3 * t ^ 4) + ((fun t => 28 * t ^ 3)
      + ((fun t => 66 * t ^ 2) + ((fun t => -(36 * t)) + fun _ => (3:ℝ))))
      = thresholdPoly := by
    funext s
    simp only [Pi.add_apply]
    rw [thresholdPoly]
    ring
  rw [ederiv] at d
  rw [← efun]
  exact d

lemma deriv_thresholdPoly_att (t : ℝ) :
    deriv thresholdPoly t = 12 * t ^ 3 + 84 * t ^ 2 + 132 * t - 36 :=
  (hasDerivAt_thresholdPoly_att t).deriv

lemma continuous_thresholdPoly_att : Continuous thresholdPoly := by
  have h : thresholdPoly = fun t => 3 * t ^ 4 + 28 * t ^ 3 + 66 * t ^ 2 - 36 * t + 3 := rfl
  rw [h]; continuity

/-- The derivative `12t³ + 84t² + 132t - 36` is positive on `[9/25, 37/100]`. -/
lemma thresholdPoly_deriv_pos_att {t : ℝ} (ht : (9 / 25 : ℝ) ≤ t) (_ht' : t ≤ 37 / 100) :
    (0:ℝ) < 12 * t ^ 3 + 84 * t ^ 2 + 132 * t - 36 := by
  have t0 : (0:ℝ) < t := lt_of_lt_of_le (by norm_num) ht
  have key : (12:ℝ) * t ^ 3 + 84 * t ^ 2 + 132 * t - 36 = 12 * t * (t ^ 2 + 7 * t + 11) - 36 := by
    ring
  rw [key]
  have h11 : (11:ℝ) ≤ t ^ 2 + 7 * t + 11 := by nlinarith [sq_nonneg t]
  have h12 : (12:ℝ) * (9 / 25) ≤ 12 * t := by nlinarith
  have hprod : (12:ℝ) * (9 / 25) * 11 ≤ 12 * t * (t ^ 2 + 7 * t + 11) :=
    mul_le_mul h12 h11 (by norm_num : (0:ℝ) ≤ 11) (by nlinarith)
  have hval : (12:ℝ) * (9 / 25) * 11 > 36 := by norm_num
  nlinarith

lemma thresholdPoly_strictMonoOn_att : StrictMonoOn thresholdPoly (Set.Icc (9 / 25) (37 / 100)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) continuous_thresholdPoly_att.continuousOn
  intro t ht
  rw [interior_Icc] at ht
  rw [deriv_thresholdPoly_att]
  exact thresholdPoly_deriv_pos_att ht.1.le ht.2.le

/-- `thresholdPoly` has a unique root in `(0.36, 0.37) = (9/25, 37/100)`. -/
theorem exists_unique_threshold_root :
    ∃! t : ℝ, t ∈ Set.Ioo (9 / 25) (37 / 100) ∧ thresholdPoly t = 0 := by
  have hlo : thresholdPoly (9 / 25) < 0 := by
    rw [thresholdPoly_at_nineTwentyFifths]; norm_num
  have hhi : thresholdPoly (37 / 100) > 0 := by
    rw [thresholdPoly_at_37_100]; norm_num
  have hle : (9 / 25 : ℝ) ≤ 37 / 100 := by norm_num
  have hcont : ContinuousOn thresholdPoly (Set.Icc (9 / 25) (37 / 100)) :=
    continuous_thresholdPoly_att.continuousOn
  have hy : (0:ℝ) ∈ Set.Icc (thresholdPoly (9 / 25)) (thresholdPoly (37 / 100)) := by
    constructor <;> linarith
  have hmem : (0:ℝ) ∈ thresholdPoly '' Set.Icc (9 / 25) (37 / 100) :=
    intermediate_value_Icc hle hcont hy
  obtain ⟨t, ht_mem, htt⟩ : ∃ t ∈ Set.Icc (9 / 25) (37 / 100), thresholdPoly t = 0 := by
    simpa [Set.mem_image] using hmem
  have t_ne_lo : t ≠ 9 / 25 := by
    rintro rfl; linarith
  have t_ne_hi : t ≠ 37 / 100 := by
    rintro rfl; linarith
  have ht : t ∈ Set.Ioo (9 / 25) (37 / 100) :=
    ⟨lt_of_le_of_ne ht_mem.1 t_ne_lo.symm, lt_of_le_of_ne ht_mem.2 t_ne_hi⟩
  refine ⟨t, ⟨ht, htt⟩, ?_⟩
  intro t' ht'
  exact (thresholdPoly_strictMonoOn_att.injOn
    ⟨ht.1.le, ht.2.le⟩ ⟨ht'.1.1.le, ht'.1.2.le⟩ (htt.trans ht'.2.symm)).symm

/-- The attained value `1/yRoot + 2yRoot - 3` is the unique root of
`thresholdPoly` in `(0.36, 0.37)` (this is `t*` of Theorem 1). -/
theorem attained_is_unique_threshold_root :
    (1 / yRoot + 2 * yRoot - 3) ∈ Set.Ioo (9 / 25) (37 / 100) ∧
      thresholdPoly (1 / yRoot + 2 * yRoot - 3) = 0 ∧
      ∀ t, t ∈ Set.Ioo (9 / 25) (37 / 100) → thresholdPoly t = 0 → t = 1 / yRoot + 2 * yRoot - 3 := by
  obtain ⟨t, ⟨ht, htt⟩, huniq⟩ := exists_unique_threshold_root
  have key : t = 1 / yRoot + 2 * yRoot - 3 :=
    (huniq (1 / yRoot + 2 * yRoot - 3) ⟨⟨attained_t_bounds.1, attained_t_bounds.2⟩,
      thresholdPoly_yRoot⟩).symm
  refine ⟨⟨attained_t_bounds.1, attained_t_bounds.2⟩, thresholdPoly_yRoot, ?_⟩
  intro s hs hss
  exact (huniq s ⟨hs, hss⟩).trans key

/-! ## Postprocessing: independent sign noise (end of Section 2) -/

/-- Multiplying each party's output by an independent private sign of mean `η`
scales the one-body, two-body, and three-body aggregate moments by `η`, `η²`,
`η³` respectively. -/
def AggregateMoments.scaleSigns (η : ℝ) (m : AggregateMoments) : AggregateMoments where
  M1 := η * m.M1
  M2 := η ^ 2 * m.M2
  M3 := η ^ 3 * m.M3

lemma AggregateMoments.scaleSigns_apply (η : ℝ) (m : AggregateMoments) :
    m.scaleSigns η = ⟨η * m.M1, η ^ 2 * m.M2, η ^ 3 * m.M3⟩ := rfl

lemma AggregateMoments.scaleSigns_one (m : AggregateMoments) : m.scaleSigns 1 = m := by
  simp [AggregateMoments.scaleSigns]

lemma AggregateMoments.scaleSigns_zero (m : AggregateMoments) : m.scaleSigns 0 = ⟨0, 0, 0⟩ := by
  simp [AggregateMoments.scaleSigns]

/-- Sign noise of mean `η` applied to a vanishing model `(0, t, 0)` yields
`(0, η² · t, 0)`. -/
theorem scaleSigns_vanishing {t η : ℝ} :
    (AggregateMoments.mk 0 t 0).scaleSigns η = AggregateMoments.mk 0 (η ^ 2 * t) 0 := by
  simp [AggregateMoments.scaleSigns]

/-- For `η = √(t/t*)` with `0 ≤ t ≤ t*`, the scaled moments of `(0, t*, 0)` are
exactly `(0, t, 0)`, i.e. the family `p_t` of (2). -/
theorem scaleSigns_attains_p_t {t tStar η : ℝ}
    (hts : (0:ℝ) < tStar) (ht : 0 ≤ t) (hη : η = sqrt (t / tStar)) :
    (AggregateMoments.mk 0 tStar 0).scaleSigns η = AggregateMoments.mk 0 t 0 := by
  have hη2 : η ^ 2 = t / tStar := by
    rw [hη, sq_sqrt]
    exact div_nonneg ht hts.le
  have hη2' : η ^ 2 * tStar = t := by
    rw [hη2]
    field_simp [hts.ne']
  rw [scaleSigns_vanishing, hη2']

/-- The noise mean `η = √(t/t*)` lies in `[0, 1]` whenever `0 ≤ t ≤ t*`. -/
lemma eta_mem {t tStar : ℝ} (hts : (0:ℝ) < tStar) (ht : 0 ≤ t) (hle : t ≤ tStar) :
    sqrt (t / tStar) ∈ Set.Icc (0:ℝ) 1 := by
  have h1 : 0 ≤ t / tStar := div_nonneg ht hts.le
  have h2 : t / tStar ≤ 1 := by
    rw [div_le_one hts]
    exact hle
  exact ⟨sqrt_nonneg _, sqrt_le_one.mpr h2⟩

/-- Attainment of Theorem 1 (half): the exceptional table with law (8) produces
moments `(0, t*, 0)` where `t*` is the unique root of `thresholdPoly` in
`(0.36, 0.37)`, and independent sign noise of mean `η = √(t/t*)` yields `(0, t, 0)`
for every `t ∈ [0, t*]`. -/
theorem attainment_of_theorem :
    let tStar := 1 / yRoot + 2 * yRoot - 3
    detMoments DetTriangle.exceptional (law3 xAtt yAtt zAtt) (law3 xAtt yAtt zAtt)
        (law3 xAtt yAtt zAtt) = AggregateMoments.mk 0 tStar 0 ∧
      thresholdPoly tStar = 0 ∧
      (9 / 25 : ℝ) < tStar ∧ tStar < 37 / 100 ∧
      ∀ t, 0 ≤ t → t ≤ tStar →
        (AggregateMoments.mk 0 tStar 0).scaleSigns (sqrt (t / tStar))
          = AggregateMoments.mk 0 t 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [attaining_moments]; rfl
  · exact thresholdPoly_yRoot
  · exact attained_t_bounds.1
  · exact attained_t_bounds.2
  · intro t ht hle
    have hpos : (0:ℝ) < (1 / yRoot + 2 * yRoot - 3) := by
      have := attained_t_bounds.1
      exact lt_trans (by norm_num) this
    exact scaleSigns_attains_p_t hpos ht rfl

end Paper15

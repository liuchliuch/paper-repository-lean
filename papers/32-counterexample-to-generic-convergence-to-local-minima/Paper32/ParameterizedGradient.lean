import Paper32.Dynamics
import Paper32.Geometry

open Set Filter Topology

noncomputable section

namespace Paper32.TrapParameters

/-- The literal parameterized min-absolute-value core of Proposition A.1. -/
def gAB (p : TrapParameters) (z : Point) : ℝ :=
  min (|z.1| + p.A * |z.2|) (p.B * |z.1| - |z.2|)

local instance (p : TrapParameters) (x y : ℝ) : Decidable (p.Horizontal x y) :=
  Classical.propDecidable _

/-- Ordinary Euclidean gradient of the parameterized core away from its arrangement. -/
def gradientAB (p : TrapParameters) (z : Point) : Point :=
  if p.Horizontal z.1 z.2 then
    (quadrantSign z.1, p.A * quadrantSign z.2)
  else (p.B * quadrantSign z.1, -quadrantSign z.2)

lemma horizontal_branch_ineq {p : TrapParameters} {z : Point}
    (hh : p.Horizontal z.1 z.2) :
    |z.1| + p.A * |z.2| < p.B * |z.1| - |z.2| := by
  have hA : 0 < p.A + 1 := by linarith [p.delta_lt_A, p.delta_nonneg]
  have hm : p.slope * (p.A + 1) = p.B - 1 := by
    unfold slope
    exact div_mul_cancel₀ _ (ne_of_gt hA)
  have h := mul_lt_mul_of_pos_right hh hA
  have hmx := congrArg (fun t => t * |z.1|) hm
  nlinarith only [h, hmx]

lemma vertical_branch_ineq {p : TrapParameters} {z : Point}
    (hv : p.Vertical z.1 z.2) :
    p.B * |z.1| - |z.2| < |z.1| + p.A * |z.2| := by
  have hA : 0 < p.A + 1 := by linarith [p.delta_lt_A, p.delta_nonneg]
  have hm : p.slope * (p.A + 1) = p.B - 1 := by
    unfold slope
    exact div_mul_cancel₀ _ (ne_of_gt hA)
  have h := mul_lt_mul_of_pos_right hv hA
  have hmx := congrArg (fun t => t * |z.1|) hm
  nlinarith only [h, hmx]

private lemma abs_fst_derivative {z : Point} (hz : z.1 ≠ 0) :
    HasFDerivAt (fun q : Point => |q.1|)
      (quadrantSign z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) z := by
  by_cases hn : z.1 < 0
  · have heq : quadrantSign z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ =
        -ContinuousLinearMap.fst ℝ ℝ ℝ := by
      apply ContinuousLinearMap.ext
      intro q
      simp [quadrantSign, hn]
    rw [heq]
    exact (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).abs_of_neg hn
  · have hp : 0 < z.1 := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
    simpa [quadrantSign, hn, neg_one_smul] using
      (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).abs_of_pos hp

private lemma abs_snd_derivative {z : Point} (hz : z.2 ≠ 0) :
    HasFDerivAt (fun q : Point => |q.2|)
      (quadrantSign z.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) z := by
  by_cases hn : z.2 < 0
  · have heq : quadrantSign z.2 • ContinuousLinearMap.snd ℝ ℝ ℝ =
        -ContinuousLinearMap.snd ℝ ℝ ℝ := by
      apply ContinuousLinearMap.ext
      intro q
      simp [quadrantSign, hn]
    rw [heq]
    exact (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).abs_of_neg hn
  · have hp : 0 < z.2 := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
    simpa [quadrantSign, hn, neg_one_smul] using
      (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).abs_of_pos hp

/-- Actual derivative, horizontal sector, for every admitted A and B. -/
theorem hasFDerivAt_gAB_horizontal {p : TrapParameters} {z : Point}
    (hx : z.1 ≠ 0) (hy : z.2 ≠ 0) (hh : p.Horizontal z.1 z.2) :
    HasFDerivAt (gAB p) (linCLM (quadrantSign z.1, p.A * quadrantSign z.2)) z := by
  have hbranch := horizontal_branch_ineq hh
  have hc : Continuous (fun q : Point =>
      (p.B * |q.1| - |q.2|) - (|q.1| + p.A * |q.2|)) := by fun_prop
  have heq : gAB p =ᶠ[𝓝 z] (fun q : Point => |q.1| + p.A * |q.2|) := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds
      (Ioi_mem_nhds (sub_pos.mpr hbranch))] with q hq
    exact min_eq_left (le_of_lt (sub_pos.mp hq))
  have hd := (abs_fst_derivative hx).add ((abs_snd_derivative hy).const_mul p.A)
  have hd' : HasFDerivAt (fun q : Point => |q.1| + p.A * |q.2|)
      (linCLM (quadrantSign z.1, p.A * quadrantSign z.2)) z := by
    simpa [linCLM, smul_smul] using hd
  exact hd'.congr_of_eventuallyEq heq

/-- Actual derivative, vertical sector, for every admitted A and B. -/
theorem hasFDerivAt_gAB_vertical {p : TrapParameters} {z : Point}
    (hx : z.1 ≠ 0) (hy : z.2 ≠ 0) (hv : p.Vertical z.1 z.2) :
    HasFDerivAt (gAB p) (linCLM (p.B * quadrantSign z.1, -quadrantSign z.2)) z := by
  have hbranch := vertical_branch_ineq hv
  have hc : Continuous (fun q : Point =>
      (|q.1| + p.A * |q.2|) - (p.B * |q.1| - |q.2|)) := by fun_prop
  have heq : gAB p =ᶠ[𝓝 z] (fun q : Point => p.B * |q.1| - |q.2|) := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds
      (Ioi_mem_nhds (sub_pos.mpr hbranch))] with q hq
    exact min_eq_right (le_of_lt (sub_pos.mp hq))
  have hd := ((abs_fst_derivative hx).const_mul p.B).sub (abs_snd_derivative hy)
  have hd' : HasFDerivAt (fun q : Point => p.B * |q.1| - |q.2|)
      (linCLM (p.B * quadrantSign z.1, -quadrantSign z.2)) z := by
    have heq : linCLM (p.B * quadrantSign z.1, -quadrantSign z.2) =
        p.B • (quadrantSign z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) -
          quadrantSign z.2 • ContinuousLinearMap.snd ℝ ℝ ℝ := by
      apply ContinuousLinearMap.ext
      intro q
      simp [linCLM]
      ring
    rw [heq]
    exact hd
  exact hd'.congr_of_eventuallyEq heq

/-- The sector formula is the genuine Fréchet derivative of the literal source core. -/
theorem hasFDerivAt_gAB {p : TrapParameters} {z : Point}
    (hx : z.1 ≠ 0) (hy : z.2 ≠ 0) (hb : |z.2| ≠ p.slope * |z.1|) :
    HasFDerivAt (gAB p) (linCLM (gradientAB p z)) z := by
  rcases lt_or_gt_of_ne hb with hh | hv
  · simpa [gradientAB, Horizontal, hh] using hasFDerivAt_gAB_horizontal hx hy hh
  · have hh : ¬ p.Horizontal z.1 z.2 := by unfold Horizontal; linarith
    simpa [gradientAB, hh, mul_add] using hasFDerivAt_gAB_vertical hx hy hv

/-- An actual noisy gradient step supplies precisely the CoreStep used in A.1. -/
def coreStep_of_gradientAB {p : TrapParameters} {α : ℝ} {z z' e : Point}
    (hx : z.1 ≠ 0) (hy : z.2 ≠ 0) (hb : |z.2| ≠ p.slope * |z.1|)
    (heX : |e.1| ≤ p.delta) (heY : |e.2| ≤ p.delta)
    (hstep : z' = z - α • (gradientAB p z + e)) :
    p.CoreStep α z.1 z.2 z'.1 z'.2 where
  x_ne := hx
  y_ne := hy
  sector_ne := hb
  ex := e.1
  ey := e.2
  ex_bound := heX
  ey_bound := heY
  x_update := by
    have h := congrArg Prod.fst hstep
    by_cases hh : p.Horizontal z.1 z.2
    · simpa [gradientAB, hh, mul_add] using h
    · simpa [gradientAB, hh, mul_add] using h
  y_update := by
    have h := congrArg Prod.snd hstep
    by_cases hh : p.Horizontal z.1 z.2
    · simpa [gradientAB, hh, mul_add] using h
    · simpa [gradientAB, hh, mul_add] using h

end Paper32.TrapParameters

namespace Paper32.TrapParameters

/-- Proposition A.1 for the literal core and its verified ordinary gradient.
Indices begin with the initial state z₁, at scale α₀, as in the source. -/
theorem parameterized_gradient_trap (p : TrapParameters)
    (α : ℕ → ℝ) (z e : ℕ → Point)
    (hα : ∀ k, 0 < α k) (hlim : Tendsto α atTop (𝓝 0))
    (hratio : ∀ k, α k ≤ p.kappa * α (k + 1))
    (hx : ∀ k, (z (k + 1)).1 ≠ 0)
    (hy : ∀ k, (z (k + 1)).2 ≠ 0)
    (hb : ∀ k, |(z (k + 1)).2| ≠ p.slope * |(z (k + 1)).1|)
    (heX : ∀ k, |(e (k + 1)).1| ≤ p.delta)
    (heY : ∀ k, |(e (k + 1)).2| ≤ p.delta)
    (hstep : ∀ k, z (k + 2) = z (k + 1) -
      α (k + 1) • (gradientAB p (z (k + 1)) + e (k + 1)))
    (hinit : |(z 1).1| ≤ p.X * α 0 ∧ |(z 1).2| ≤ p.Y * α 0) :
    (∀ k, |(z (k + 1)).1| ≤ p.X * α k ∧
      |(z (k + 1)).2| ≤ p.Z * α k) ∧
    Tendsto z atTop (𝓝 (0 : Point)) ∧
    (∀ k, p.Vertical (z (k + 1)).1 (z (k + 1)).2 →
      p.Horizontal (z (k + 2)).1 (z (k + 2)).2) := by
  let steps : ∀ k, p.CoreStep (α (k + 1)) (z (k + 1)).1 (z (k + 1)).2
      (z (k + 2)).1 (z (k + 2)).2 := fun k =>
    coreStep_of_gradientAB (hx k) (hy k) (hb k) (heX k) (heY k) (hstep k)
  have hconv := parameterized_convergence p α (fun k => (z k).1)
    (fun k => (z k).2) hα hlim hratio steps hinit
  refine ⟨parameterized_bounds p α (fun k => (z k).1) (fun k => (z k).2)
    hα hratio steps hinit, ?_, ?_⟩
  · exact hconv.1.prodMk_nhds hconv.2
  · exact no_consecutive_vertical p α (fun k => (z k).1) (fun k => (z k).2)
      hα hratio steps hinit

end Paper32.TrapParameters

namespace Paper32.TrapParameters

/-- Raw coefficients (A,B,δ,κ,X,Y,Z), in their source order. -/
abbrev ParameterTuple := Fin 7 → ℝ

def numericalTuple : ParameterTuple :=
  fun i => match i.val with
    | 0 => 2
    | 1 => 7
    | 2 => 0.02
    | 3 => 1.13
    | 4 => 7.2
    | 5 => 2.5
    | _ => 3.9

/-- Minimum of every strict admissibility margin. Its positivity certifies
all source hypotheses, including the strict versions of δ≥0 and κ≥1. -/
def strictMargin (q : ParameterTuple) : ℝ :=
  min (q 2) <| min (1 - q 2) <| min (q 0 - q 2) <| min (q 1 - 1) <|
  min (q 3 - 1) <| min (q 4) <| min (q 5) <| min (q 6) <|
  min (q 4 - (q 1 + q 2)) <| min (q 5 - (q 0 + q 2)) <|
  min (1 - q 2 - q 4 * (q 3 - 1)) <|
  min (q 0 - q 2 - q 5 * (q 3 - 1)) <|
  min (q 1 - q 2 - q 5 * q 3 / ((q 1 - 1) / (q 0 + 1))) <|
  min (q 6 - (q 5 * q 3 + 1 + q 2)) <|
  min (((q 1 - 1) / (q 0 + 1)) * (q 1 - q 2) - q 5 * q 3 - q 6)
    (q 5 - (q 6 * q 3 - (q 0 - q 2)))

lemma numerical_margin_pos : 0 < strictMargin numericalTuple := by
  simp only [strictMargin, lt_min_iff]
  norm_num [numericalTuple]

lemma continuousAt_strictMargin : ContinuousAt strictMargin numericalTuple := by
  have hc (i : Fin 7) : ContinuousAt (fun q : ParameterTuple => q i) numericalTuple :=
    (continuous_apply i).continuousAt
  have hOne : ContinuousAt (fun _ : ParameterTuple => (1 : ℝ)) numericalTuple := continuousAt_const
  have hm := ((hc 1).sub hOne).div ((hc 0).add hOne) (by norm_num [numericalTuple])
  have hms : ((numericalTuple 1 - 1) / (numericalTuple 0 + 1)) ≠ 0 := by
    norm_num [numericalTuple]
  exact (hc 2).min ((hOne.sub (hc 2)).min (((hc 0).sub (hc 2)).min
    (((hc 1).sub hOne).min (((hc 3).sub hOne).min ((hc 4).min ((hc 5).min ((hc 6).min
      (((hc 4).sub ((hc 1).add (hc 2))).min
        (((hc 5).sub ((hc 0).add (hc 2))).min
          (((hOne.sub (hc 2)).sub ((hc 4).mul ((hc 3).sub hOne))).min
            ((((hc 0).sub (hc 2)).sub ((hc 5).mul ((hc 3).sub hOne))).min
              ((((hc 1).sub (hc 2)).sub (((hc 5).mul (hc 3)).div hm hms)).min
                (((hc 6).sub ((((hc 5).mul (hc 3)).add hOne).add (hc 2))).min
                  ((((hm.mul ((hc 1).sub (hc 2))).sub ((hc 5).mul (hc 3))).sub (hc 6)).min
                    ((hc 5).sub (((hc 6).mul (hc 3)).sub ((hc 0).sub (hc 2))))))))))))))))))

/-- Convert an open strict-margin certificate into the actual parameters
used by the pathwise trapping theorem. -/
def parametersOfMargin (q : ParameterTuple) (h : 0 < strictMargin q) : TrapParameters := by
  simp only [strictMargin, lt_min_iff] at h
  have hd := h.1
  have hd1 := h.2.1
  have hA := h.2.2.1
  have hB := h.2.2.2.1
  have hk := h.2.2.2.2.1
  have hX := h.2.2.2.2.2.1
  have hY := h.2.2.2.2.2.2.1
  have hZ := h.2.2.2.2.2.2.2.1
  have hBX := h.2.2.2.2.2.2.2.2.1
  have hAY := h.2.2.2.2.2.2.2.2.2.1
  have hXr := h.2.2.2.2.2.2.2.2.2.2.1
  have hYr := h.2.2.2.2.2.2.2.2.2.2.2.1
  have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hvY := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hvS := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hrY := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact {
    A := q 0, B := q 1, delta := q 2, kappa := q 3,
    X := q 4, Y := q 5, Z := q 6,
    delta_nonneg := le_of_lt hd
    delta_lt_one := by linarith
    delta_lt_A := by linarith
    one_lt_B := by linarith
    one_le_kappa := by linarith
    X_pos := hX
    Y_pos := hY
    Z_pos := hZ
    B_delta_lt_X := by linarith
    A_delta_lt_Y := by linarith
    X_ratio := by linarith
    Y_ratio := by linarith
    vertical_cross := by linarith
    vertical_Y := by linarith
    vertical_sector := by linarith
    recovery_Y := by linarith }

/-- The unnumbered claim following Proposition A.1: an open neighborhood
of the displayed seven coefficients satisfies the same exact trap criterion. -/
theorem open_neighborhood_of_numerical_parameters :
    ∃ U : Set ParameterTuple, IsOpen U ∧ numericalTuple ∈ U ∧
      ∀ q ∈ U, ∃ p : TrapParameters,
        p.A = q 0 ∧ p.B = q 1 ∧ p.delta = q 2 ∧ p.kappa = q 3 ∧
        p.X = q 4 ∧ p.Y = q 5 ∧ p.Z = q 6 := by
  have hn : {q : ParameterTuple | 0 < strictMargin q} ∈ 𝓝 numericalTuple :=
    continuousAt_strictMargin.preimage_mem_nhds (Ioi_mem_nhds numerical_margin_pos)
  rcases mem_nhds_iff.mp hn with ⟨U, hsub, hU, hmem⟩
  refine ⟨U, hU, hmem, ?_⟩
  intro q hq
  exact ⟨parametersOfMargin q (hsub hq), rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Paper32.TrapParameters

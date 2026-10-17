import Paper10.Appendix
import Paper10.MetricCalculus
import Mathlib.Analysis.Convex.Deriv

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Paper10
variable {q : ℕ}
set_option maxHeartbeats 1000000

private def trMap : Matrix (Fin q) (Fin q) ℝ →L[ℝ] ℝ :=
  (Matrix.traceLinearMap (Fin q) ℝ ℝ).toContinuousLinearMap

/-- The first derivative of the actual quartic trace along any matrix line. -/
theorem hasDerivAt_trace_four (A H : Matrix (Fin q) (Fin q) ℝ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Matrix.trace ((A + u • H) ^ 4))
      (4 * Matrix.trace ((A + t • H) * (A + t • H) * (A + t • H) * H)) t := by
  have hp : ∀ M : Matrix (Fin q) (Fin q) ℝ, M ^ 4 = M * M * M * M := by
    intro M
    simp [pow_succ]
  simp_rw [hp]
  let Z := A + t • H
  have hc : HasDerivAt (fun u : ℝ => A + u • H) H t := by
    simpa only [zero_add, one_smul] using
      (hasDerivAt_const t A).add ((hasDerivAt_id t).smul_const H)
  have hm := ((hc.mul hc).mul hc).mul hc
  have ht := (trMap (q := q)).hasFDerivAt.comp_hasDerivAt t hm
  have h1 : Matrix.trace (H * Z * Z * Z) = Matrix.trace (Z * Z * Z * H) :=
    (trace_four_cycle Z Z Z H).symm
  have h3 : Matrix.trace (Z * Z * H * Z) = Matrix.trace (Z * Z * Z * H) :=
    trace_four_cycle Z Z H Z
  have h2 : Matrix.trace (Z * H * Z * Z) = Matrix.trace (Z * Z * Z * H) :=
    (trace_four_cycle Z H Z Z).trans h3
  convert ht using 1
  change 4 * Matrix.trace (Z * Z * Z * H) =
      Matrix.trace (((H * Z + Z * H) * Z + Z * Z * H) * Z + Z * Z * Z * H)
  simp only [Matrix.add_mul, Matrix.trace_add, h1, h2, h3]
  ring

/-- Exact second directional derivative displayed in Appendix A.2. -/
theorem hasDerivAt_trace_four_first (A H : Matrix (Fin q) (Fin q) ℝ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => 4 * Matrix.trace ((A + u • H) * (A + u • H) * (A + u • H) * H))
      (8 * Matrix.trace ((A + t • H) * (A + t • H) * H * H) +
        4 * Matrix.trace ((A + t • H) * H * (A + t • H) * H)) t := by
  let Z := A + t • H
  have hc : HasDerivAt (fun u : ℝ => A + u • H) H t := by
    simpa only [zero_add, one_smul] using
      (hasDerivAt_const t A).add ((hasDerivAt_id t).smul_const H)
  have hm := ((hc.mul hc).mul hc).mul_const H
  have ht := ((trMap (q := q)).hasFDerivAt.comp_hasDerivAt t hm).const_mul 4
  convert ht using 1
  change 8 * Matrix.trace (Z * Z * H * H) + 4 * Matrix.trace (Z * H * Z * H) =
    4 * Matrix.trace (((H * Z + Z * H) * Z + Z * Z * H) * H)
  simp only [Matrix.add_mul, Matrix.trace_add]
  rw [show Matrix.trace (H * Z * Z * H) = Matrix.trace (Z * Z * H * H) from
    (trace_four_cycle Z Z H H).symm]
  ring

/-- Convexity of the actual quartic trace along every symmetric line. -/
theorem trace_four_line_convex (A H : Matrix (Fin q) (Fin q) ℝ) (hA : A.IsSymm) (hH : H.IsSymm) :
    ConvexOn ℝ Set.univ (fun t : ℝ => Matrix.trace ((A + t • H) ^ 4)) := by
  have hd : deriv (fun t : ℝ => Matrix.trace ((A + t • H) ^ 4)) =
      fun t => 4 * Matrix.trace ((A + t • H) * (A + t • H) * (A + t • H) * H) :=
    funext (fun t => (hasDerivAt_trace_four A H t).deriv)
  apply convexOn_univ_of_deriv2_nonneg
  · exact fun t => (hasDerivAt_trace_four A H t).differentiableAt
  · rw [hd]
    exact fun t => (hasDerivAt_trace_four_first A H t).differentiableAt
  · intro t
    rw [Function.iterate_succ_apply', Function.iterate_one, hd,
      (hasDerivAt_trace_four_first A H t).deriv]
    exact (tr_four_convex_nonneg (hA.add (hH.smul t)) hH).trans
      (tr_four_convex (hA.add (hH.smul t)) hH)

/-- Appendix A.2: Tr(A⁴) is convex on the entire space of real symmetric matrices. -/
theorem trace_four_convexOn :
    ConvexOn ℝ {A : Matrix (Fin q) (Fin q) ℝ | A.IsSymm} (fun A => Matrix.trace (A ^ 4)) := by
  refine ⟨?_, ?_⟩
  · intro A hA B hB a b ha hb hab
    exact (hA.smul a).add (hB.smul b)
  · intro A hA B hB a b ha hb hab
    have hc := trace_four_line_convex A (B - A) hA (hB.sub hA)
    have hh := hc.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) ha hb hab
    have he : A + b • (B - A) = a • A + b • B := by
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      nlinarith [congrArg (fun x : ℝ => x * A i j) hab]
    simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero, one_smul,
      add_sub_cancel, he] using hh

end Paper10

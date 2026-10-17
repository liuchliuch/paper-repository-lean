import Paper20.QEvaluation
import Paper20.RSeriesSemantics
import Paper20.PartitionHooks

namespace Paper20
open Polynomial
noncomputable section
set_option maxHeartbeats 2000000

/-- The exact normalized series obtained from the actual partition data in
equations (18)--(21). This definition contains no BPS coefficients. -/
def normalizedPartitionSeries (r k : ℕ) : PowerSeries ℚ :=
  PowerSeries.C (1/(r.factorial:ℚ))*
    ((partitionsOf r).map (fun ps => PowerSeries.C (((dimOf r ps)^2:ℕ):ℚ)*
      ((Phi.contentNumerator (contentOf ps).natAbs k : ℚ[X]) : PowerSeries ℚ)*
      LogSeries.Rproduct (hooksOf ps) (partsEvenHooks ps))).sum

/-- Equation (20)'s actual constructed Q evaluates to the coefficient of
the genuine normalized partition-series product, rather than a finite
recurrence substituted for equation (18). -/
theorem Qcoeff_eq_normalizedPartitionSeries (r h k : ℕ) :
    peval (Qcoeff r h) ((k:ℚ)*(k+1)) =
      PowerSeries.coeff h (normalizedPartitionSeries r k) := by
  rw [Qcoeff_evaluation, normalizedPartitionSeries, PowerSeries.coeff_C_mul,
    map_list_sum]
  congr 1
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ps hp
  dsimp only [Function.comp_apply]
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  congr 1
  rw [LogSeries.sum_map_range]
  apply Finset.sum_congr rfl
  intro j hj
  rw [LogSeries.Rseries_correct _ _ h (h-j)
    (hooksOf_positive_of_mem_partitionsOf hp) (by omega), Polynomial.coeff_coe]
  ring

end
end Paper20

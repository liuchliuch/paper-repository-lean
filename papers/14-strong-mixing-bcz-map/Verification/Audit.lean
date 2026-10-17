import Verification.Solution
import Paper14.TestMetric
import Lean

/-!
# Axiom audit for Paper 14 contracts

Audit every declaration in the `P14Contract` and `Paper14` namespaces against
its complete transitive axiom closure.  Only `propext`, `Classical.choice`,
and `Quot.sound` are permitted.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  for (name, _) in env.constants.toList do
    if (`P14Contract |>.isPrefixOf name) || (`Paper14 |>.isPrefixOf name) then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless permitted.contains ax do
          throwError "Illegal transitive axiom {ax} in {name}"
      count := count + 1
  logInfo m!"P14Contract/Paper14 declarations audited: {count}; all transitive axioms are permitted."

#print axioms P14Contract.b_apply
#print axioms P14Contract.tau_apply
#print axioms P14Contract.floor_branch_le
#print axioms P14Contract.b_inverse_left
#print axioms P14Contract.b_det_one
#print axioms P14Contract.coordinate_change
#print axioms P14Contract.primitive_iff_coprime
#print axioms P14Contract.sieve_residual_nonneg
#print axioms P14Contract.indicator_mean_sum
#print axioms P14Contract.flow_time_lower


#print axioms Paper14.measurePreserving_B
#print axioms Paper14.measurePreserving_phiR
#print axioms Paper14.phiR_tendstoInMeasure
#print axioms Paper14.integral_tau
#print axioms Paper14.positive_components_of_decomposition

#print axioms Paper14.kac_integral
#print axioms Paper14.conjugate_induced_excess_first_moment
#print axioms Paper14.sum_shift_excessGraphMeasure

#print axioms Paper14.ergodic_B
#print axioms Paper14.Lemma2
#print axioms Paper14.Proposition3
#print axioms Paper14.Theorem4
#print axioms Paper14.Lemma5
#print axioms Paper14.Theorem1
#print axioms Paper14.Theorem1ComplexL2
#print axioms Paper14.finite_block_mixing
#print axioms Paper14.bcz_suspension_fundamentalDomain

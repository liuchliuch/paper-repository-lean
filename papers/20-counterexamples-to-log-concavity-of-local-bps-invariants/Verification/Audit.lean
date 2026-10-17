import Paper20
import Verification.SupportingSolution
import Verification.Solution
import Verification.RelativeSolution
import Lean

/-! Full transitive axiom audit for every production/supporting declaration.
The challenge and negative controls are deliberately absent from the imports. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut roots : Array Name := #[]
  let mut privateRoots : Nat := 0
  for (name, _) in env.constants.toList do
    -- Select by the ACTUAL defining module, including private/generated
    -- declarations and names exported outside the Paper20 namespace.
    let fromProduction := match env.getModuleIdxFor? name with
      | none => false
      | some idx =>
        let modName := env.header.moduleNames[idx.toNat]!
        (`Paper20).isPrefixOf modName || modName == `Verification.Objects ||
          modName == `Verification.SupportingSolution || modName == `Verification.Solution ||
          modName == `Verification.RelativeTransfer || modName == `Verification.RelativeSolution
    if fromProduction then
      unless (env.checked.get.find? name).isSome do
        throwError "Production/supporting declaration {name} is absent from the checked kernel environment"
      roots := roots.push name
      if name.toString.startsWith "_private." then
        privateRoots := privateRoots + 1
  -- Exactly Lean's official collector on the union of ALL production roots.
  -- Reusing visited nodes only avoids traversing identical dependencies
  -- thousands of times; every discovered transitive axiom is still tested.
  let action : Lean.CollectAxioms.M Unit := roots.forM Lean.CollectAxioms.collect
  let (_, closure) := (action.run env).run {}
  for ax in closure.axioms do
    unless permitted.contains ax do
      -- Give a precise originating declaration in the failure case.
      for name in roots do
        let axioms ← collectAxioms name
        if axioms.contains ax then
          throwError "Illegal transitive axiom {ax} in {name}"
      throwError "Illegal transitive axiom {ax} in production/supporting closure"
  logInfo m!"Production/supporting declarations audited by defining module: {roots.size}; private declarations: {privateRoots}; every transitive axiom is permitted."

#print axioms Paper20.Semantics.localBPSExpansion_iff_series
#print axioms Paper20.Semantics.localBPSExpansion_eq_extracted
#print axioms Paper20.Cert.Checked43.certificate_recurrence
#print axioms Paper20.Cert.Hilbert43.residual_eq
#print axioms Paper20.Ordinary43Bridge.theorem11_of_hilbert_prefix
#print axioms Paper20.BraidWalk.walk_bounds
#print axioms Paper20.BraidWalk.walk_endpoints
#print axioms Paper20.prop_3_2
#print axioms Paper20.Uniform36.G_shift
#print axioms Paper20.Uniform36.thm12_Q
#print axioms Paper20.Uniform36.table1_verified
#print axioms Paper20.Elimination.bpsFromF_eq_extracted
#print axioms Paper20.FastHilbert.total_correct
#print axioms Paper20.Phi.Apoly_eval_content
#print axioms Paper20.Phi.even_quantum
#print axioms Paper20.Dpoly_quantum
#print axioms Paper20.LogSeries.Rseries_correct
#print axioms Paper20.Qcoeff_eq_normalizedPartitionSeries
#print axioms Paper20.WalkTrace.transpositionReturns_eq_matrix_moment

#print axioms Paper20.HeckeOperators.adjacent_braid
#print axioms Paper20.HeckeOperators.adjacent_commute
#print axioms Paper20.HeckeWalkExpansion.wordAction_coeff
#print axioms Paper20.BraidWalk.admissible_even_stays
#print axioms Paper20.HilbertSeriesProof.bpsCoeff_top

#print axioms Paper20.HeckeFullTwistTrace.fullTwist_identity_polynomial
#print axioms Paper20.HalfTwistMatrix.halfTwist_delta
#print axioms Paper20.normalizedPartitionSeries36_rationalHilbert
#print axioms Paper20.QuantumSeriesCoordinates.coordinateMap_injective

#print axioms Paper20.HeckeTraceAlgebra.canonicalTrace_basis
#print axioms Paper20.HeckeTraceAlgebra.canonicalTrace_cyclic
#print axioms Paper20.HeckeTraceAlgebra.trace_nondegenerate
#print axioms Paper20.HeckeTraceAlgebra.trace_basis_inverse
#print axioms Paper20.HeckeTraceAlgebra.canonicalTrace_omega_even_variable
#print axioms Paper20.Cert.ACacheFast36.aCached_correct
#print axioms Paper20.RContent36.evaluateFastVector_scaled

#print axioms P20Objects.transpositionReturns_one
#print axioms Paper20.HeckeTraceAlgebra.fullTwist_central
#print axioms Paper20.HeckeSpecialization.specialize_basis
#print axioms Paper20.HeckeParameterPolynomial.walkCount_exponent_polynomial
#print axioms Paper20.HeckeParameterPolynomial.exponentPolynomial_top_matrix
#print axioms Paper20.HeckeTraceAlgebra.algebra_divX_mem
#print axioms Paper20.HeckeBar.fullTwist_trace_reciprocity
#print axioms Paper20.HookBeta.actual_hook_vandermonde
#print axioms Paper20.Cert.ContentQ36Rows.evaluated22
#print axioms Paper20.ContentQ36Bridge.Q22_of_root
#print axioms Paper20.ContentQ36Bridge.constructed_Q_inequality

#print axioms Paper20.HookDeterminant.diagram_hook_dvd_factorial
#print axioms Paper20.HookDeterminant.actual_dim_mul_hooks
#print axioms Paper20.normalizedPartitionSeries_rationalHilbert
#print axioms Paper20.HilbertSeriesProof.rational_expansion_to_program
#print axioms Paper20.HilbertAtZero.rational_expansion_of_quantum
#print axioms Paper20.HilbertHeckeBridge.bps_Q_evaluation_of_character
#print axioms Paper20.HeckeTraceAlgebra.infinitesimalFullTwist_eq_transpositionSum
#print axioms Paper20.HeckeTraceAlgebra.exponentPolynomial_top_actual_returns

#print axioms Paper20.HookDeterminant.factorial_det_branching
#print axioms Paper20.HookDeterminant.actual_dim_factorial_det
#print axioms Paper20.YoungCorners.young_differential_identity
#print axioms Paper20.YoungShapes.down_up
#print axioms Paper20.YoungShapes.vacuum_norm

#print axioms Paper20.YoungShapes.dimension_branching
#print axioms Paper20.YoungShapes.vacuum_dimension
#print axioms Paper20.dimSquareSum_eq_factorial
#print axioms Paper20.Qcoeff_zero_order_polynomial

#print axioms Paper20.YoungShapes.standardFilling_card
#print axioms Paper20.YoungShapes.exchange_exchange
#print axioms Paper20.Seminormal.hilbert_unit_parameter_injective
#print axioms Paper20.Seminormal.action_braid
#print axioms Paper20.Seminormal.tableauLinear_quadratic
#print axioms Paper20.Seminormal.tableauLinear_commute

#print axioms Paper20.Seminormal.tableauLinear_braid
#print axioms Paper20.YoungShapes.filling_content_triple_ne
#print axioms Paper20.Seminormal.chain_diagonal_equal
#print axioms Paper20.Seminormal.tableauLinear_murphy
#print axioms Paper20.Seminormal.murphyOperator_eq_diagonal
#print axioms Paper20.Seminormal.fullTwistTableau_scalar

#print axioms Paper20.PresentedHecke.normalSpan_eq_top
#print axioms Paper20.PresentedHecke.presented_finrank_le
#print axioms Paper20.FieldHecke.regularRepresentation_injective
#print axioms Paper20.FieldHecke.originalRepresentation_generator
#print axioms Paper20.Cert.HilbertParts.Tree.h43_partition_sum
#print axioms Paper20.Counterexample43.theorem1_1
#print axioms P20Required.thm_1_1
#print axioms Paper20.Seminormal.tableauProjector_apply
#print axioms Paper20.ExternalNormalization.schurElement_quantum
#print axioms Paper20.ExternalInput.partition_trace
#print axioms Paper20.Relative.bps_bounds
#print axioms Paper20.Relative.bps_Q
#print axioms Paper20.Relative.Q_at_zero
#print axioms Paper20.Relative.Q_top_returns
#print axioms Paper20.ExternalInput.geometric_local_expansion
#print axioms Paper20.ExternalInput.geometricBPS_eq_program
#print axioms Paper20.ExternalInput.geometric_trace
#print axioms Paper20.Relative.geometric_theorem1_1
#print axioms Paper20.Relative.theorem1_2_of_root
#print axioms Paper20.Relative.actual_leading_test
#print axioms Paper20.SkeinParity.convention_sign
#print axioms Paper20.Relative.moment_returns
#print axioms Paper20.ExternalInput.mathas_semisimplicity_product
#print axioms Paper20.ExternalInput.schurElement_ne_zero
#print axioms Paper20.Relative.geometric_node_homfly
#print axioms Paper20.ExternalInput.homfly_coefficient_sign
#print axioms Paper20.ExternalInput.GeometricInputs.hilbert_homfly
#print axioms Paper20.ExternalInput.origin_eval_injective
#print axioms Paper20.ExternalInput.normalized_ruling_unique
#print axioms Paper20.ExternalInput.ruling_theorem1_1
#print axioms Paper20.ExternalInput.ruling_theorem1_2_of_root
#print axioms Paper20.Cert.RContent36.Tree.root_correct
#print axioms Paper20.Counterexample36.theorem1_2
#print axioms Paper20.Counterexample36.geometric_theorem1_2
#print axioms Paper20.Counterexample36.ruling_theorem1_2
#print axioms P20Relative.thm_1_2
#print axioms P20Relative.prop_3_2
#print axioms P20Relative.ruling_thm_1_2

import Paper18.AllSources
import Lean

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  -- The official Lean collector, sharing its visited set across all roots.
  -- This audits the same union of transitive closures without re-traversing
  -- imported mathlib declarations for every generated projection.
  let mut state : CollectAxioms.State := {}
  for (name, _) in env.constants.toList do
    -- Attribute a declaration by its defining module, rather than its
    -- namespace. This includes private and generated declarations and
    -- declarations intentionally placed in CategoryTheory namespaces.
    let ownModule := match env.getModuleIdxFor? name with
      | some idx => `Paper18 |>.isPrefixOf env.header.moduleNames[idx]!
      | none => `Paper18 |>.isPrefixOf name
    if ownModule then
      let (_, next) := ((CollectAxioms.collect name).run env).run state
      state := next
      for ax in state.axioms do
        unless permitted.contains ax do
          throwError "Illegal transitive axiom {ax}, discovered while auditing {name}"
      count := count + 1
  logInfo m!"Paper18 module-origin declarations audited: {count}; all transitive axioms are permitted."
  logInfo m!"Transitive closure axioms: {state.axioms}"

#print axioms Paper18.lemma2_1_twist
#print axioms Paper18.lemma2_1_unique
#print axioms Paper18.prop2_2
#print axioms Paper18.prop2_2_slope_trivial
#print axioms Paper18.lemma3_1_dominant
#print axioms Paper18.equivariant_dim_integral
#print axioms Paper18.lemmaA_1_cohomology
#print axioms Paper18.lemmaA_1_boundary_eq
#print axioms Paper18.theorem1_1_reduction
#print axioms Paper18.theorem1_1_reduction_integral
#print axioms Paper18.appendixB_chi_does_not_extend
#print axioms Paper18.appendixB_slope
#print axioms Paper18.posMatrix_positive_eigenspace_one_dim

#print axioms Paper18.FusionBasis.fpdim_isIntegral
#print axioms Paper18.FusionMap.fpdim_rational
#print axioms Paper18.EquivariantDimensionModel.integral_iff
#print axioms Paper18.normalizedFour_is_coboundary

#print axioms Paper18.FusionRules.exists_fpdim
#print axioms Paper18.Category.FiniteSemisimpleSkeleton.lemma3_1_dominant
#print axioms Paper18.Category.WeakAction.lemma3_1_equivariant
#print axioms Paper18.Category.FiniteSemisimpleSkeleton.fpdim_map
#print axioms Paper18.Category.exists_simple_biproduct_of_splitMonos
#print axioms Paper18.Category.lemma2_1
#print axioms Paper18.Category.spherical_of_negative_boson_centralizer
#print axioms Paper18.Category.pivotalOfBoundaryTrivialization_preserves
#print axioms Paper18.Category.AppendixBPointed.appendixB_actual_counterexample
#print axioms Paper18.Category.FiniteSemisimpleSkeleton.supportFPdim_mul_centralizer
#print axioms Paper18.Category.TannakianCenter.centralizerCenter
#print axioms Paper18.Category.spherical_of_minimal_pivotal_boundary
#print axioms Paper18.Category.TannakianSignKernel.positiveTannakianCenter
#print axioms Paper18.Category.SeparableAlgebra.localNondegenerate
#print axioms Paper18.Category.FiniteSemisimpleSkeleton.weaklyIntegral_of_orderTwo_centralizerIntegral
#print axioms Paper18.Category.DiagonalAlgebra.canonicalSeparable
#print axioms Paper18.Category.centralizer_integral_case_one
#print axioms Paper18.Category.centralizer_invertible_eq_image_of_minimal

#print axioms Paper18.Category.caseOneModularExtension

#print axioms Paper18.Category.CaseTwoCondensation.modularExtension

#print axioms Paper18.Category.PreliminaryCentralizer.sphericalized_preliminary

#print axioms Paper18.Category.PreliminaryCentralizer.negativeCentralizerFPdim_eq_four

#print axioms Paper18.Category.spherical_extension_of_c2_boundary

#print axioms Paper18.Category.SeparableAlgebra.quotient

#print axioms Paper18.Category.DiagonalAlgebra.canonicalSeparableNoPivotal

#print axioms Paper18.Category.FiniteSemisimpleSkeleton.exists_unique_positive_of_weakIntegral_withoutPivotal

#print axioms Paper18.Category.Sphericalized.positiveForget_isEquivalence

#print axioms Paper18.Category.FiniteSemisimpleSkeleton.supportFPdim_centralizer_inter_reciprocity

#print axioms Paper18.Category.FiniteSemisimpleSkeleton.exists_positive_of_positive_source_centralizer
#print axioms Paper18.Category.GaloisBraidedExtension.exists_positiveRefinement

#print axioms Paper18.Category.DrinfeldCoendModules.equivalence
#print axioms Paper18.Category.DrinfeldNoPivotal.center_nondegenerate
#print axioms Paper18.Category.DrinfeldCoendModules.center_totalFPdim_noPivotal
#print axioms Paper18.Category.Drinfeld.factorizationEquivalenceNoPivotal
#print axioms Paper18.Category.ModuleInternalHom.componentRightModuleEquivalence
#print axioms Paper18.Category.GraphLagrangian.moduleOrbitSkeleton
#print axioms Paper18.Category.ModuleFunctor.wattsEndSkeleton
#print axioms Paper18.Category.BoundaryAutoequivalence.moduleFreeNatIsoMonoidal
#print axioms Paper18.Category.FixedBoundary.tannakianModule_monoidal_comparison_of_nondegenerate

#print axioms Paper18.Category.FixedBoundary.minimalBoundary_trivializable
#print axioms Paper18.Category.FixedBoundary.minimalBoundary_exists_monoidal_iso
#print axioms Paper18.Category.FixedBoundary.lemmaA1_boundary_rigidity
#print axioms Paper18.Category.spherical_extension_of_c2_minimal
#print axioms Paper18.Category.monoidalNatTransIso
#print axioms Paper18.Category.GraphPicard.capTranspose_tensor
#print axioms Paper18.Category.GraphPicard.mapped_tensor_evaluation

#print axioms Paper18.Category.GraphPicard.graphPositiveMonoidalEquivalenceOfNondegenerate
#print axioms Paper18.Category.GraphPicard.graphNegativeMonoidalEquivalenceOfNondegenerate
#print axioms Paper18.Category.SeparableAlgebra.orbitEnd_totalFPdim_fusion
#print axioms Paper18.Category.BalancedModuleCategory.balancedEquivalence
#print axioms Paper18.Category.CrossedBraidedGauging.CrossedBraiding.equivariant_nondegenerate
#print axioms Paper18.Category.CrossedExtension.quotientCenterAction
#print axioms Paper18.Category.CrossedExtension.quotientCenterDescentIso
#print axioms Paper18.Category.CrossedBraidedGauging.CrossedBraiding.centralizerIntegral_of_induced_tests
#print axioms Paper18.Category.GaloisBraidedExtension.ofCrossedGauging
#print axioms Paper18.Category.GraphPicard.graphAlgebraAdjointUnitIso
#print axioms Paper18.Category.GraphPicard.graphAdjointUnitSeparable

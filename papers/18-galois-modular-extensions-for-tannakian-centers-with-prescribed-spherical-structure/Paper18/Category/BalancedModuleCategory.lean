import Paper18.Category.BalancedModuleCategoryExtensionLinear

/-! # The actual balanced tensor product of internal module categories

The native category of actual left A/right B bimodules represents the
balanced product of left A-modules (with right ambient tensor action)
and right B-modules (with left ambient tensor action). The actual external
tensor, its balancing natural isomorphism, and both coherence laws are
constructed without a braiding or a pivotal structure.

For actual separable A and B and every target E with coequalizers,
`balancedEquivalence` is the proved equivalence between actual functors
out of the native model and actual balanced functors into E.
`BalancedFunctor.extension` is defined by actual coequalizers;
`extensionExternalNatIso` and `extensionExternalNatIso_balanced` prove its
actual external comparison and balancing square. Its monad-action laws
are derived from balancing, rather than supplied as extension premises.

Separately complex-linear input yields an actual additive complex-linear
extension. Actual module-category products for chosen Picard components,
and identification with their selected output components, remain a
separate construction; this file does not assume or assert those data.
-/

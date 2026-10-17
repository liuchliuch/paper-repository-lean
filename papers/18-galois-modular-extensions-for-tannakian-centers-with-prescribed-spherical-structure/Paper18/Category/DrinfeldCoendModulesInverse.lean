import Paper18.Category.DrinfeldCoendModulesInverseSkeleton
import Paper18.Category.DrinfeldCoendModulesInverseForget

/-! # The actual no-pivotal coend-module inverse and finite center skeleton

`fromModules` recovers a half-braiding from each actual module action by
rigid transposition. Its tensor law follows from actual module associativity
and the actual coend multiplication. Rigidity proves invertibility.

`centerRoundtripIso` and `moduleRoundtripIso` give the actual two roundtrips.
`equivalence` identifies the actual center with the actual modules over the
proved separable coend algebra. `centerSkeletonNoPivotal` transports the
resulting actual finite simple decompositions, with no pivotal input.
-/

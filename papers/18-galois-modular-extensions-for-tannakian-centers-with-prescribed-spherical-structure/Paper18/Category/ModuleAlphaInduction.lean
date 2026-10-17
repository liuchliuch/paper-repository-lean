import Paper18.Category.ModuleAlphaInductionMonoidal

/-! # Actual positive and negative alpha induction

`ModuleAlphaInduction.positive C M` and `negative C M` land in the actual
category of additive complex-linear strong native module endofunctors.
Their underlying functor is exactly the given native left action. Their
actual inverse lineators use, respectively, the positive braiding and the
inverse of the opposite braiding.

`positiveMop C M` and `negativeMop C M` are actual additive complex-linear
strong monoidal functors to the monoidal opposite of that category. This
is the conventional composition order; mathlib's native endofunctor
tensor has `F ⊗ G = F ⋙ G`. Neither construction assumes a pivotal
structure, a braiding on the acted-on category, or an alpha equivalence.
-/

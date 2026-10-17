import P31.QueryProgram
import P31.JensenGrowth
import P31.Schedule

/-!
# Explicit complementary-composite external input

The only algorithmic result imported from the literature is the objective-error
part of Diakonikolas--Guzmán [6, Theorem 2] (Theorem 2.1 in arXiv:2101.11041v2), its nonlogarithmic branch, specialized
as in P31 Section 2.1: q_src=p, lambda=mu, psi=H, x_init=c,
phi=powerAtom p c, eta=(mu/p)*delta^p, and m_0=A_0 M_0.
The source constants (including atom normalization) are absorbed into C(p,kappa).
At (p,kappa)=(2,2), the recurrence coefficient is interpreted as M_t=L.

This is an explicit input, not an axiom declaration. In particular its algorithm
constructor has no access to f, its values, its gradient, or an exact minimizer.
Only a run supplies gradient replies. The input guarantees objective error only;
its distance consequence is proved here from actual Jensen growth.
-/

noncomputable section
namespace P31
open QueryProgram

abbrev CompositeProx (V : Type*) := V → ℝ → ℝ → V

/-- Exactly the internal minimization assumed in Lemma 2.2. -/
def IsCompositeProx {ι : Type*} [Fintype ι] (p : ℝ)
    (H : (ι → ℝ) → ℝ) (center : ι → ℝ) (prox : CompositeProx (ι → ℝ)) : Prop :=
  ∀ g A m, 0 < A → 0 < m → ∀ y,
    coordinateFunctional g (prox g A m) + A * H (prox g A m) +
        m * powerAtom p center (prox g A m) ≤
      coordinateFunctional g y + A * H y + m * powerAtom p center y

/-- The fixed integer query ceiling corresponding to equation (2.7). -/
def compositeQueryBudget (C p κ L μ D δ : ℝ) : ℕ :=
  ⌈C * (1 + (L / (μ * δ ^ (p - κ))) ^ Schedule.beta p κ *
    (D / δ) ^ (κ * Schedule.beta p κ))⌉₊

/-- Explicit known external objective theorem. `C` depends only on `p,kappa`;
a dimension-uniform application supplies this interface with the same C for
all finite coordinate types. The call bound is fixed before any oracle reply.
There is no stage, path, distance, or terminal-gradient conclusion in this input. -/
structure ExternalComplementaryComposite (ι : Type*) [Fintype ι] (p κ C : ℝ) where
  routine : ((ι → ℝ) → ℝ) → (ι → ℝ) → ℝ → ℝ → ℝ → ℝ →
    CompositeProx (ι → ℝ) → Program (ι → ℝ) (ι → ℝ) (ι → ℝ)
  calls_le : ∀ H c L μ D δ prox oracle,
    0 < L → 0 < μ → 0 < D → 0 < δ → δ ≤ D →
    ((routine H c L μ D δ prox).run oracle).calls ≤ compositeQueryBudget C p κ L μ D δ
  objective_gap : ∀ H c L μ D δ prox,
    0 < L → 0 < μ → 0 < D → 0 < δ → δ ≤ D →
    LpPowerJensen p μ H → IsCompositeProx p H c prox →
    ∀ (f : (ι → ℝ) → ℝ) (grad : (ι → ℝ) → ι → ℝ) (zstar : ι → ℝ),
    ConvexOn ℝ Set.univ f →
    (∀ x, HasFDerivAt f (coordinateFunctional (grad x)) x) →
    (∀ x y, lpNorm (dualExponent p) (grad x - grad y) ≤
      L * lpNorm p (x-y) ^ (κ-1)) →
    (∀ y, f zstar + H zstar ≤ f y + H y) → lpNorm p (c-zstar) ≤ D →
    let z := ((routine H c L μ D δ prox).run grad).value
    f z + H z - (f zstar + H zstar) ≤ μ / p * δ ^ p

/-- The external objective guarantee implies actual distance contraction;
no distance or growth certificate is assumed. -/
theorem externalComposite_contraction {ι : Type*} [Fintype ι] {p κ C L μ D δ : ℝ}
    (engine : ExternalComplementaryComposite ι p κ C) (hp : 0 < p)
    (H : (ι → ℝ) → ℝ) (c : ι → ℝ) (prox : CompositeProx (ι → ℝ))
    (hL : 0 < L) (hμ : 0 < μ) (hD : 0 < D) (hδ : 0 < δ) (hδD : δ ≤ D)
    (hH : LpPowerJensen p μ H) (hprox : IsCompositeProx p H c prox)
    (f : (ι → ℝ) → ℝ) (grad : (ι → ℝ) → ι → ℝ) (zstar : ι → ℝ)
    (hf : ConvexOn ℝ Set.univ f)
    (hg : ∀ x, HasFDerivAt f (coordinateFunctional (grad x)) x)
    (hh : ∀ x y, lpNorm (dualExponent p) (grad x-grad y) ≤ L * lpNorm p (x-y)^(κ-1))
    (hz : ∀ y, f zstar + H zstar ≤ f y + H y) (hd : lpNorm p (c-zstar) ≤ D) :
    lpNorm p (((engine.routine H c L μ D δ prox).run grad).value-zstar) ≤ δ := by
  apply lpPowerJensen_stage_contraction hp hμ hδ.le (lpPowerJensen_add_convex hf hH) hz
  exact engine.objective_gap H c L μ D δ prox hL hμ hD hδ hδD hH hprox
    f grad zstar hf hg hh hz hd

/-- One source constant and one objective-only engine in every positive finite
dimension. This quantifier prevents C from depending on dimension. -/
abbrev ExternalCompositeFamily (p κ C : ℝ) :=
  ∀ d : ℕ, 0 < d → ExternalComplementaryComposite (Fin d) p κ C

end P31

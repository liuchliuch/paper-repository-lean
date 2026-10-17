import PsgEst.LowerBound
import PsgEst.Ergodicity

/-!
# The source minimax class and the spectral formalization

The source class consists of irreducible, aperiodic finite stochastic matrices
with a given stationary law `π`, stationary minimum at least `p`, and gap at
least `g`. For `g>0`, its estimation problem agrees exactly with the existing
`relativelyAccurate` and `nStar` definitions.

The stationary law is explicit in both formulations. This module does not
assert existence or uniqueness of that law for an arbitrary irreducible matrix;
that separate textbook theorem is not a hidden hypothesis in these equivalences.
-/

open Matrix BigOperators Real Finset Classical

namespace PsgEst

/-- Standard irreducibility, expressed by positive transition powers. -/
abbrev StandardIrreducible {d : ℕ} (S : Stoch d) : Prop := MatrixIrreducible S

/-- Standard aperiodicity: positive return lengths have gcd one. -/
abbrev StandardAperiodic {d : ℕ} (S : Stoch d) : Prop := MatrixAperiodic S

/-- Membership in the source class `C(d,p,g)`, with stationary law explicit. -/
def standardModelClass {d : ℕ} [NeZero d] (S : Stoch d) (st : Stationary S)
    (p g : ℝ) : Prop :=
  StandardIrreducible S ∧ StandardAperiodic S ∧
    p ≤ Stationary.star st ∧ g ≤ gammaPS S st

/-- Positive `g` makes the usual structural conditions automatic. -/
theorem standardModelClass_iff {d : ℕ} [NeZero d] (S : Stoch d)
    (st : Stationary S) (p g : ℝ) (hg : 0 < g) :
    standardModelClass S st p g ↔ p ≤ Stationary.star st ∧ g ≤ gammaPS S st := by
  constructor
  · intro h
    exact h.2.2
  · rintro ⟨hπ, hγ⟩
    have h := positive_gap_standard_properties S st (hg.trans_le hγ)
    exact ⟨h.1, h.2.1, hπ, hγ⟩

/-- Confidence-`2/3` relative accuracy on the standard source class, uniformly
over deterministic initial states. -/
def standardRelativelyAccurate (n d : ℕ) [NeZero d]
    (est : (Fin (n + 1) → Fin d) → ℝ) (p g ε : ℝ) : Prop :=
  ∀ (S : Stoch d) (st : Stationary S),
    StandardIrreducible S → StandardAperiodic S →
    p ≤ Stationary.star st → g ≤ gammaPS S st →
    ∀ x0 : Fin d,
      let mu0 : Fin d → ℝ := fun i => if i = x0 then 1 else 0
      2 / 3 ≤ pathMeasure S.P mu0
        {X | |est X - gammaPS S st| ≤ ε * gammaPS S st}

/-- Under positive `g`, source accuracy equals the existing spectral criterion. -/
theorem standardRelativelyAccurate_iff (n d : ℕ) [NeZero d]
    (est : (Fin (n + 1) → Fin d) → ℝ) (p g ε : ℝ) (hg : 0 < g) :
    standardRelativelyAccurate n d est p g ε ↔ relativelyAccurate n d est p g ε := by
  constructor
  · intro h S st hπ hγ x0
    have hs := positive_gap_standard_properties S st (hg.trans_le hγ)
    exact h S st hs.1 hs.2.1 hπ hγ x0
  · intro h S st hi ha hπ hγ x0
    exact h S st hπ hγ x0

/-- Minimax sample size defined directly on the standard source class. -/
noncomputable def standardNStar (d : ℕ) [NeZero d] (p g ε : ℝ) : ℕ :=
  sInf {n : ℕ | ∃ est : (Fin (n + 1) → Fin d) → ℝ,
    standardRelativelyAccurate n d est p g ε}

/-- The sets of admissible sample sizes agree pointwise. -/
theorem standard_sample_sizes_eq (d : ℕ) [NeZero d] (p g ε : ℝ) (hg : 0 < g) :
    {n : ℕ | ∃ est : (Fin (n + 1) → Fin d) → ℝ,
      standardRelativelyAccurate n d est p g ε} =
    {n : ℕ | ∃ est : (Fin (n + 1) → Fin d) → ℝ,
      relativelyAccurate n d est p g ε} := by
  ext n
  constructor
  · rintro ⟨est, h⟩
    exact ⟨est, (standardRelativelyAccurate_iff n d est p g ε hg).mp h⟩
  · rintro ⟨est, h⟩
    exact ⟨est, (standardRelativelyAccurate_iff n d est p g ε hg).mpr h⟩

/-- The infima, including their empty-set convention, agree exactly. -/
theorem standardNStar_eq_nStar (d : ℕ) [NeZero d] (p g ε : ℝ) (hg : 0 < g) :
    standardNStar d p g ε = nStar d p g ε := by
  unfold standardNStar nStar
  rw [standard_sample_sizes_eq d p g ε hg]

end PsgEst

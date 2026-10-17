import Paper27.Geometry.LineCocycles
import Mathlib.Tactic.Linarith

/-!
# The normal correction in Lemma 3.1

The proof constructs the numerical negative degree from the normal tensor
identity, applies the universal negative-degree section theorem, and then
substitutes into the actual covector factorization. No vanishing of β or
common-component dichotomy is taken as an external theorem.
-/
noncomputable section
namespace Paper27.Geometry

/-- Hom(N,T), specified by its actual frame transition functions. -/
structure HomLineCocycle {D : Curve} (N T : HolomorphicLineCocycle D) where
  bundle : HolomorphicLineCocycle D
  transition_eq : ∀ i j p, p ∈ D.chartDomain i → p ∈ D.chartDomain j →
    bundle.transition i j p = T.transition i j p / N.transition i j p

/-- The standard degree functor's Hom law, quantified over arbitrary bundles.
This is a separate external input, not the negative-degree conclusion used
for the particular normal correction. -/
def HomDegreeLaw (theory : LineBundleDegreeTheory) : Prop :=
  ∀ (D : Curve) (N T : HolomorphicLineCocycle D) (H : HomLineCocycle N T),
    theory.degree D H.bundle = theory.degree D T - theory.degree D N

/-- The precise negative Hom degree in §3 p.4 is derived rather than assumed. -/
theorem normal_hom_degree (theory : LineBundleDegreeTheory)
    (homLaw : HomDegreeLaw theory) (D : Curve)
    (N T : HolomorphicLineCocycle D) (H : HomLineCocycle N T)
    (n : ℕ) (hn : 2 ≤ n) (hN : theory.degree D N < 0)
    (htensor : (n : ℤ) * theory.degree D N = theory.degree D T) :
    theory.degree D H.bundle < 0 := by
  rw [homLaw D N T H, ← htensor, ← sub_one_mul]
  exact mul_neg_of_pos_of_neg (by omega : (0 : ℤ) < (n : ℤ) - 1) hN

/-- Once a holomorphic map on TX|D annihilates TD, its generic quotient
factorization is a section of Hom(N,T). The input below is its actual scalar
factorization in the local normal frames; the output is the covector identity
β=0 used in the source. -/
theorem normal_correction_vanishes (theory : LineBundleDegreeTheory)
    (homLaw : HomDegreeLaw theory) (D : Curve)
    (N T : HolomorphicLineCocycle D) (H : HomLineCocycle N T)
    (n : ℕ) (hn : 2 ≤ n) (hN : theory.degree D N < 0)
    (htensor : (n : ℤ) * theory.degree D N = theory.degree D T)
    (β : H.bundle.HolomorphicSection)
    (l₁ l₃ : D → (ℂ × ℂ) →ₗ[ℂ] ℂ) (c₁ c₃ : D → ℂ)
    (normal : D → D → (ℂ × ℂ) →ₗ[ℂ] ℂ)
    (hfactor : ∀ i p, p ∈ D.chartDomain i → ∀ v,
      l₃ p v - (c₃ p / c₁ p) * l₁ p v = β.coefficient i p * normal i p v) :
    ∀ p v, l₃ p v = (c₃ p / c₁ p) * l₁ p v := by
  have hnegative := normal_hom_degree theory homLaw D N T H n hn hN htensor
  have hzero := theory.negative_degree_no_section D H.bundle hnegative β
  intro p v
  have hp : p ∈ D.chartDomain p := mem_chart_source ℂ p
  have hb := hfactor p p hp v
  rw [hzero p p hp, zero_mul] at hb
  exact sub_eq_zero.mp hb

/-- Equal normal tensor powers have equal ramification indices because the
normal degree is nonzero. This covers all three pairs of Lemma 3.1. -/
theorem equal_ramification_indices {d t : ℤ} (hd : d < 0)
    (n₁₂ n₁₃ n₂₃ : ℕ)
    (h₁₂ : (n₁₂ : ℤ) * d = t) (h₁₃ : (n₁₃ : ℤ) * d = t)
    (h₂₃ : (n₂₃ : ℤ) * d = t) : n₁₂ = n₁₃ ∧ n₁₂ = n₂₃ := by
  have hd₀ : d ≠ 0 := ne_of_lt hd
  constructor
  · exact_mod_cast (mul_right_cancel₀ hd₀ (h₁₂.trans h₁₃.symm))
  · exact_mod_cast (mul_right_cancel₀ hd₀ (h₁₂.trans h₂₃.symm))

end Paper27.Geometry

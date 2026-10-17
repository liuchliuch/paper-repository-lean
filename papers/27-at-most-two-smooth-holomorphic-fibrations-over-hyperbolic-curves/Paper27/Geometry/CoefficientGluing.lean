import Paper27.Geometry.Objects
import Paper27.CompactCoefficient
import Paper27.Geometry.DifferentialRigidity

/-!
# The leading coefficient in the common-tangency case

The local coefficients in (5) are initially functions on different chart
neighbourhoods. The transformation identity is the one obtained by comparing
the nth Taylor terms. We cancel the nonzero coordinate differential, glue the
functions on the actual curve, prove the glued function holomorphic locally,
and use compactness to obtain one constant, as in §3 p.10.
-/
noncomputable section
open scoped Manifold Topology
open Filter
namespace Paper27.Geometry.CoefficientGluing

/-- Local holomorphic functions with the raw nth-jet transition identity glue
to one global nonzero constant different from one. The exclusions follow from
the two displayed leading coefficients, not from a global-constant assumption. -/
theorem leading_coefficient_constant (D : Curve) {I : Type*}
    (U : I → Set D) (hopen : ∀ i, IsOpen (U i))
    (hcover : ∀ p : D, ∃ i, p ∈ U i)
    (a : I → D → ℂ)
    (ha : ∀ i, MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (a i) (U i))
    (d : I → I → D → ℂ)
    (hd : ∀ i j p, p ∈ U i → p ∈ U j → d i j p ≠ 0)
    (htransition : ∀ i j p, p ∈ U i → p ∈ U j →
      a j p * d i j p = d i j p * a i p)
    (n : ℕ)
    (ha0 : ∀ i p, p ∈ U i → a i p ≠ 0)
    (hleading : ∀ i p, p ∈ U i → (n : ℂ) * (a i p - 1) ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ c ≠ 1 ∧ ∀ i p, p ∈ U i → a i p = c := by
  let chosen (p : D) : I := Classical.choose (hcover p)
  have hchosen (p : D) : p ∈ U (chosen p) := Classical.choose_spec (hcover p)
  have hagree (i j : I) (p : D) (hi : p ∈ U i) (hj : p ∈ U j) :
      a i p = a j p := by
    apply (mul_right_cancel₀ (hd i j p hi hj))
    exact (mul_comm _ _).trans (htransition i j p hi hj).symm
  let A : D → ℂ := fun p => a (chosen p) p
  have hA_local (i : I) (p : D) (hp : p ∈ U i) : A p = a i p :=
    hagree (chosen p) i p (hchosen p) hp
  have hA : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) A := by
    intro p
    let i := chosen p
    have hp : p ∈ U i := hchosen p
    have halocal := (ha i).mdifferentiableAt ((hopen i).mem_nhds hp)
    apply halocal.congr_of_eventuallyEq
    filter_upwards [(hopen i).mem_nhds hp] with q hq
    exact hA_local i q hq
  have hA0 (p : D) : A p ≠ 0 := ha0 (chosen p) p (hchosen p)
  have hA1 (p : D) : A p ≠ 1 :=
    DifferentialRigidity.leading_coefficient_ne_one (hleading (chosen p) p (hchosen p))
  obtain ⟨c, hc0, hc1, hc⟩ := Paper27.CompactCoefficient.exists_constant A hA hA0 hA1
  refine ⟨c, hc0, hc1, fun i p hp => ?_⟩
  exact (hA_local i p hp).symm.trans (hc p)

end Paper27.Geometry.CoefficientGluing

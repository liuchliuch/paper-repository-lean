import Paper20.InfinitesimalCentral
import Paper20.WalkTrace

namespace Paper20.HeckeTraceAlgebra
open Polynomial Matrix Finset Paper20.HeckeMatrices Paper20.HeckeWalkExpansion
open Paper20.HeckeSpecialization Paper20.HeckeParameterPolynomial Paper20.WalkTrace
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

lemma transpositionSum_apply (r : ℕ) (p : State r) :
    transpositionSum r p=if p.IsSwap then 1 else 0 := by
  classical
  unfold transpositionSum generator
  rw [Finsupp.finset_sum_apply]
  simp only [MonoidAlgebra.single,Finsupp.single_apply]
  by_cases hp : p.IsSwap
  · rw [if_pos hp]
    rw [Finset.sum_eq_single (⟨p,hp⟩:P20Objects.Transposition r)]
    · simp
    · intro q hq hne
      have hn : p ≠ q.val := by
        intro he
        exact hne (Subtype.ext he.symm)
      simp [hn,Ne.symm hn]
    · intro hn
      exact False.elim (hn (mem_univ _))
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro q hq
    have hn : p ≠ q.val := by
      intro he
      exact hp (he ▸ q.property)
    simp [hn,Ne.symm hn]

lemma infinitesimal_regular_entry (r : ℕ) (hr : 1 ≤ r) (s t : State r) :
    infinitesimalFullTwist r s t=if (s*t⁻¹).IsSwap then 1 else 0 := by
  have he := specialization_entry r (incrementQuotient r)
    (incrementQuotient_mem r hr) s t
  rw [specialize_incrementQuotient,
    ← specialize_apply r (incrementQuotient r) (s*t⁻¹) 1,
    specialize_incrementQuotient,infinitesimal_identity_column] at he
  exact he

/-- The genuine derivative of the actual full twist is exactly the
ordinary regular representation of the sum of ALL actual transpositions.
This is derived from single-stay support, centrality, and the exact
simple-transposition coefficient, without a spectral substitution. -/
theorem infinitesimalFullTwist_eq_transpositionSum (r : ℕ) (hr : 1 ≤ r) :
    (Int.castRingHom ℚ).mapMatrix (infinitesimalFullTwist r)=
      regularMatrix (transpositionSum r) := by
  apply Matrix.ext
  intro s t
  change (infinitesimalFullTwist r s t:ℚ)=_
  rw [infinitesimal_regular_entry r hr s t,regularMatrix,transpositionSum_apply]
  split_ifs <;> rfl

/-- Every actual even infinitesimal full-twist matrix moment is the
independently defined cardinal of actual ordered transposition returns. -/
theorem infinitesimalFullTwist_returns (r h : ℕ) (hr : 1 ≤ r) :
    ((infinitesimalFullTwist r^(2*h)) 1 1:ℚ)=(P20Objects.transpositionReturns r h:ℚ) := by
  have he := congrFun (congrFun
    (map_pow ((Int.castRingHom ℚ).mapMatrix) (infinitesimalFullTwist r) (2*h)) 1) 1
  change (((infinitesimalFullTwist r^(2*h)) 1 1:ℤ):ℚ)=_ at he
  rw [infinitesimalFullTwist_eq_transpositionSum r hr,← regularMatrix_pow] at he
  rw [he,regularMatrix]
  simp only [inv_one,mul_one]
  exact (transpositionReturns_eq_identity_coeff r h).symm

/-- The genuine Hecke exponent-polynomial leading coefficient is the
actual transposition return cardinal divided by (2h)!, for every rank
and order. It is not the still-separate partition spectral formula. -/
theorem exponentPolynomial_top_actual_returns (r h : ℕ) (hr : 1 ≤ r) :
    (exponentPolynomial r (2*h)).coeff (2*h)=
      (P20Objects.transpositionReturns r h:ℚ)/((2*h).factorial:ℚ) := by
  rw [exponentPolynomial_top_matrix,infinitesimalFullTwist_returns r h hr]

end
end Paper20.HeckeTraceAlgebra

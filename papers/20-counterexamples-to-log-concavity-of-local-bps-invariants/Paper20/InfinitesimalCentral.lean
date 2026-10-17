import Paper20.InfinitesimalSupport

namespace Paper20.HeckeTraceAlgebra
open Polynomial Matrix Finset Paper20.HeckeMatrices Paper20.HeckeWalkExpansion
open Paper20.HeckeSpecialization Paper20.HeckeParameterPolynomial
open Paper20.OneStayTransposition
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- Division of Omega-1 by z preserves its actual centrality. -/
theorem incrementQuotient_central (r : ℕ) (hr : 1 ≤ r) (A : Mat r) (hA : A ∈ algebra r) :
    Commute (incrementQuotient r) A := by
  have he := (fullTwist_central r A hA).eq
  rw [fullTwist_decompose r hr] at he
  simp only [add_mul,mul_add,one_mul,mul_one,Matrix.smul_mul,Matrix.mul_smul] at he
  have hc : (Polynomial.X:ℤ[X]) • (incrementQuotient r*A)=
      (Polynomial.X:ℤ[X]) • (A*incrementQuotient r) := add_left_cancel he
  apply Matrix.ext
  intro s t
  have hs := congrFun (congrFun hc s) t
  exact mul_left_cancel₀ (Polynomial.X_ne_zero : (Polynomial.X:ℤ[X]) ≠ 0) hs

lemma permutationMatrix_entry {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (p s t : G) : permutationMatrix p s t=if p=s*t⁻¹ then 1 else 0 := by
  have he : t=p⁻¹*s ↔ p=s*t⁻¹ := by
    constructor
    · intro h
      calc
        p = p*t*t⁻¹ := by simp [mul_assoc]
        _ = s*t⁻¹ := by rw [h,mul_inv_cancel_left]
    · intro h
      rw [h,_root_.mul_inv_rev]
      simp [mul_assoc]
  simp only [permutationMatrix,he]

/-- Every specialized actual Hecke matrix is the genuine ordinary left
regular matrix of its identity-column coefficients. -/
theorem specialization_entry (r : ℕ) (A : Mat r) (hA : A ∈ algebra r) (s t : State r) :
    specialize r A s t=(A (s*t⁻¹) 1).coeff 0 := by
  classical
  have he := congrArg (fun M : Mat r => (specialize r M) s t)
    (identity_column_expansion r A hA)
  dsimp only at he
  rw [map_sum] at he
  simp only [Matrix.sum_apply] at he
  have ht (p : State r) :
      specialize r (A p 1 • basisMatrix r p) s t=
        (A p 1).coeff 0*(if p=s*t⁻¹ then 1 else 0) := by
    rw [specialize_apply]
    change (A p 1*basisMatrix r p s t).coeff 0=_
    rw [Polynomial.mul_coeff_zero,← specialize_apply r (basisMatrix r p) s t,
      specialize_basis,permutationMatrix_entry]
  simp_rw [ht] at he
  simpa only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',mem_univ,ite_true] using he

/-- The genuine infinitesimal full-twist coefficient is constant on
actual conjugacy classes, derived from actual centrality and regularity. -/
theorem infinitesimal_conjugate (r : ℕ) (hr : 1 ≤ r) (g p : State r) :
    infinitesimalFullTwist r (g*p*g⁻¹) 1=infinitesimalFullTwist r p 1 := by
  have hc := incrementQuotient_central r hr (basisMatrix r g) (basisMatrix_mem r g)
  have hm := congrArg (specialize r) hc.eq
  simp only [map_mul,specialize_basis,specialize_incrementQuotient] at hm
  have he := congrArg (fun M : Matrix (State r) (State r) ℤ => M.mulVec (delta (1:State r))) hm
  dsimp only at he
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,
    permutationMatrix_delta,permutationMatrix_mulVec] at he
  have hs := congrFun he (g*p)
  simp only [mulVec_delta,inv_mul_cancel_left] at hs
  have hentry := specialization_entry r (incrementQuotient r)
    (incrementQuotient_mem r hr) (g*p) g
  rw [specialize_incrementQuotient,← specialize_apply r (incrementQuotient r)
    (g*p*g⁻¹) 1,specialize_incrementQuotient] at hentry
  exact hentry.symm.trans hs

/-- Every actual transposition has coefficient exactly one in the genuine
infinitesimal full twist. -/
theorem infinitesimal_transposition (r : ℕ) (p : State r) (hp : p.IsSwap) :
    infinitesimalFullTwist r p 1=1 := by
  obtain ⟨a,b,hab,heq⟩ := hp
  have hr : 2 ≤ r := by
    have ha := a.isLt
    have hb := b.isLt
    have hn : a.val ≠ b.val := fun h => hab (Fin.ext h)
    omega
  let i : Fin (r-1) := ⟨0,by omega⟩
  obtain ⟨x,y,hxy,hs⟩ := swapAt_isSwap i
  obtain ⟨g,hg⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap hxy hab)
  rw [heq,← hg,← hs]
  rw [infinitesimal_conjugate r (by omega),infinitesimal_simple_coordinate]

theorem infinitesimal_identity_column (r : ℕ) (p : State r) :
    infinitesimalFullTwist r p 1=if p.IsSwap then 1 else 0 := by
  classical
  by_cases hp : p.IsSwap
  · rw [if_pos hp,infinitesimal_transposition r p hp]
  · rw [if_neg hp,infinitesimal_support r p hp]

end
end Paper20.HeckeTraceAlgebra

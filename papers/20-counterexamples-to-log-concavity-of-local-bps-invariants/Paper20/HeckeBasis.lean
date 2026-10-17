import Paper20.HeckeSorting
import Paper20.HeckeDelta

namespace Paper20.HeckeTraceAlgebra
open Polynomial Matrix Paper20.BraidWalk Paper20.HeckeOperators Paper20.HeckeMatrices
open Paper20.HeckeWalkExpansion Paper20.HeckeSorting
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- Actual descent sorting constructs a matrix taking the identity vector
to every permutation vector in the generated left Hecke algebra. -/
theorem exists_left_basis (r : ℕ) (p : State r) :
    ∃ A : Mat r, A ∈ algebra r ∧ A.mulVec (delta (1 : State r))=delta p := by
  have aux : ∀ n : ℕ, ∀ p : State r, potential p=n →
      ∃ A : Mat r, A ∈ algebra r ∧ A.mulVec (delta (1 : State r))=delta p := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro p hn
      by_cases hp : p=1
      · exact ⟨1,(algebra r).one_mem,by simp [hp]⟩
      · obtain ⟨i,hd⟩ := exists_descent p hp
        have hlt : potential (adjacentMove i p) < n := by
          rw [← hn]
          exact potential_descent_lt i p hd
        obtain ⟨A,hA,he⟩ := ih _ hlt (adjacentMove i p) rfl
        have hi : T r i ∈ algebra r := Algebra.subset_adjoin (Set.mem_range_self i)
        refine ⟨T r i*A,(algebra r).mul_mem hi hA,?_⟩
        rw [← Matrix.mulVec_mulVec,he,T,generator_mulVec]
        have ha : ¬descent i (adjacentMove i p) := by
          rw [adjacent_descent_flip]
          exact not_not.mpr hd
        have hx := operator_delta_ascent (adjacentMove i) (descent i)
          (adjacentMove_involutive i) (Polynomial.X:ℤ[X]) (adjacentMove i p) ha
        simpa only [adjacentMove_involutive i p] using hx
  exact aux (potential p) p rfl

/-- Right descent sorting supplies every basis vector with a matrix that
commutes with the whole actual left Hecke algebra. -/
theorem exists_right_basis (r : ℕ) (p : State r) :
    ∃ B : Mat r, (∀ A : Mat r, A ∈ algebra r → Commute A B) ∧
      B.mulVec (delta (1 : State r))=delta p := by
  have aux : ∀ n : ℕ, ∀ p : State r, potential p.symm=n →
      ∃ B : Mat r, (∀ A : Mat r, A ∈ algebra r → Commute A B) ∧
        B.mulVec (delta (1 : State r))=delta p := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro p hn
      by_cases hp : p=1
      · exact ⟨1,fun A _ => Commute.one_right A,by simp [hp]⟩
      · have hp' : p.symm ≠ 1 := by
          intro h
          exact hp (congrArg (fun q : State r => q.symm) h)
        obtain ⟨i,hd⟩ := exists_descent p.symm hp'
        have hright : rightDescent i p := hd
        have hlt : potential (rightMove i p).symm < n := by
          rw [rightMove_symm,← hn]
          exact potential_descent_lt i p.symm hd
        obtain ⟨B,hB,he⟩ := ih _ hlt (rightMove i p) rfl
        refine ⟨rightT r i*B,?_,?_⟩
        · intro A hA
          exact (algebra_commutes_right r i A hA).mul_right (hB A hA)
        · rw [← Matrix.mulVec_mulVec,he,rightT,generator_mulVec]
          have ha : ¬rightDescent i (rightMove i p) := by
            rw [rightDescent_flip]
            exact not_not.mpr hright
          have hx := operator_delta_ascent (rightMove i) (rightDescent i)
            (rightMove_involutive i) (Polynomial.X:ℤ[X]) (rightMove i p) ha
          simpa only [rightMove_involutive i p] using hx
  exact aux (potential p.symm) p rfl

/-- Faithfulness: a matrix in the actual Hecke algebra is determined by
its identity column. Right cyclicity makes every other column recoverable. -/
theorem eq_of_identity_column (r : ℕ) (A B : Mat r) (hA : A ∈ algebra r) (hB : B ∈ algebra r)
    (he : A.mulVec (delta (1 : State r))=B.mulVec (delta (1 : State r))) : A=B := by
  apply Matrix.ext
  intro s t
  obtain ⟨C,hC,hδ⟩ := exists_right_basis r t
  have hv : A.mulVec (delta t)=B.mulVec (delta t) := by
    calc
      _ = A.mulVec (C.mulVec (delta (1 : State r))) := by rw [hδ]
      _ = (A*C).mulVec (delta (1 : State r)) := by rw [Matrix.mulVec_mulVec]
      _ = (C*A).mulVec (delta (1 : State r)) := by rw [(hC A hA).eq]
      _ = C.mulVec (A.mulVec (delta (1 : State r))) := by rw [Matrix.mulVec_mulVec]
      _ = C.mulVec (B.mulVec (delta (1 : State r))) := by rw [he]
      _ = (C*B).mulVec (delta (1 : State r)) := by rw [Matrix.mulVec_mulVec]
      _ = (B*C).mulVec (delta (1 : State r)) := by rw [(hC B hB).eq]
      _ = B.mulVec (C.mulVec (delta (1 : State r))) := by rw [Matrix.mulVec_mulVec]
      _ = _ := by rw [hδ]
  have hx := congrFun hv s
  simpa only [mulVec_delta] using hx

def basisMatrix (r : ℕ) (p : State r) : Mat r := Classical.choose (exists_left_basis r p)

theorem basisMatrix_mem (r : ℕ) (p : State r) : basisMatrix r p ∈ algebra r :=
  (Classical.choose_spec (exists_left_basis r p)).1

theorem basisMatrix_delta (r : ℕ) (p : State r) :
    (basisMatrix r p).mulVec (delta (1 : State r))=delta p :=
  (Classical.choose_spec (exists_left_basis r p)).2

theorem basisMatrix_one (r : ℕ) : basisMatrix r 1=1 := by
  apply eq_of_identity_column r _ _ (basisMatrix_mem r 1) (algebra r).one_mem
  rw [basisMatrix_delta,Matrix.one_mulVec]

/-- The canonical trace has exactly the required standard-basis
normalization, for every actual permutation. -/
theorem trace_basisMatrix (r : ℕ) (p : State r) :
    trace r (basisMatrix r p)=if p=1 then 1 else 0 := by
  have he := congrFun (basisMatrix_delta r p) 1
  simpa only [trace,mulVec_delta,delta,eq_comm] using he

end
end Paper20.HeckeTraceAlgebra

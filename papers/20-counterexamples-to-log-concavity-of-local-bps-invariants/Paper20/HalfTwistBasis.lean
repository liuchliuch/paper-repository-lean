import Paper20.HalfTwistMatrix
import Paper20.PrefixSweep

namespace Paper20.HalfTwistMatrix
open Polynomial Matrix Paper20.HeckeOperators Paper20.HeckeMatrices
open Paper20.HeckeWalkExpansion Paper20.BraidWalk Paper20.PrefixSweep
open Paper20.HalfTwistWord
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

def sweepMatrix (r m t : ℕ) : Matrix (Equiv.Perm (Fin r)) (Equiv.Perm (Fin r)) ℤ[X] :=
  ((List.range' (m-t) t).map (generator r)).prod

lemma sweepMatrix_zero (r m : ℕ) : sweepMatrix r m 0=1 := by simp [sweepMatrix]

lemma sweepMatrix_succ (r m t : ℕ) (ht : t < m) :
    sweepMatrix r m (t+1)=generator r (m-1-t)*sweepMatrix r m t := by
  have hj : m-(t+1)=m-1-t := by omega
  have hs : m-(t+1)+1=m-t := by omega
  unfold sweepMatrix
  rw [List.range'_succ,List.map_cons,List.prod_cons,hs,hj]

lemma sweepMatrix_full (r m : ℕ) : sweepMatrix r m m=up (generator r) m := by
  simp only [sweepMatrix,Nat.sub_self,up,List.range_eq_range']

/-- During the whole insertion sweep each genuine generator is an ascent,
so there is exactly the moved basis vector and no stay correction. -/
theorem sweepMatrix_delta (r m : ℕ) (hm : m < r) (t : ℕ) (ht : t ≤ m) :
    (sweepMatrix r m t).mulVec (delta (reversePrefix r m hm.le))=
      delta (state r m hm t) := by
  induction t with
  | zero => simp only [sweepMatrix_zero,Matrix.one_mulVec,state]
  | succ t ih =>
    have ht' : t < m := by omega
    have hi : m-1-t < r-1 := by omega
    rw [sweepMatrix_succ r m t ht',← Matrix.mulVec_mulVec,ih (by omega),
      generator,dif_pos hi,T,generator_mulVec]
    have he := operator_delta_ascent (adjacentMove (⟨m-1-t,hi⟩:Fin (r-1)))
      (descent ⟨m-1-t,hi⟩) (adjacentMove_involutive _) (Polynomial.X:ℤ[X])
      (state r m hm t) (state_ascent r m hm t ht')
    simpa only [state,adjacentNat,dif_pos hi] using he

theorem up_delta (r m : ℕ) (hm : m < r) :
    (up (generator r) m).mulVec (delta (reversePrefix r m hm.le))=
      delta (reversePrefix r (m+1) (by omega)) := by
  rw [← sweepMatrix_full,sweepMatrix_delta r m hm m le_rfl,state_final]

/-- Every triangular partial half twist sends the unit permutation's
standard basis vector to the corresponding reversed prefix. -/
theorem triangle_delta (r n : ℕ) (hn : n < r) :
    (triangle (generator r) n).mulVec (delta (1 : Equiv.Perm (Fin r)))=
      delta (reversePrefix r (n+1) (by omega)) := by
  induction n with
  | zero => simp only [triangle,word,List.map_nil,List.prod_nil,Matrix.one_mulVec,
      reversePrefix_one r (by omega)]
  | succ n ih =>
    rw [triangle_mirror _ (generator_far r) n,← Matrix.mulVec_mulVec,ih (by omega),
      up_delta r (n+1) hn]

/-- The actual half-twist matrix has exactly the longest-permutation basis
vector in its identity column, derived from the explicit ascent sweep. -/
theorem halfTwist_delta (r : ℕ) (hr : 1 ≤ r) :
    (halfTwist r).mulVec (delta (1 : Equiv.Perm (Fin r)))=delta Fin.revPerm := by
  rw [halfTwist_eq_triangle]
  have hn : r-1 < r := by omega
  have he := triangle_delta r (r-1) hn
  have hr' : r-1+1=r := by omega
  simpa only [hr',reversePrefix_full] using he

end
end Paper20.HalfTwistMatrix

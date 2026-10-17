import Paper20.HeckeBasis

namespace Paper20.HeckeTraceAlgebra
open Module Polynomial Matrix Paper20.BraidWalk Paper20.HeckeOperators Paper20.HeckeMatrices
open Paper20.HeckeWalkExpansion
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

lemma operator_delta {S R : Type*} [CommRing R] (move : S → S) (desc : S → Prop)
    (hinv : Function.Involutive move) (z : R) (p : S) :
    operator move desc z (delta p)=delta (move p)+(if desc p then z • delta p else 0) := by
  funext s
  have he : move s=p ↔ s=move p := by
    constructor
    · intro h; have hx := congrArg move h; simpa only [hinv s] using hx
    · intro h; rw [h,hinv p]
  have hm : (delta p (move s):R)=delta (move p) s := by
    simp only [delta,he]
  rw [operator,hm]
  by_cases hs : s=p
  · subst s
    by_cases hd : desc p <;> simp [hd,delta]
  · by_cases hd : desc p <;> simp [hd,delta,hs]

/-- The same standard-basis multiplication rule as the source Hecke
algebra, derived for the concrete permutation-indexed basis. -/
theorem T_mul_basisMatrix (r : ℕ) (i : Fin (r-1)) (p : State r) :
    T r i*basisMatrix r p = basisMatrix r (adjacentMove i p)+
      (if descent i p then (Polynomial.X:ℤ[X]) • basisMatrix r p else 0) := by
  have hi : T r i ∈ algebra r := Algebra.subset_adjoin (Set.mem_range_self i)
  have hm : basisMatrix r (adjacentMove i p)+
      (if descent i p then (Polynomial.X:ℤ[X]) • basisMatrix r p else 0) ∈ algebra r := by
    apply (algebra r).add_mem (basisMatrix_mem r _)
    split_ifs
    · exact (algebra r).smul_mem (basisMatrix_mem r p) Polynomial.X
    · exact (algebra r).zero_mem
  apply eq_of_identity_column r _ _ ((algebra r).mul_mem hi (basisMatrix_mem r p)) hm
  rw [← Matrix.mulVec_mulVec,basisMatrix_delta,T,generator_mulVec,
    operator_delta _ _ (adjacentMove_involutive i)]
  by_cases hd : descent i p
  · simp only [hd,↓reduceIte,Matrix.add_mulVec,Matrix.smul_mulVec,basisMatrix_delta]
  · simp only [hd,↓reduceIte,add_zero,basisMatrix_delta]

/-- Identity-column coordinates on the actual generated Hecke algebra. -/
def identityColumn (r : ℕ) : algebra r →ₗ[ℤ[X]] (State r → ℤ[X]) where
  toFun A := (A:Mat r).mulVec (delta (1 : State r))
  map_add' A B := by
    change ((A:Mat r)+(B:Mat r)).mulVec _ = _
    exact Matrix.add_mulVec _ _ _
  map_smul' c A := by
    change (c • (A:Mat r)).mulVec _ = _
    exact Matrix.smul_mulVec _ _ _

theorem identityColumn_injective (r : ℕ) : Function.Injective (identityColumn r) := by
  intro A B h
  apply Subtype.ext
  exact eq_of_identity_column r A.val B.val A.property B.property h

theorem identityColumn_surjective (r : ℕ) : Function.Surjective (identityColumn r) := by
  intro f
  let M : Mat r := ∑ p : State r, f p • basisMatrix r p
  have hM : M ∈ algebra r := by
    apply (algebra r).sum_mem
    intro p hp
    exact (algebra r).smul_mem (basisMatrix_mem r p) (f p)
  refine ⟨⟨M,hM⟩,?_⟩
  change M.mulVec (delta (1 : State r))=f
  rw [show M=∑ p : State r, f p • basisMatrix r p from rfl,Matrix.sum_mulVec]
  simp_rw [Matrix.smul_mulVec,basisMatrix_delta]
  funext s
  simp [Finset.sum_apply,Pi.smul_apply,delta,smul_eq_mul,mul_ite]

def identityColumnEquiv (r : ℕ) : algebra r ≃ₗ[ℤ[X]] (State r → ℤ[X]) :=
  LinearEquiv.ofBijective (identityColumn r)
    ⟨identityColumn_injective r,identityColumn_surjective r⟩

/-- A genuine free standard basis, indexed by every actual permutation.
This proves the regular model has exactly r! basis elements. -/
def standardBasis (r : ℕ) : Basis (State r) ℤ[X] (algebra r) :=
  (Pi.basisFun ℤ[X] (State r)).map (identityColumnEquiv r).symm

theorem standardBasis_matrix (r : ℕ) (p : State r) :
    ((standardBasis r p : algebra r):Mat r)=basisMatrix r p := by
  apply eq_of_identity_column r _ _ (standardBasis r p).property (basisMatrix_mem r p)
  rw [basisMatrix_delta]
  have hpi : Pi.basisFun ℤ[X] (State r) p=delta p := by
    funext s
    simp [Pi.basisFun_apply,Pi.single_apply,delta,eq_comm]
  change identityColumnEquiv r (standardBasis r p)=delta p
  rw [standardBasis,Basis.map_apply,LinearEquiv.apply_symm_apply,hpi]

def canonicalTrace (r : ℕ) : algebra r →ₗ[ℤ[X]] ℤ[X] where
  toFun A := trace r A.val
  map_add' A B := rfl
  map_smul' c A := rfl

theorem canonicalTrace_basis (r : ℕ) (p : State r) :
    canonicalTrace r (standardBasis r p)=if p=1 then 1 else 0 := by
  change trace r ((standardBasis r p : algebra r):Mat r)=_
  rw [standardBasis_matrix,trace_basisMatrix]

theorem canonicalTrace_cyclic (r : ℕ) (A B : algebra r) :
    canonicalTrace r (A*B)=canonicalTrace r (B*A) :=
  trace_mul_comm r A.val B.val A.property B.property

theorem standardBasis_index_card (r : ℕ) : Fintype.card (State r)=r.factorial := by
  simp [State,Fintype.card_perm]

end
end Paper20.HeckeTraceAlgebra

import Paper28.BassSerreObjectInput

/-! Native branch restrictions to the two actual factor edge sets. The
central branch recovers the factor coordinate up to a representative;
every other vertex routes all factor edges into one branch. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph
variable {G : Type} [Group G] {A B : Subgroup G} (T : BassSerreObject A B)

def factorBaseCoset (A : Subgroup G) : G ⧸ A := QuotientGroup.mk 1

def factorBaseRepresentative (A : Subgroup G) : A :=
  ⟨(factorBaseCoset A).out,by
    have h := QuotientGroup.leftRel_apply.mp (Quotient.exact (QuotientGroup.out_eq' (factorBaseCoset A)).symm)
    simpa only [factorBaseCoset,inv_one,one_mul] using h⟩

theorem factor_coset_identity (a : A) : (QuotientGroup.mk a.val : G ⧸ A) = factorBaseCoset A :=
  Quotient.sound (QuotientGroup.leftRel_apply.mpr (by simpa only [mul_one] using A.inv_mem a.property))

theorem bassSerreBranchB_incident (v : G ⧸ B) (b : B) : bassSerreBranchB T v (v.out*b.val) = b := by
  apply (T.rightLabel v).injective
  rw [bassSerreBranchB,Equiv.apply_symm_apply]
  apply Subtype.ext
  have hq : QuotientGroup.mk (v.out*b.val) = v := by
    calc
      _ = (QuotientGroup.mk v.out : G ⧸ B) := Quotient.sound (QuotientGroup.leftRel_apply.mpr (by simp))
      _ = v := QuotientGroup.out_eq' v
  have hb : (bassSerreGraph A B).Adj (Sum.inr v) (bassSerreLeft A B (v.out*b.val)) := ⟨v.out*b.val,rfl,hq⟩
  have he : bassSerreEdge A B (v.out*b.val) = ⟨s(Sum.inr v,bassSerreLeft A B (v.out*b.val)),hb⟩ := by
    apply Subtype.ext
    change s(_,Sum.inr (QuotientGroup.mk (v.out*b.val))) = _
    rw [hq]
    exact Sym2.eq_swap
  rw [he,treeBranch_incident,T.rightLabel_formula]

theorem bassSerreFactorBranchA_center (a : A) :
    bassSerreBranchA T (factorBaseCoset A) a.val = (factorBaseRepresentative A)⁻¹*a := by
  have h := bassSerreBranchA_incident T (factorBaseCoset A) ((factorBaseRepresentative A)⁻¹*a)
  change bassSerreBranchA T (factorBaseCoset A)
    ((factorBaseCoset A).out*((factorBaseCoset A).out⁻¹*a.val)) = _ at h
  simpa only [mul_inv_cancel_left] using h

theorem bassSerreFactorBranchB_center (b : B) :
    bassSerreBranchB T (factorBaseCoset B) b.val = (factorBaseRepresentative B)⁻¹*b := by
  have h := bassSerreBranchB_incident T (factorBaseCoset B) ((factorBaseRepresentative B)⁻¹*b)
  change bassSerreBranchB T (factorBaseCoset B)
    ((factorBaseCoset B).out*((factorBaseCoset B).out⁻¹*b.val)) = _ at h
  simpa only [mul_inv_cancel_left] using h

theorem treeBranches_common_endpoint {V E : Type*} (Q : SimpleGraph V) (hQ : Q.IsTree)
    (v c : V) (hc : c ≠ v) (edges : E → Q.edgeSet) (hEdges : ∀ e, c ∈ (edges e).val) :
    ∃ w : Q.neighborSet v, ∀ e, treeBranch Q hQ v (edges e) = w :=
  ⟨firstNeighbor Q hQ v c hc,fun e => treeBranch_eq_firstNeighbor_endpoint Q hQ v (edges e) c (hEdges e) hc⟩

theorem bassSerreFactorA_branches_constant (v : BassSerreVertex A B)
    (hv : v ≠ Sum.inl (factorBaseCoset A)) :
    ∃ w : (bassSerreGraph A B).neighborSet v, ∀ a : A,
      treeBranch (bassSerreGraph A B) T.isTree v (bassSerreEdge A B a.val) = w := by
  apply treeBranches_common_endpoint _ T.isTree v (.inl (factorBaseCoset A)) hv.symm
  intro a
  have he : bassSerreLeft A B a.val = Sum.inl (factorBaseCoset A) := congrArg Sum.inl (factor_coset_identity a)
  rw [← he]
  exact Sym2.mem_mk_left _ _

theorem bassSerreFactorB_branches_constant (v : BassSerreVertex A B)
    (hv : v ≠ Sum.inr (factorBaseCoset B)) :
    ∃ w : (bassSerreGraph A B).neighborSet v, ∀ b : B,
      treeBranch (bassSerreGraph A B) T.isTree v (bassSerreEdge A B b.val) = w := by
  apply treeBranches_common_endpoint _ T.isTree v (.inr (factorBaseCoset B)) hv.symm
  intro b
  have he : bassSerreRight A B b.val = Sum.inr (factorBaseCoset B) := congrArg Sum.inr (factor_coset_identity b)
  rw [← he]
  exact Sym2.mem_mk_right _ _

end Paper28

import ELV.LpHilbert
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Stack finite query times into the ancillary control index. -/
noncomputable section
namespace ELV.Query
variable {I J E : Type*} [Fintype I] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def timeStack (v : I → lp (fun _ : J => E) 2) : lp (fun _ : I × J => E) 2 :=
  ⟨fun p => v p.1 p.2,by
    apply memℓp_gen
    have hs : Summable (fun p : I × J => ‖v p.1 p.2‖ ^ 2) :=
      (summable_prod_of_nonneg (fun _ => sq_nonneg _)).2
        ⟨fun i => lp_summable_sq (v i),(hasSum_fintype _).summable⟩
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hs⟩

@[simp] theorem timeStack_apply (v : I → lp (fun _ : J => E) 2) (i : I) (j : J) :
    timeStack v (i,j) = v i j := rfl

/-- The stacked norm is exactly the sum of the true query-time norms. -/
theorem timeStack_norm_sq (v : I → lp (fun _ : J => E) 2) :
    ‖timeStack v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [lp_norm_sq]
  change (∑' p : I × J, ‖v p.1 p.2‖ ^ 2) = _
  have hs : Summable (fun p : I × J => ‖v p.1 p.2‖ ^ 2) :=
    (summable_prod_of_nonneg (fun _ => sq_nonneg _)).2
      ⟨fun i => lp_summable_sq (v i),(hasSum_fintype _).summable⟩
  rw [hs.tsum_prod,tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  exact (lp_norm_sq (v i)).symm

/-- Cross-instance inner products are the finite query-time sum. -/
theorem timeStack_inner (v w : I → lp (fun _ : J => E) 2) :
    inner ℂ (timeStack v) (timeStack w) = ∑ i, inner ℂ (v i) (w i) := by
  rw [lp.inner_eq_tsum]
  have hs : Summable (fun p : I × J => inner ℂ (v p.1 p.2) (w p.1 p.2)) :=
    lp.summable_inner (timeStack v) (timeStack w)
  change (∑' p : I × J, inner ℂ (v p.1 p.2) (w p.1 p.2)) = _
  rw [hs.tsum_prod,tsum_fintype]
  rfl

end ELV.Query

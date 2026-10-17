import Paper29.ProductLawTools

noncomputable section
open scoped BigOperators Classical
namespace Paper29.Sampling

/-- A fresh coordinate has its original channel law after conditioning on any
weight/event invariant under changes to that coordinate. This algebraic identity
is uniform in the hidden source and therefore applies to adaptive posteriors. -/
theorem product_fresh_coordinate {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → Bool → ℝ) (j : I) (hnorm : ∑ b, p j b = 1)
    (W : (I → Bool) → ℝ) (hinvariant : ∀ y b, W (Function.update y j b) = W y)
    (g : Bool → ℝ) :
    (∑ y : I → Bool, (∏ i,p i (y i))*W y*g (y j)) =
      (∑ b,p j b*g b)*(∑ y : I → Bool, (∏ i,p i (y i))*W y) := by
  let e := Equiv.funSplitAt j Bool
  let rest : ℝ := ∑ z : {i : I // i≠j} → Bool,
    (∏ i : {i : I // i≠j},p i (z i))*W (e.symm (false,z))
  have hW (b : Bool) (z : {i : I // i≠j} → Bool) : W (e.symm (b,z)) = W (e.symm (false,z)) := by
    have he : e.symm (b,z) = Function.update (e.symm (false,z)) j b := by
      funext i
      by_cases hi : i=j
      · subst i
        simp [e]
      · simp [e,Equiv.piSplitAt,hi]
    rw [he,hinvariant]
  have hsplit (g : Bool → ℝ) :
      (∑ y : I → Bool, (∏ i,p i (y i))*W y*g (y j)) = (∑ b,p j b*g b)*rest := by
    rw [← e.symm.sum_comp (fun y : I → Bool => (∏ i,p i (y i))*W y*g (y j)),Fintype.sum_prod_type]
    have he (b : Bool) (z : {i : I // i≠j} → Bool) :
        (∏ i,p i (e.symm (b,z) i))*W (e.symm (b,z))*g (e.symm (b,z) j) =
          (p j b*g b)*((∏ i : {i : I // i≠j},p i (z i))*W (e.symm (false,z))) := by
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ j,hW]
      have hj : e.symm (b,z) j = b := by simp [e]
      have hn (i : {i : I // i≠j}) : e.symm (b,z) i = z i := by
        simp [e,Equiv.piSplitAt,i.property]
      simp only [hj,hn]
      ring
    simp_rw [he]
    simp only [← Finset.mul_sum,rest,Finset.sum_mul]
  have hbase : (∑ y : I → Bool, (∏ i,p i (y i))*W y) = rest := by
    simpa only [mul_one,hnorm,one_mul] using hsplit (fun _ => 1)
  rw [hbase]
  exact hsplit g

end Paper29.Sampling

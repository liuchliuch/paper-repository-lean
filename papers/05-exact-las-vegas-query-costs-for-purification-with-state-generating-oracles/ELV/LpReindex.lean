import ELV.QueryCircuit

/-! Reindexing square summable vectors, including the bilateral counter shift. -/
noncomputable section
open scoped ENNReal
namespace ELV.Query
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma reindex_mem (e : I ≃ J) (v : lp (fun _ : I => E) 2) :
    Memℓp (fun j => v (e.symm j)) 2 := by
  apply memℓp_gen
  exact e.symm.summable_iff.mpr ((lp.memℓp v).summable (by norm_num))

/-- Relabel orthogonal coordinates by a bijection, as an actual unitary. -/
def lpReindex (e : I ≃ J) : lp (fun _ : I => E) 2 ≃ₗᵢ[ℂ] lp (fun _ : J => E) 2 where
  toLinearEquiv :=
    { toFun := fun v => ⟨fun j => v (e.symm j), reindex_mem e v⟩
      invFun := fun v => ⟨fun i => v (e i), reindex_mem e.symm v⟩
      left_inv := by intro v; ext i; simp
      right_inv := by intro v; ext j; simp
      map_add' := by intro v w; rfl
      map_smul' := by intro c v; rfl }
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [@norm_sq_eq_re_inner ℂ,@norm_sq_eq_re_inner ℂ]
    congr 1
    change (∑' j, inner ℂ (v (e.symm j)) (v (e.symm j))) = ∑' i, inner ℂ (v i) (v i)
    exact e.symm.tsum_eq (fun i : I => inner ℂ (v i) (v i))

@[simp] theorem lpReindex_apply (e : I ≃ J) (v : lp (fun _ : I => E) 2) (j : J) :
    lpReindex e v j = v (e.symm j) := rfl

def successorEquiv : ℤ ≃ ℤ where
  toFun z := z+1
  invFun z := z-1
  left_inv z := by simp
  right_inv z := by simp

/-- The bilateral shift `V e_n = e_(n+1)`. -/
def bilateralShift : lp (fun _ : ℤ => E) 2 ≃ₗᵢ[ℂ] lp (fun _ : ℤ => E) 2 := lpReindex successorEquiv

@[simp] theorem bilateralShift_apply (v : lp (fun _ : ℤ => E) 2) (j : ℤ) :
    bilateralShift v j = v (j-1) := rfl

end ELV.Query

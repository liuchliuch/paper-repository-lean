import ELV.LpReindex
import ELV.HilbertSum
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! Unitary coordinate decompositions for the fixed line-walk construction. -/
noncomputable section
open scoped ENNReal
namespace ELV.Query
open ELV.Stabilize
variable {I J E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

lemma lp_summable_sq (v : lp (fun _ : I => E) 2) : Summable (fun i => ‖v i‖ ^ 2) := by
  simpa using (lp.memℓp v).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

lemma lp_norm_sq (v : lp (fun _ : I => E) 2) : ‖v‖ ^ 2 = ∑' i, ‖v i‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) v

lemma congr_mem (e : E ≃ₗᵢ[ℂ] F) (v : lp (fun _ : I => E) 2) :
    Memℓp (fun i => e (v i)) 2 := by
  apply memℓp_gen
  simpa using lp_summable_sq v

/-- Apply the same known unitary coordinate change in every counter position. -/
def lpCongr (e : E ≃ₗᵢ[ℂ] F) : lp (fun _ : I => E) 2 ≃ₗᵢ[ℂ] lp (fun _ : I => F) 2 where
  toLinearEquiv :=
    { toFun := fun v => ⟨fun i => e (v i), congr_mem e v⟩
      invFun := fun v => ⟨fun i => e.symm (v i), congr_mem e.symm v⟩
      left_inv := by intro v; ext i; simp
      right_inv := by intro v; ext i; simp
      map_add' := by intro v w; ext i; exact map_add e _ _
      map_smul' := by intro c v; ext i; exact map_smul e c _ }
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [lp_norm_sq,lp_norm_sq]
    apply tsum_congr
    intro i
    exact congrArg (fun x : ℝ => x^2) (e.norm_map (v i))

@[simp] lemma lpCongr_apply (e : E ≃ₗᵢ[ℂ] F) (v : lp (fun _ : I => E) 2) (i : I) :
    lpCongr e v i = e (v i) := rfl

lemma fst_mem (v : lp (fun _ : I => HilbertPair E F) 2) : Memℓp (fun i => (v i).fst) 2 := by
  apply memℓp_gen
  have hs := lp_summable_sq v
  have hb : ∀ i, ‖(v i).fst‖ ^ 2 ≤ ‖v i‖ ^ 2 := by
    intro i
    rw [WithLp.prod_norm_sq_eq_of_L2]
    nlinarith [sq_nonneg ‖(v i).snd‖]
  simpa using Summable.of_nonneg_of_le (fun i => sq_nonneg ‖(v i).fst‖) hb hs

lemma snd_mem (v : lp (fun _ : I => HilbertPair E F) 2) : Memℓp (fun i => (v i).snd) 2 := by
  apply memℓp_gen
  have hs := lp_summable_sq v
  have hb : ∀ i, ‖(v i).snd‖ ^ 2 ≤ ‖v i‖ ^ 2 := by
    intro i
    rw [WithLp.prod_norm_sq_eq_of_L2]
    nlinarith [sq_nonneg ‖(v i).fst‖]
  simpa using Summable.of_nonneg_of_le (fun i => sq_nonneg ‖(v i).snd‖) hb hs

lemma pair_mem (v : lp (fun _ : I => E) 2) (w : lp (fun _ : I => F) 2) :
    Memℓp (fun i => WithLp.toLp 2 (v i,w i)) 2 := by
  apply memℓp_gen
  simpa [WithLp.prod_norm_sq_eq_of_L2,Real.rpow_two] using
    (lp_summable_sq v).add (lp_summable_sq w)

/-- Orthogonal direct sums commute with square summable counter coordinates. -/
def lpPair : lp (fun _ : I => HilbertPair E F) 2 ≃ₗᵢ[ℂ]
    HilbertPair (lp (fun _ : I => E) 2) (lp (fun _ : I => F) 2) where
  toLinearEquiv :=
    { toFun := fun v => WithLp.toLp 2 (⟨fun i => (v i).fst,fst_mem v⟩,
                                      ⟨fun i => (v i).snd,snd_mem v⟩)
      invFun := fun z => ⟨fun i => WithLp.toLp 2 (z.fst i,z.snd i),pair_mem z.fst z.snd⟩
      left_inv := by intro v; rfl
      right_inv := by intro z; rfl
      map_add' := by intro v w; rfl
      map_smul' := by intro c v; rfl }
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2,lp_norm_sq,lp_norm_sq,lp_norm_sq]
    change (∑' i, ‖(v i).fst‖ ^ 2) + (∑' i, ‖(v i).snd‖ ^ 2) = ∑' i, ‖v i‖ ^ 2
    have hf : Summable (fun i => ‖(v i).fst‖ ^ 2) := by
      simpa using (fst_mem v).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    have hg : Summable (fun i => ‖(v i).snd‖ ^ 2) := by
      simpa using (snd_mem v).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    rw [← hf.tsum_add hg]
    apply tsum_congr
    intro i
    simpa using (WithLp.prod_norm_sq_eq_of_L2 (v i)).symm

lemma sum_inl_mem (v : lp (fun _ : I ⊕ J => E) 2) : Memℓp (fun i => v (Sum.inl i)) 2 := by
  apply memℓp_gen
  simpa using (lp_summable_sq v).comp_injective Sum.inl_injective

lemma sum_inr_mem (v : lp (fun _ : I ⊕ J => E) 2) : Memℓp (fun j => v (Sum.inr j)) 2 := by
  apply memℓp_gen
  simpa using (lp_summable_sq v).comp_injective Sum.inr_injective

lemma sum_elim_mem (v : lp (fun _ : I => E) 2) (w : lp (fun _ : J => E) 2) :
    Memℓp (Sum.elim v w) 2 := by
  apply memℓp_gen
  apply Summable.sum
  · simpa using lp_summable_sq v
  · simpa using lp_summable_sq w

/-- Split the two counter channels into an orthogonal Hilbert pair. -/
def lpSum : lp (fun _ : I ⊕ J => E) 2 ≃ₗᵢ[ℂ]
    HilbertPair (lp (fun _ : I => E) 2) (lp (fun _ : J => E) 2) where
  toLinearEquiv :=
    { toFun := fun v => WithLp.toLp 2 (⟨fun i => v (Sum.inl i),sum_inl_mem v⟩,
                                      ⟨fun j => v (Sum.inr j),sum_inr_mem v⟩)
      invFun := fun z => ⟨Sum.elim z.fst z.snd,sum_elim_mem z.fst z.snd⟩
      left_inv := by intro v; apply Subtype.ext; funext i; cases i <;> rfl
      right_inv := by intro z; rfl
      map_add' := by intro v w; apply (WithLp.equiv 2 _).injective; rfl
      map_smul' := by intro c v; apply (WithLp.equiv 2 _).injective; rfl }
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2,lp_norm_sq,lp_norm_sq,lp_norm_sq]
    change (∑' i, ‖v (Sum.inl i)‖ ^ 2) + (∑' j, ‖v (Sum.inr j)‖ ^ 2) = ∑' k, ‖v k‖ ^ 2
    exact ((lp_summable_sq v).comp_injective Sum.inl_injective).tsum_sum
      ((lp_summable_sq v).comp_injective Sum.inr_injective) |>.symm

end ELV.Query

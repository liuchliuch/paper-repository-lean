import Paper13.GraphDynamics
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators

def zeroState (n : ℕ) : QubitBasis n := fun _ => 0

lemma flipBit_zero_injective {n : ℕ} : Function.Injective (fun v : Fin n => flipBit v (zeroState n)) := by
  intro v w h
  by_contra hvw
  have he := congrFun h v
  simp [flipBit,zeroState,Function.update,hvw] at he

lemma mixer_nonzero (n : ℕ) (hn : 0 < n) : HXFull n ≠ 0 := by
  let v : Fin n := ⟨0,hn⟩
  have he : HXFull n (flipBit v (zeroState n)) (zeroState n)=1 := by
    simp only [HXFull,Matrix.sum_apply,Xv_basisOp,basisOp]
    have hf (w : Fin n) : flipBit v (zeroState n)=flipBit w (zeroState n) ↔ v=w :=
      flipBit_zero_injective.eq_iff
    simp only [hf]
    simp
  intro hz
  rw [hz] at he
  norm_num at he

/-- The actual shared mixer guarantees a positive-dimensional standard algebra. -/
theorem graphStd_finrank_pos {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n) :
    0 < Module.finrank ℝ (graphStd G) := by
  have hm : iMul (HXFull n) ∈ graphStd G := subset_lieClosure (by simp [stdGens])
  have hne : iMul (HXFull n) ≠ 0 := by
    change Complex.I • HXFull n ≠ 0
    exact smul_ne_zero Complex.I_ne_zero (mixer_nonzero n hn)
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨iMul (HXFull n),hm⟩,?_⟩
  intro h
  exact hne (congrArg Subtype.val h)
end Paper13

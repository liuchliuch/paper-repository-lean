import Paper29.DecodingLoss

noncomputable section
open scoped BigOperators Classical
namespace Paper29.HardDistribution

/-- The actual row in the original pool corresponding to a block coordinate. -/
def blockRow {n r N : ℕ} (hblocks : r*N ≤ n) (a : Fin r × Fin N) : Fin n :=
  ⟨a.1.val*N+a.2.val, by
    have h := a.2.isLt
    have hj : a.1.val+1 ≤ r := a.1.isLt
    calc
      a.1.val*N+a.2.val < a.1.val*N+N := Nat.add_lt_add_left h _
      _ = (a.1.val+1)*N := by ring
      _ ≤ r*N := Nat.mul_le_mul_right N hj
      _ ≤ n := hblocks⟩

theorem blockRow_div {n r N : ℕ} (hN : 0 < N) (hblocks : r*N ≤ n) (a : Fin r × Fin N) :
    (blockRow hblocks a).val/N = a.1.val := by
  change (a.1.val*N+a.2.val)/N = _
  rw [Nat.mul_comm a.1.val N,Nat.mul_add_div hN]
  simp [Nat.div_eq_of_lt a.2.isLt]

theorem blockRow_mod {n r N : ℕ} (hblocks : r*N ≤ n) (a : Fin r × Fin N) :
    (blockRow hblocks a).val%N = a.2.val := by
  change (a.1.val*N+a.2.val)%N = _
  rw [Nat.mul_comm a.1.val N,Nat.mul_add_mod,Nat.mod_eq_of_lt a.2.isLt]

theorem blockRow_injective {n r N : ℕ} (hN : 0 < N) (hblocks : r*N ≤ n) :
    Function.Injective (blockRow hblocks) := by
  intro a b hab
  apply Prod.ext
  · apply Fin.ext
    have hh := congrArg (fun i : Fin n => i.val/N) hab
    simpa only [blockRow_div hN] using hh
  · apply Fin.ext
    have hh := congrArg (fun i : Fin n => i.val%N) hab
    simpa only [blockRow_mod] using hh

theorem mem_blockRow_image {n r N : ℕ} (hN : 0 < N) (hblocks : r*N ≤ n) (i : Fin n) :
    i ∈ Finset.univ.image (blockRow hblocks) ↔ i.val < r*N := by
  constructor
  · rintro hi
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hi
    change a.1.val*N+a.2.val < r*N
    have hj : a.1.val+1 ≤ r := a.1.isLt
    nlinarith [Nat.mul_le_mul_right N hj,a.2.isLt]
  · intro hi
    let a : Fin r × Fin N := (⟨i.val/N,(Nat.div_lt_iff_lt_mul hN).2 hi⟩,
      ⟨i.val%N,Nat.mod_lt _ hN⟩)
    refine Finset.mem_image.mpr ⟨a,Finset.mem_univ _,?_⟩
    apply Fin.ext
    change (i.val/N)*N+i.val%N = i.val
    simpa only [Nat.mul_comm] using Nat.div_add_mod i.val N

theorem long_prediction {n d r N : ℕ} (hN : 0 < N) (hrd : r ≤ d)
    (x : Fin d → ℝ) (i : Fin n) (hi : i.val < r*N) :
    ((longDesign n d r N).mulVec x) i =
      4*x ⟨i.val/N,lt_of_lt_of_le ((Nat.div_lt_iff_lt_mul hN).2 hi) hrd⟩ := by
  let j : Fin d := ⟨i.val/N,lt_of_lt_of_le ((Nat.div_lt_iff_lt_mul hN).2 hi) hrd⟩
  have he (k : Fin d) : (k.val<r ∧ i.val/N=k.val ∧ i.val<r*N) ↔ k=j := by
    constructor
    · intro hk
      exact Fin.ext hk.2.1.symm
    · rintro rfl
      exact ⟨(Nat.div_lt_iff_lt_mul hN).2 hi,rfl,hi⟩
  simp only [Matrix.mulVec,dotProduct,longDesign_apply,he,ite_mul,zero_mul]
  simp [j]

theorem long_padded_prediction {n d r N : ℕ} (x : Fin d → ℝ) (i : Fin n) (hi : ¬i.val<r*N) :
    ((longDesign n d r N).mulVec x) i = 0 := by
  simp [Matrix.mulVec,dotProduct,longDesign_apply,hi]

/-- The actual ambient matrix objective is exactly the sum of its block losses;
the fewer-than-r padding rows contribute zero. -/
theorem long_objective_blocks {n d r N : ℕ} (hN : 0 < N) (hrd : r ≤ d) (hblocks : r*N ≤ n)
    (y : Bits r N) (x : Fin d → ℝ) :
    objective (longDesign n d r N) (longResponse y) x =
      productLoss y (fun j => x (Fin.castLE hrd j)) := by
  let E := Finset.univ.image (blockRow hblocks)
  have hsum : (∑ i ∈ E, huber (((longDesign n d r N).mulVec x) i-longResponse y i)) =
      objective (longDesign n d r N) (longResponse y) x := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hpad : ¬i.val<r*N := by simpa only [E,mem_blockRow_image hN] using hi
    rw [long_padded_prediction x i hpad]
    simp [longResponse,hpad]
  rw [← hsum,Finset.sum_image (blockRow_injective hN hblocks).injOn,Fintype.sum_prod_type]
  unfold productLoss blockLoss
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have hi : (blockRow hblocks (j,k)).val<r*N :=
    (mem_blockRow_image hN hblocks _).1 (Finset.mem_image.mpr ⟨(j,k),Finset.mem_univ _,rfl⟩)
  rw [long_prediction hN hrd x _ hi]
  simp only [longResponse,dif_pos hi,dif_pos hN,blockRow_div hN,blockRow_mod]
  congr 1
  change 4*x (Fin.castLE hrd j)-4*bit (y (j,k)) = 4*(x (Fin.castLE hrd j)-bit (y (j,k)))
  ring

end Paper29.HardDistribution

import Paper29.BlockDesign
import Paper29.QueryModel
import Paper29.Localization

noncomputable section
open scoped BigOperators Classical
namespace Paper29.HardDistribution

/-- Zero padding lifts an arbitrary block-coordinate comparator into the actual
ambient parameter space. -/
def ambientLift {r d : ℕ} (x : Fin r → ℝ) : Fin d → ℝ :=
  fun j => if hj : j.val<r then x ⟨j.val,hj⟩ else 0

theorem ambientLift_restrict {r d : ℕ} (hrd : r ≤ d) (x : Fin r → ℝ) (j : Fin r) :
    ambientLift (d:=d) x (Fin.castLE hrd j) = x j := by
  simp [ambientLift,j.isLt]

/-- A successful output on the actual long hard design satisfies the exact
block-objective comparator guarantee used in the decoding count. -/
theorem long_success_block_comparator {n d r N : ℕ} (hN : 0 < N) (hrd : r ≤ d) (hblocks : r*N ≤ n)
    (y : Bits r N) (xhat : Fin d → ℝ) (ε : ℝ)
    (hsuccess : ∀ x, Real.sqrt (objective (longDesign n d r N) (longResponse y) xhat) ≤
      (1+ε)*Real.sqrt (objective (longDesign n d r N) (longResponse y) x)) :
    Real.sqrt (productLoss y (fun j => xhat (Fin.castLE hrd j))) ≤
      (1+ε)*Real.sqrt (productLoss y (productOpt y)) := by
  have hh := hsuccess (ambientLift (d:=d) (productOpt y))
  simp only [long_objective_blocks hN hrd hblocks,ambientLift_restrict hrd] at hh
  exact hh

/-- Zero optimum on the short hard matrix forces every decoded hidden sign. -/
theorem short_prediction {n d r : ℕ} (hrd : r ≤ d) (x : Fin d → ℝ)
    (j : Fin r) (hj : j.val<n) :
    ((shortDesign n d r).mulVec x) ⟨j.val,hj⟩ = x (Fin.castLE hrd j) := by
  have he (k : Fin d) : (k.val<r ∧ j.val=k.val) ↔ k=Fin.castLE hrd j := by
    constructor
    · intro hk
      exact Fin.ext hk.2.symm
    · rintro rfl
      exact ⟨j.isLt,rfl⟩
  simp only [Matrix.mulVec,dotProduct,shortDesign_apply,he,ite_mul,one_mul,zero_mul]
  simp

theorem short_padded_prediction {n d r : ℕ} (x : Fin d → ℝ) (i : Fin n) (hi : ¬i.val<r) :
    ((shortDesign n d r).mulVec x) i = 0 := by
  have he (j : Fin d) : ¬(j.val<r ∧ i.val=j.val) := by intro h; exact hi (h.2 ▸ h.1)
  simp [Matrix.mulVec,dotProduct,shortDesign_apply,he]

theorem short_zero_optimum {n d r : ℕ} (hrn : r ≤ n) (hrd : r ≤ d) (s : Signs r) :
    objective (shortDesign n d r) (shortResponse s) (ambientLift (d:=d) (fun j => sign (s j))) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i.val<r
  · let j : Fin r := ⟨i.val,hi⟩
    have hp := short_prediction hrd (ambientLift (d:=d) (fun j => sign (s j))) j i.isLt
    rw [ambientLift_restrict hrd] at hp
    change huber (((shortDesign n d r).mulVec _) i-shortResponse s i) = 0
    have hi' : (⟨j.val,i.isLt⟩ : Fin n) = i := by rfl
    rw [hi'] at hp
    rw [hp]
    simp [shortResponse,hi,j]
  · rw [short_padded_prediction _ i hi]
    simp [shortResponse,hi]

theorem short_success_decodes {n d r : ℕ} (hrn : r ≤ n) (hrd : r ≤ d) (s : Signs r)
    (xhat : Fin d → ℝ) (ε : ℝ)
    (hsuccess : ∀ x, Real.sqrt (objective (shortDesign n d r) (shortResponse s) xhat) ≤
      (1+ε)*Real.sqrt (objective (shortDesign n d r) (shortResponse s) x)) :
    (fun j => decode (xhat (Fin.castLE hrd j))) = s := by
  have hh := hsuccess (ambientLift (d:=d) (fun j => sign (s j)))
  rw [short_zero_optimum hrn hrd,Real.sqrt_zero,mul_zero] at hh
  have hzero : objective (shortDesign n d r) (shortResponse s) xhat = 0 :=
    le_antisymm (Real.sqrt_eq_zero'.mp (le_antisymm hh (Real.sqrt_nonneg _)))
      (Finset.sum_nonneg (fun i _ => huber_nonneg _))
  have hz := Localization.residual_zero_of_objective_zero _ _ _ hzero
  funext j
  have hjn : j.val<n := lt_of_lt_of_le j.isLt hrn
  have he := hz ⟨j.val,hjn⟩
  rw [short_prediction hrd] at he
  have he' : xhat (Fin.castLE hrd j) = sign (s j) := by
    simpa [shortResponse,j.isLt] using sub_eq_zero.mp he
  rw [he']
  cases hs : s j <;> norm_num [decode,sign,hs]

end Paper29.HardDistribution

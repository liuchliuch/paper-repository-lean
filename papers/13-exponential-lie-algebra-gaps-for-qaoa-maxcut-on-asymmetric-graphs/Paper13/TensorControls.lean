import Paper13.TensorBlocks
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators

/-- A local matrix acting on one copy of the product-basis Hilbert space. -/
def liftSite {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (v : κ) (A : Matrix ι ι ℂ) : Matrix (κ → ι) (κ → ι) ℂ :=
  tensorMatrix (fun w => if w = v then A else 1)

lemma liftSite_entry {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (v : κ) (A : Matrix ι ι ℂ) (x y : κ → ι) :
    liftSite v A x y = if (∀ w, w ≠ v → x w = y w) then A (x v) (y v) else 0 := by
  classical
  simp only [liftSite, tensorMatrix]
  by_cases h : ∀ w, w ≠ v → x w = y w
  · rw [if_pos h, Finset.prod_eq_single v]
    · simp
    · intro w hw hwv
      simp [hwv, Matrix.one_apply, h w hwv]
    · simp
  · rw [if_neg h]
    push_neg at h
    obtain ⟨w,hwv,hxy⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ w)
    simp [hwv,Matrix.one_apply,hxy]

lemma liftSite_one {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (v : κ) : liftSite v (1 : Matrix ι ι ℂ) = 1 := by
  simp only [liftSite, ite_self, tensorMatrix_one]

lemma liftSite_add {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (v : κ) (A B : Matrix ι ι ℂ) : liftSite v (A+B) = liftSite v A + liftSite v B := by
  ext x y
  simp only [liftSite_entry, Matrix.add_apply]
  split_ifs <;> simp

lemma liftSite_smul {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (v : κ) (z : ℂ) (A : Matrix ι ι ℂ) : liftSite v (z • A) = z • liftSite v A := by
  ext x y
  simp only [liftSite_entry, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

lemma liftSite_zero {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (v : κ) : liftSite v (0 : Matrix ι ι ℂ) = 0 := by
  ext x y
  simp [liftSite_entry]

lemma liftSite_mul {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (v : κ) (A B : Matrix ι ι ℂ) : liftSite v (A*B) = liftSite v A * liftSite v B := by
  rw [liftSite,liftSite,liftSite,tensorMatrix_mul]
  congr 1
  funext w
  split_ifs <;> simp

/-- The actual local embedding is complex-linear. -/
def liftSiteLinear {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (v : κ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix (κ → ι) (κ → ι) ℂ where
  toFun := liftSite v
  map_add' := liftSite_add v
  map_smul' := liftSite_smul v

lemma liftSite_sum {κ ι β : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (v : κ) (s : Finset β) (A : β → Matrix ι ι ℂ) :
    liftSite v (∑ b ∈ s, A b) = ∑ b ∈ s, liftSite v (A b) :=
  map_sum (liftSiteLinear v) A s

/-- A tensor block commutes with a local control exactly when its local factor does. -/
lemma tensorMatrix_commute_liftSite {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (A : κ → Matrix ι ι ℂ) (v : κ) (B : Matrix ι ι ℂ) (h : A v * B = B * A v) :
    tensorMatrix A * liftSite v B = liftSite v B * tensorMatrix A := by
  simp only [liftSite,tensorMatrix_mul]
  congr 1
  funext w
  by_cases hw : w = v
  · subst w; simp only [if_pos rfl]; exact h
  · simp [hw]

lemma liftSite_conjTranspose {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (v : κ) (A : Matrix ι ι ℂ) : (liftSite v A)ᴴ = liftSite v Aᴴ := by
  rw [liftSite,tensorMatrix_conjTranspose]
  congr 1
  funext w
  split_ifs <;> simp
end Paper13

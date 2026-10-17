import Paper12.Registers
import Paper12.TwoReflection
import Paper12.Selector

noncomputable section
namespace Paper12
open Matrix Classical
variable {J K : Type*} [Fintype J] [Fintype K]

def vecInner (ψ χ : Vec J) : ℂ := ∑ b, star (ψ b) * χ b

def column (ψ : Vec J) : Matrix (Basis J) Unit ℂ := fun b _ => ψ b

theorem column_apply (A : Op J) (ψ : Vec J) : A * column ψ = column (applyOp A ψ) := rfl

theorem column_isometry (ψ : Vec J) (h : vecInner ψ ψ = 1) : IsIsometry (column ψ) := by
  ext i j
  change vecInner ψ ψ = _
  rw [h]
  simp

theorem vecInner_basis (b c : Basis J) : vecInner (eBasis b) (eBasis c) = if b = c then 1 else 0 := by
  unfold vecInner eBasis
  rw [Finset.sum_eq_single b]
  · simp [eq_comm]
  · intro a _ ha; simp [ha]
  · intro hb; exact (hb (Finset.mem_univ _)).elim

@[simp] theorem vecInner_zero : vecInner (zeroKet J) (zeroKet J) = 1 := by
  exact (vecInner_basis _ _).trans (if_pos rfl)

theorem vecInner_registerVec (ψ φ : Vec J) (χ η : Vec K) :
    vecInner (registerVec ψ χ) (registerVec φ η) = vecInner ψ φ * vecInner χ η := by
  unfold vecInner registerVec
  rw [sum_joint, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  rw [show star (ψ a * χ b) = star (ψ a) * star (χ b) from map_mul (starRingEnd ℂ) _ _]
  ring

def predicateProjector (p : Basis J → Prop) : Op J :=
  Matrix.diagonal (fun b => if p b then 1 else 0)

theorem predicateProjector_orthogonal (p : Basis J → Prop) :
    IsOrthoProj (predicateProjector p) := by
  constructor
  · rw [predicateProjector, Matrix.diagonal_mul_diagonal]
    congr 1
    funext b
    split_ifs <;> simp
  · ext i j
    simp only [predicateProjector, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst j; simp
    · simp [hij, Ne.symm hij]

theorem predicateProjector_apply (p : Basis J → Prop) (ψ : Vec J) :
    applyOp (predicateProjector p) ψ = fun b => if p b then ψ b else 0 := by
  funext b
  simp only [applyOp, predicateProjector, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single b]
  · by_cases hp : p b <;> simp [hp]
  · intro a _ ha; simp [Ne.symm ha]
  · intro hb; exact (hb (Finset.mem_univ _)).elim

theorem zeroKet_projector :
    column (zeroKet J) * (column (zeroKet J))ᴴ =
      predicateProjector (fun b : Basis J => b = fun _ => 0) := by
  ext i j
  simp only [column, zeroKet, eBasis, Matrix.mul_apply, Matrix.conjTranspose_apply,
    predicateProjector, Matrix.diagonal_apply]
  simp only [Fintype.sum_unique]
  by_cases hi : i = fun _ : J => (0 : Fin 2)
  · subst i; by_cases hj : j = fun _ : J => (0 : Fin 2) <;> simp [hj, eq_comm]
  · by_cases hij : i = j
    · subst j; simp [hi]
    · simp [hi, hij]

theorem oneHot_injective : Function.Injective (oneHot (J := J)) := by
  intro q r h
  by_contra hne
  have hh := congrFun h q
  simp [oneHot, hne] at hh

def weightedOneHot (d : J → ℝ) : Vec J :=
  fun b => ∑ q : J, if b = oneHot q then (d q : ℂ) else 0

theorem weightedOneHot_at (d : J → ℝ) (q : J) : weightedOneHot d (oneHot q) = d q := by
  unfold weightedOneHot
  rw [Finset.sum_eq_single q]
  · simp
  · intro r _ hr
    exact if_neg (fun h => hr (oneHot_injective h).symm)
  · intro hq; exact (hq (Finset.mem_univ _)).elim

theorem weightedOneHot_inner (d : J → ℝ) :
    vecInner (weightedOneHot d) (weightedOneHot d) = ∑ q : J, (d q : ℂ) ^ 2 := by
  have hstar : ∀ b : Basis J, star (weightedOneHot d b) = weightedOneHot d b := by
    intro b
    change starRingEnd ℂ (∑ q : J, if b = oneHot q then (d q : ℂ) else 0) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> simp
  have hdecomp : ∀ b : Basis J,
      star (weightedOneHot d b) * weightedOneHot d b =
        ∑ q : J, (if b = oneHot q then (d q : ℂ) else 0) * weightedOneHot d b := by
    intro b
    rw [hstar]
    exact Finset.sum_mul _ _ _
  unfold vecInner
  simp_rw [hdecomp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_eq_single (oneHot q)]
  · simp [weightedOneHot_at, sq]
  · intro b _ hb
    simp [hb]
  · intro hq; exact (hq (Finset.mem_univ _)).elim
end Paper12

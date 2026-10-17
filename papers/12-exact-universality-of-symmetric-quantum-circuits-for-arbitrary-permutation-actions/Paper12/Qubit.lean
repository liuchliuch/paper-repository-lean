import Mathlib

/-!
# Qubit registers, Pauli basis, and the permutation representation

Operators on a finite qubit register `X` are matrices on the computational
basis `X → Fin 2`.  Tensor-factor products of 2×2 Pauli matrices are the
entries of a product formula on basis indices, matching the Kronecker
product.  A permutation `γ : X ≃ X` acts by relabelling basis states, and
by conjugation on Pauli words.
-/

noncomputable section

namespace Paper12

open Matrix Complex

/-- Computational-basis index of a qubit register `X`. -/
abbrev Basis (X : Type*) := X → Fin 2

/-- Vectors in the register Hilbert space `(ℂ²)^{⊗ X}`. -/
abbrev Vec (X : Type*) := Basis X → ℂ

/-- Linear operators on the register Hilbert space. -/
abbrev Op (X : Type*) := Matrix (Basis X) (Basis X) ℂ

-- Instances so that `Basis X` has decidable equality and (when `X` is finite)
-- a `Fintype`, making `Op X` a unital algebra of matrices.
instance instDecidableEqBasis (X : Type*) : DecidableEq (Basis X) := Classical.decEq _

instance instFintypeBasis (X : Type*) [Fintype X] : Fintype (Basis X) := by classical exact Pi.instFintype

/-- Phase-free Hermitian Pauli symbols. -/
inductive PSym
  | I | X | Y | Z
  deriving DecidableEq, Repr, Inhabited

instance instFintypePSym : Fintype PSym where
  elems := {.I, .X, .Y, .Z}
  complete := by intro s; cases s <;> simp

/-- The 2×2 matrix of a Pauli symbol. -/
def pmat : PSym → Matrix (Fin 2) (Fin 2) ℂ
  | .I => 1
  | .X => ![![0, 1], ![1, 0]]
  | .Y => ![![0, -I], ![I, 0]]
  | .Z => ![![1, 0], ![0, -1]]

@[simp] theorem pmat_I : pmat .I = (1 : Matrix (Fin 2) (Fin 2) ℂ) := rfl

theorem pmat_hermitian (s : PSym) : (pmat s)ᴴ = pmat s := by
  cases s with
  | I => simp [pmat]
  | X => ext i j; fin_cases i <;> fin_cases j <;> simp [pmat, conjTranspose]
  | Y => ext i j; fin_cases i <;> fin_cases j <;> simp [pmat, conjTranspose, Complex.I_mul_I]
  | Z => ext i j; fin_cases i <;> fin_cases j <;> simp [pmat, conjTranspose]

theorem pmat_unitary (s : PSym) : (pmat s)ᴴ * pmat s = 1 := by
  rw [pmat_hermitian]
  cases s with
  | I => simp [pmat]
  | X => ext i j; fin_cases i <;> fin_cases j <;>
      simp [pmat, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two]
  | Y => ext i j; fin_cases i <;> fin_cases j <;>
      simp [pmat, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two, Complex.I_mul_I]
  | Z => ext i j; fin_cases i <;> fin_cases j <;>
      simp [pmat, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two]

/-- A Pauli word is a choice of one Pauli symbol on each wire. -/
abbrev PWord (X : Type*) := X → PSym

/-- Tensor product of the local Pauli matrices, as an operator on `X`. -/
def pop (X : Type*) [Fintype X] (w : PWord X) : Op X :=
  Matrix.of fun b b' => ∏ x, (pmat (w x) (b x) (b' x))

theorem pop_apply (X : Type*) [Fintype X] (w : PWord X) (b b' : Basis X) :
    pop X w b b' = ∏ x, (pmat (w x) (b x) (b' x)) := rfl

/-- Permutation of basis states induced by `γ : X ≃ X`.
Matches `R_X(γ)|b⟩ = |b ∘ γ⁻¹⟩`. -/
def permBasis (γ : X ≃ X) (b : Basis X) : Basis X := fun x => b (γ.symm x)

@[simp] theorem permBasis_apply (γ : X ≃ X) (b : Basis X) (x : X) :
    permBasis γ b x = b (γ.symm x) := rfl

theorem permBasis_injective (γ : X ≃ X) : Function.Injective (permBasis γ) := by
  intro b b' h
  funext x
  have := congrFun h (γ x)
  simpa [permBasis] using this

theorem permBasis_comp (γ δ : X ≃ X) (b : Basis X) :
    permBasis γ (permBasis δ b) = permBasis (γ * δ) b := by
  funext x
  show b (δ.symm (γ.symm x)) = b ((γ * δ).symm x)
  rfl

theorem permBasis_iff (γ : X ≃ X) (i j : Basis X) :
    permBasis γ i = j ↔ permBasis γ.symm j = i := by
  constructor
  · intro h
    funext x
    have := congrFun h (γ x)
    have h2 := this.symm
    simpa [permBasis] using h2
  · intro h
    funext x
    have := congrFun h (γ.symm x)
    have h2 := this.symm
    simpa [permBasis] using h2

/-- Tensor-factor permutation representation `R_X(γ)`. -/
def R (γ : X ≃ X) : Op X :=
  Matrix.of fun i j => if permBasis γ j = i then (1 : ℂ) else 0

theorem R_apply (γ : X ≃ X) (i j : Basis X) :
    R γ i j = if permBasis γ j = i then (1 : ℂ) else 0 := rfl

section MatrixOps

variable [Fintype X]

theorem R_adj (γ : X ≃ X) : (R γ)ᴴ = R γ.symm := by
  ext i j
  simp only [conjTranspose_apply, R_apply, Pi.star_apply, starRingEnd_apply]
  by_cases h : permBasis γ i = j
  · rw [if_pos h, if_pos ((permBasis_iff γ i j).mp h), star_one]
  · rw [if_neg h]
    by_cases h2 : permBasis γ.symm j = i
    · exfalso
      apply h
      exact (permBasis_iff γ i j).mpr h2
    · rw [if_neg h2, star_zero]

theorem R_adj_apply (γ : X ≃ X) (i j : Basis X) :
    (R γ)ᴴ i j = if permBasis γ i = j then (1 : ℂ) else 0 := by
  rw [R_adj, R_apply]
  by_cases h : permBasis γ i = j
  · rw [if_pos h, if_pos ((permBasis_iff γ i j).mp h)]
  · rw [if_neg h, if_neg]
    exact fun he => h ((permBasis_iff γ i j).mpr he)

/-- `R` is a representation: `R(1) = 1` and `R(γ δ) = R(γ) R(δ)`. -/
theorem R_one : R (Equiv.refl X) = (1 : Op X) := by
  ext i j
  rw [R_apply, Matrix.one_apply]
  have hperm : permBasis (Equiv.refl X) j = j := rfl
  rw [hperm]
  by_cases h : j = i
  · simp [h]
  · have h' : i ≠ j := Ne.symm h
    simp [h, h']

theorem R_mul (γ δ : X ≃ X) : R (γ * δ) = R γ * R δ := by
  ext i j
  simp only [R_apply, Matrix.mul_apply]
  have key : ∑ k : Basis X, (if permBasis γ k = i then (1 : ℂ) else 0) *
      (if permBasis δ j = k then (1 : ℂ) else 0)
      = if permBasis γ (permBasis δ j) = i then 1 else 0 := by
    rw [Finset.sum_eq_single (permBasis δ j)]
    · by_cases h : permBasis γ (permBasis δ j) = i
      · rw [if_pos h, if_pos rfl, mul_one]
      · rw [if_neg h, if_pos rfl, zero_mul]
    · intro b _ hb
      have h2 : (if permBasis δ j = b then (1 : ℂ) else 0) = 0 :=
        if_neg (fun h => hb h.symm)
      rw [h2, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [key, permBasis_comp]

theorem R_unitary (γ : X ≃ X) : (R γ)ᴴ * R γ = (1 : Op X) := by
  rw [R_adj, ← R_mul]
  have heq : γ.symm * γ = Equiv.refl X := by
    ext x
    simp [Equiv.Perm.coe_mul, Equiv.symm_apply_apply]
  rw [heq, R_one]

theorem R_mul_adj (γ : X ≃ X) : R γ * (R γ)ᴴ = (1 : Op X) := by
  rw [R_adj, ← R_mul]
  have heq : γ * γ.symm = Equiv.refl X := by
    ext x
    simp [Equiv.Perm.coe_mul, Equiv.apply_symm_apply]
  rw [heq, R_one]

end MatrixOps

/-- Induced action on Pauli words: `(γ • w)_y = w_{γ⁻¹ y}`. -/
def actWord (γ : X ≃ X) (w : PWord X) : PWord X := fun y => w (γ.symm y)

@[simp] theorem actWord_apply (γ : X ≃ X) (w : PWord X) (y : X) :
    actWord γ w y = w (γ.symm y) := rfl

theorem actWord_mul (γ δ : X ≃ X) (w : PWord X) :
    actWord (γ * δ) w = actWord γ (actWord δ w) := by
  funext y
  show w ((γ * δ).symm y) = w (δ.symm (γ.symm y))
  rfl

/-- Key identity used by the paper: `(γ P)_{γ x} = P_x`. -/
@[simp] theorem actWord_at_image (γ : X ≃ X) (w : PWord X) (x : X) :
    actWord γ w (γ x) = w x := by
  simp [actWord]

/-- Coefficient function on Pauli words. -/
def Coeffs (X : Type*) := PWord X → ℂ

/-- Orbit-equality of a coefficient function. -/
def OrbitsEqual {X : Type*} (γ : X ≃ X) (α : Coeffs X) : Prop :=
  ∀ w, α (actWord γ w) = α w

end Paper12

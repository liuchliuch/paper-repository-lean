import Paper26.ProductCollectiveMeasurement

/-! Ignoring additional fresh copies gives a genuine padded collective POVM,
with exactly the same outcome measure. Positivity, total effect and the Born
law are proved on the actual tensor powers, including zero-copy boundaries. -/
noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder
open MeasureTheory

namespace Paper26.CollectivePadding
open QuantumModel ContinuousPOVM CollectiveModel CoordinateTransport
variable {ι Γ Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Γ] [DecidableEq Γ]
  [MeasurableSpace Ω]

def ignoreFactor (M : DominatedPOVM ι Ω) : DominatedPOVM (ι × Γ) Ω where
  reference := M.reference
  reference_finite := M.reference_finite
  effect y := M.effect y ⊗ₖ (1 : Matrix Γ Γ ℂ)
  entry_measurable x z := (M.entry_measurable x.1 z.1).mul_const _
  positive_ae := M.positive_ae.mono fun y hy => by
    obtain ⟨Q, hQ⟩ := TensorCopies.psd_exists_gram (M.effect y) hy
    have h := Matrix.posSemidef_conjTranspose_mul_self (Q ⊗ₖ (1 : Matrix Γ Γ ℂ))
    simpa only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, hQ, Matrix.one_mul] using h
  entry_integrable x z := (M.entry_integrable x.1 z.1).mul_const _
  total x z := by
    change (∫ y, M.effect y x.1 z.1 * (1 : Matrix Γ Γ ℂ) x.2 z.2 ∂M.reference) = _
    rw [integral_mul_const, M.total]
    exact congrArg (fun A : Matrix (ι × Γ) (ι × Γ) ℂ => A x z)
        (Matrix.one_kronecker_one : (1 : Matrix ι ι ℂ) ⊗ₖ (1 : Matrix Γ Γ ℂ) = 1)

def productDensity (ρ : Density ι) (σ : Density Γ) : Density (ι × Γ) where
  matrix := ρ.matrix ⊗ₖ σ.matrix
  positive := by
    obtain ⟨Q, hQ⟩ := TensorCopies.psd_exists_gram ρ.matrix ρ.positive
    obtain ⟨R, hR⟩ := TensorCopies.psd_exists_gram σ.matrix σ.positive
    have h := Matrix.posSemidef_conjTranspose_mul_self (Q ⊗ₖ R)
    simpa only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hQ, hR] using h
  trace_one := by rw [Matrix.trace_kronecker, ρ.trace_one, σ.trace_one, one_mul]

theorem ignoreFactor_born (M : DominatedPOVM ι Ω) (ρ : Density ι) (σ : Density Γ) (y : Ω) :
    (ignoreFactor (Γ := Γ) M).born (productDensity ρ σ) y = M.born ρ y := by
  change (Matrix.trace ((ρ.matrix ⊗ₖ σ.matrix) * (M.effect y ⊗ₖ 1))).re = _
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.trace_kronecker, σ.trace_one, mul_one]
  rfl

theorem ignoreFactor_outcomeMeasure (M : DominatedPOVM ι Ω) (ρ : Density ι) (σ : Density Γ) :
    (ignoreFactor M).outcomeMeasure (productDensity ρ σ) = M.outcomeMeasure ρ := by
  change M.reference.withDensity _ = M.reference.withDensity _
  simp_rw [ignoreFactor_born]

def splitEquiv (n k : ℕ) : ((Fin n → ι) × (Fin k → ι)) ≃ (Fin (n+k) → ι) where
  toFun x := Fin.addCases x.1 x.2
  invFun x := (fun i => x (Fin.castAdd k i), fun j => x (Fin.natAdd n j))
  left_inv x := by ext <;> simp
  right_inv x := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp

theorem split_matrix (A : Matrix ι ι ℂ) (n k : ℕ) :
    matrix (splitEquiv (ι := ι) n k) (TensorCopies.matrix A n ⊗ₖ TensorCopies.matrix A k) =
      TensorCopies.matrix A (n+k) := by
  ext x y
  change (∏ i : Fin n, A (x (Fin.castAdd k i)) (y (Fin.castAdd k i))) *
    (∏ j : Fin k, A (x (Fin.natAdd n j)) (y (Fin.natAdd n j))) = _
  exact (Fin.prod_univ_add (fun i : Fin (n+k) => A (x i) (y i))).symm

theorem split_density (ρ : Density ι) (n k : ℕ) :
    density (splitEquiv n k) (productDensity (TensorCopies.density ρ n) (TensorCopies.density ρ k)) =
      TensorCopies.density ρ (n+k) := by
  apply CommonCenter.density_eq_of_matrix
  exact split_matrix ρ.matrix n k

def pad (n k : ℕ) (M : DominatedPOVM (Fin n → ι) Ω) : DominatedPOVM (Fin (n+k) → ι) Ω :=
  povm (splitEquiv n k) (ignoreFactor (Γ := Fin k → ι) M)

theorem pad_outcomeMeasure (n k : ℕ) (M : DominatedPOVM (Fin n → ι) Ω) (ρ : Density ι) :
    (pad n k M).outcomeMeasure (TensorCopies.density ρ (n+k)) =
      M.outcomeMeasure (TensorCopies.density ρ n) := by
  rw [← split_density ρ n k]
  unfold pad
  rw [ProductCollectiveMeasurement.povm_outcomeMeasure, ignoreFactor_outcomeMeasure]

def padTo {n N : ℕ} (h : n ≤ N) (M : DominatedPOVM (Fin n → ι) Ω) :
    DominatedPOVM (Fin N → ι) Ω :=
  (Nat.add_sub_of_le h) ▸ pad n (N-n) M

theorem cast_outcomeMeasure {n N : ℕ} (e : n = N)
    (M : DominatedPOVM (Fin n → ι) Ω) (ρ : Density ι) :
    (show DominatedPOVM (Fin N → ι) Ω from e ▸ M).outcomeMeasure (TensorCopies.density ρ N) =
      M.outcomeMeasure (TensorCopies.density ρ n) := by
  cases e
  rfl

theorem padTo_outcomeMeasure {n N : ℕ} (h : n ≤ N)
    (M : DominatedPOVM (Fin n → ι) Ω) (ρ : Density ι) :
    (padTo h M).outcomeMeasure (TensorCopies.density ρ N) = M.outcomeMeasure (TensorCopies.density ρ n) := by
  exact (cast_outcomeMeasure (Nat.add_sub_of_le h) (pad n (N-n) M) ρ).trans
    (pad_outcomeMeasure n (N-n) M ρ)

end Paper26.CollectivePadding

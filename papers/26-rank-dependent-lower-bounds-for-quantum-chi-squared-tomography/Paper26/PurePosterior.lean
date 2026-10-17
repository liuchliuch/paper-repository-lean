import Paper26.PureCovariant
import Mathlib.GroupTheory.Perm.Fin

/-!
# Actual partial traces and the pure-state posterior

The matrices below are ordinary finite complex matrices.  The one-body
reduction is obtained by summing diagonal blocks, including every remaining
tensor coordinate.  No posterior identity is included in an input.
-/
noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators Matrix ComplexOrder
open MeasureTheory

namespace Paper26.PurePosterior
open QuantumModel SymmetricSupport

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- The ordinary partial trace, retaining the first factor. -/
def partialTrace (E : Matrix (ι × κ) (ι × κ) ℂ) : Matrix ι ι ℂ :=
  fun i j => ∑ k, E (i, k) (j, k)

omit [DecidableEq ι] [DecidableEq κ] in
theorem partialTrace_positive (E : Matrix (ι × κ) (ι × κ) ℂ)
    (hE : E.PosSemidef) : (partialTrace E).PosSemidef := by
  have heq : partialTrace E = ∑ k : κ, E.submatrix (fun i => (i, k)) (fun i => (i, k)) := by
    ext i j
    simp [partialTrace, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [heq]
  exact Finset.sum_induction _ _ (fun _ _ hA hB => hA.add hB)
    Matrix.PosSemidef.zero (fun k _ => hE.submatrix _)

omit [DecidableEq ι] [DecidableEq κ] in
theorem trace_partialTrace (E : Matrix (ι × κ) (ι × κ) ℂ) :
    Matrix.trace (partialTrace E) = Matrix.trace E := by
  simp [partialTrace, Matrix.trace, Fintype.sum_prod_type]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem partialTrace_add (E F : Matrix (ι × κ) (ι × κ) ℂ) :
    partialTrace (E + F) = partialTrace E + partialTrace F := by
  ext i j
  simp [partialTrace, Finset.sum_add_distrib]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem partialTrace_smul (c : ℂ) (E : Matrix (ι × κ) (ι × κ) ℂ) :
    partialTrace (c • E) = c • partialTrace E := by
  ext i j
  simp [partialTrace, Finset.mul_sum]

/-- Splitting off the first actual tensor factor. -/
def consEquiv (n : ℕ) : ι × (Fin n → ι) ≃ (Fin (n + 1) → ι) where
  toFun x := Fin.cons (α := fun _ => ι) x.1 x.2
  invFun x := (x 0, fun j => x j.succ)
  left_inv x := by cases x; rfl
  right_inv x := by ext j; exact Fin.cases rfl (fun _ => rfl) j

/-- The actual one-body reduction of an `(n+1)`-copy effect. -/
def oneBody {n : ℕ} (E : Matrix (Fin (n + 1) → ι) (Fin (n + 1) → ι) ℂ) :
    Matrix ι ι ℂ := partialTrace (E.submatrix (consEquiv n) (consEquiv n))

omit [DecidableEq ι] in
theorem oneBody_positive {n : ℕ}
    (E : Matrix (Fin (n + 1) → ι) (Fin (n + 1) → ι) ℂ) (hE : E.PosSemidef) :
    (oneBody E).PosSemidef := partialTrace_positive _ (hE.submatrix _)

omit [DecidableEq ι] in
theorem trace_oneBody {n : ℕ}
    (E : Matrix (Fin (n + 1) → ι) (Fin (n + 1) → ι) ℂ) :
    Matrix.trace (oneBody E) = Matrix.trace E := by
  rw [oneBody, trace_partialTrace]
  exact Equiv.sum_comp (consEquiv n) (fun x => E x x)

/-- Normalizing the genuine partial trace by the genuine positive effect
trace gives the density denoted by `τ_E` in Appendix A.1. -/
def reducedDensity {n : ℕ}
    (E : Matrix (Fin (n + 1) → ι) (Fin (n + 1) → ι) ℂ)
    (hE : E.PosSemidef) (hTr : 0 < (Matrix.trace E).re) : Density ι where
  matrix := ((Matrix.trace E).re)⁻¹ • oneBody E
  positive := (oneBody_positive E hE).smul (inv_nonneg.mpr hTr.le)
  trace_one := by
    rw [Matrix.trace_smul, trace_oneBody]
    have ht : Matrix.trace E = ((Matrix.trace E).re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im] using (Complex.nonneg_iff.mp hE.trace_nonneg).2.symm
    rw [Complex.real_smul, ht]
    simp only [Complex.ofReal_re, ← Complex.ofReal_mul, inv_mul_cancel₀ hTr.ne',
      Complex.ofReal_one]

/-- A permutation of tensor factors acts on the actual matrix indices. -/
def factorPermutation {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n → ι) where
  toFun x := x ∘ e
  invFun x := x ∘ e.symm
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp

/-- The matrix of the actual permutation action on coordinate vectors. -/
def permutationMatrix {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Matrix (Fin n → ι) (Fin n → ι) ℂ :=
  fun x y => if y = x ∘ e then 1 else 0

theorem permutationMatrix_mulVec {n : ℕ} (e : Equiv.Perm (Fin n))
    (z : (Fin n → ι) → ℂ) (x : Fin n → ι) :
    (permutationMatrix e *ᵥ z) x = z (x ∘ e) := by
  simp [permutationMatrix, Matrix.mulVec, dotProduct]

theorem permutationMatrix_mul {n : ℕ} (e : Equiv.Perm (Fin n))
    (A : Matrix (Fin n → ι) (Fin n → ι) ℂ) (x y : Fin n → ι) :
    (permutationMatrix (ι := ι) e * A) x y = A (x ∘ e) y := by
  simp [permutationMatrix, Matrix.mul_apply]

omit [DecidableEq ι] in
theorem symmetric_projector_rows {n : ℕ} (P : SymmetricProjectorInput ι n)
    (e : Equiv.Perm (Fin n)) (x y : Fin n → ι) :
    P.projector.matrix (x ∘ e) y = P.projector.matrix x y := by
  have hcol : P.projector.matrix *ᵥ (fun x => P.projector.matrix x y) =
      (fun x => P.projector.matrix x y) := by
    funext x
    exact congrFun (congrFun P.projector.idempotent x) y
  exact (P.fixed_vectors _).1 hcol e x

omit [DecidableEq ι] in
/-- Symmetric compression implies separate permutation invariance of the
effect's rows.  This is stronger than invariance under joint conjugation. -/
theorem compressed_rows {n : ℕ} (P : SymmetricProjectorInput ι n)
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ)
    (hE : E = P.projector.matrix * E * P.projector.matrix)
    (e : Equiv.Perm (Fin n)) (x y : Fin n → ι) : E (x ∘ e) y = E x y := by
  have hPE : P.projector.matrix * E = E := by
    calc
      P.projector.matrix * E = P.projector.matrix * (P.projector.matrix * E * P.projector.matrix) := by
        rw [← hE]
      _ = P.projector.matrix * E * P.projector.matrix := by
        simp only [← Matrix.mul_assoc, P.projector.idempotent]
      _ = E := hE.symm
  calc
    E (x ∘ e) y = (P.projector.matrix * E) (x ∘ e) y := by rw [hPE]
    _ = (P.projector.matrix * E) x y := by
      simp only [Matrix.mul_apply, symmetric_projector_rows]
    _ = E x y := by rw [hPE]

omit [Fintype ι] in
theorem permutationMatrix_conjTranspose {n : ℕ} (e : Equiv.Perm (Fin n)) :
    (permutationMatrix (ι := ι) e)ᴴ = permutationMatrix e.symm := by
  ext x y
  have hxy : x = y ∘ e ↔ y = x ∘ e.symm := by
    constructor
    · intro h
      rw [h]
      ext i
      simp
    · intro h
      rw [h]
      ext i
      simp
  simp [permutationMatrix, Matrix.conjTranspose_apply, hxy]

def permutationSum (n : ℕ) : Matrix (Fin n → ι) (Fin n → ι) ℂ :=
  ∑ e : Equiv.Perm (Fin n), permutationMatrix e

omit [Fintype ι] in
theorem permutationSum_rows (n : ℕ) (g : Equiv.Perm (Fin n))
    (x y : Fin n → ι) :
    permutationSum n (x ∘ g) y = permutationSum n x y := by
  change (∑ e : Equiv.Perm (Fin n), permutationMatrix e) (x ∘ g) y = _
  simp only [Matrix.sum_apply, permutationSum]
  have he (e : Equiv.Perm (Fin n)) :
      permutationMatrix (ι := ι) e (x ∘ g) y = permutationMatrix (g * e) x y := rfl
  simp_rw [he]
  exact (Equiv.sum_comp (Equiv.mulLeft g) (fun e => permutationMatrix e x y))

omit [Fintype ι] in
theorem permutationSum_hermitian (n : ℕ) :
    (permutationSum (ι := ι) n)ᴴ = permutationSum n := by
  unfold permutationSum
  rw [Matrix.conjTranspose_sum]
  simp_rw [permutationMatrix_conjTranspose]
  exact Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n))) _

/-- The usual permutation average follows from the existing actual
orthogonal projector and its fixed-vector characterization. -/
theorem projector_eq_permutation_average {n : ℕ} (P : SymmetricProjectorInput ι n) :
    P.projector.matrix = ((n.factorial : ℂ)⁻¹) • permutationSum n := by
  let S := permutationSum (ι := ι) n
  have hPS : P.projector.matrix * S = S := by
    ext x y
    have hz : P.projector.matrix *ᵥ (fun x => S x y) = (fun x => S x y) := by
      apply (P.fixed_vectors _).2
      intro e x
      exact permutationSum_rows n e x y
    exact congrFun hz x
  have hSP : S * P.projector.matrix = (n.factorial : ℂ) • P.projector.matrix := by
    change (∑ e : Equiv.Perm (Fin n), permutationMatrix e) * P.projector.matrix = _
    rw [Finset.sum_mul]
    have he (e : Equiv.Perm (Fin n)) :
        permutationMatrix (ι := ι) e * P.projector.matrix = P.projector.matrix := by
      ext x y
      rw [permutationMatrix_mul, symmetric_projector_rows]
    simp_rw [he]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin, Nat.cast_smul_eq_nsmul]
  have hS : Sᴴ = S := permutationSum_hermitian n
  have hh := congrArg Matrix.conjTranspose hSP
  simp only [Matrix.conjTranspose_mul, P.projector.hermitian.eq, hS,
    Matrix.conjTranspose_smul, star_natCast] at hh
  rw [hPS] at hh
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  change P.projector.matrix = (n.factorial : ℂ)⁻¹ • S
  rw [hh, smul_smul, inv_mul_cancel₀ hf, one_smul]

theorem permutationSum_eq {n : ℕ} (P : SymmetricProjectorInput ι n) :
    permutationSum n = (n.factorial : ℂ) • P.projector.matrix := by
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [projector_eq_permutation_average, smul_smul, mul_inv_cancel₀ hf, one_smul]

def swappedTail {n : ℕ} (x : Fin (n + 1) → ι) (p : Fin (n + 1)) : Fin n → ι :=
  fun j => x (Equiv.swap 0 p j.succ)

omit [Fintype ι] in
theorem decomposition_entry {n : ℕ} (p : Fin (n + 1)) (e : Equiv.Perm (Fin n))
    (x y : Fin (n + 1) → ι) :
    permutationMatrix (Equiv.Perm.decomposeFin.symm (p, e)) x y =
      if y 0 = x p then permutationMatrix e (swappedTail x p) (y ∘ Fin.succ) else 0 := by
  have heq : y = x ∘ ⇑(Equiv.Perm.decomposeFin.symm (p, e)) ↔
      y 0 = x p ∧ y ∘ Fin.succ = swappedTail x p ∘ e := by
    constructor
    · intro h
      subst y
      constructor
      · simp
      · ext j
        simp [swappedTail]
    · rintro ⟨h0, hs⟩
      ext j
      refine Fin.cases ?_ (fun k => ?_) j
      · simpa using h0
      · simpa [swappedTail] using congrFun hs k
  simp only [permutationMatrix, heq]
  split_ifs <;> simp_all

/-- The standard one-step symmetric-projector recurrence, proved by
decomposing actual factor permutations into a swap and a permutation of
the other factors.  The first coordinate is the new tensor factor. -/
theorem symmetric_projector_recurrence {n : ℕ}
    (P : SymmetricProjectorInput ι n) (Q : SymmetricProjectorInput ι (n + 1))
    (x y : Fin (n + 1) → ι) :
    Q.projector.matrix x y = ((n + 1 : ℕ) : ℂ)⁻¹ *
      ∑ p : Fin (n + 1),
        if y 0 = x p then P.projector.matrix (swappedTail x p) (y ∘ Fin.succ) else 0 := by
  rw [projector_eq_permutation_average Q]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have he : (permutationSum (ι := ι) (n + 1)) x y =
      ∑ p : Fin (n + 1), if y 0 = x p then
        (n.factorial : ℂ) * P.projector.matrix (swappedTail x p) (y ∘ Fin.succ) else 0 := by
    unfold permutationSum
    simp only [Matrix.sum_apply]
    rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro p _
    simp_rw [decomposition_entry]
    by_cases hp : y 0 = x p
    · simp only [hp, ↓reduceIte]
      simpa only [permutationSum, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using
        congrFun (congrFun (permutationSum_eq P) (swappedTail x p)) (y ∘ Fin.succ)
    · simp [hp]
  rw [he]
  have hs : (∑ p : Fin (n + 1), if y 0 = x p then
      (n.factorial : ℂ) * P.projector.matrix (swappedTail x p) (y ∘ Fin.succ) else 0) =
      (n.factorial : ℂ) * ∑ p : Fin (n + 1),
        if y 0 = x p then P.projector.matrix (swappedTail x p) (y ∘ Fin.succ) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> simp
  rw [hs, ← mul_assoc]
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul, _root_.mul_inv_rev]
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

omit [DecidableEq ι] in
theorem symmetric_projector_cols {n : ℕ} (P : SymmetricProjectorInput ι n)
    (e : Equiv.Perm (Fin n)) (x y : Fin n → ι) :
    P.projector.matrix x (y ∘ e) = P.projector.matrix x y := by
  have h := congrArg star (symmetric_projector_rows P e y x)
  have hH (a b) : star (P.projector.matrix a b) = P.projector.matrix b a := by
    exact congrFun (congrFun P.projector.hermitian.eq b) a
  simpa only [hH] using h

omit [DecidableEq ι] in
theorem compressed_cols {n : ℕ} (P : SymmetricProjectorInput ι n)
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ)
    (hE : E = P.projector.matrix * E * P.projector.matrix)
    (e : Equiv.Perm (Fin n)) (x y : Fin n → ι) : E x (y ∘ e) = E x y := by
  have hEP : E * P.projector.matrix = E := by
    calc
      E * P.projector.matrix = (P.projector.matrix * E * P.projector.matrix) * P.projector.matrix := by
        rw [← hE]
      _ = P.projector.matrix * E * P.projector.matrix := by
        simp only [Matrix.mul_assoc, P.projector.idempotent]
      _ = E := hE.symm
  calc
    E x (y ∘ e) = (E * P.projector.matrix) x (y ∘ e) := by rw [hEP]
    _ = (E * P.projector.matrix) x y := by
      simp only [Matrix.mul_apply, symmetric_projector_cols]
    _ = E x y := by rw [hEP]

def insertEquiv {n : ℕ} (k : Fin (n + 1)) :
    ι × (Fin n → ι) ≃ (Fin (n + 1) → ι) :=
  (consEquiv n).trans (factorPermutation (Equiv.swap 0 k))

omit [Fintype ι] [DecidableEq ι] in
theorem insertEquiv_at {n : ℕ} (k : Fin (n + 1)) (a : ι) (z : Fin n → ι) :
    insertEquiv k (a, z) k = a := by
  simp [insertEquiv, factorPermutation, consEquiv]

omit [Fintype ι] [DecidableEq ι] in
theorem update_insertEquiv {n : ℕ} (k : Fin (n + 1)) (a b : ι) (z : Fin n → ι) :
    Function.update (insertEquiv k (a, z)) k b = insertEquiv k (b, z) := by
  ext q
  by_cases hq : q = k
  · subst q
    simp [insertEquiv_at]
  · have hs : Equiv.swap 0 k q ≠ 0 := by
      intro h
      have hh := congrArg (Equiv.swap 0 k) h
      exact hq (by simpa using hh)
    simp only [Function.update_of_ne hq]
    change (Fin.cons (α := fun _ => ι) a z : Fin (n + 1) → ι) (Equiv.swap 0 k q) =
      (Fin.cons (α := fun _ => ι) b z : Fin (n + 1) → ι) (Equiv.swap 0 k q)
    obtain ⟨j, hj⟩ := Fin.eq_succ_of_ne_zero hs
    simp [hj]

omit [Fintype ι] [DecidableEq ι] in
theorem swappedTail_cons_succ {n : ℕ} (i : ι) (x : Fin n → ι) (k : Fin n) :
    swappedTail (Fin.cons (α := fun _ => ι) i x) k.succ = Function.update x k i := by
  ext q
  by_cases hq : q = k
  · subst q
    simp [swappedTail]
  · have hqs : q.succ ≠ k.succ := fun h => hq (Fin.succ_injective _ h)
    simp [swappedTail, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero q) hqs, hq]

omit [Fintype ι] [DecidableEq ι] in
theorem swappedTail_cons_zero {n : ℕ} (i : ι) (x : Fin n → ι) :
    swappedTail (Fin.cons (α := fun _ => ι) i x) 0 = x := by
  ext q
  simp [swappedTail]

/-- The contribution of swapping the new factor with an old factor. -/
def swapContraction {n : ℕ}
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) (k : Fin n) (i j : ι) : ℂ :=
  ∑ x : Fin n → ι, if j = x k then E (Function.update x k i) x else 0

/-- Each swap contracts to the actual partial trace in that coordinate. -/
theorem swapContraction_eq {n : ℕ}
    (E : Matrix (Fin (n + 1) → ι) (Fin (n + 1) → ι) ℂ)
    (k : Fin (n + 1)) (i j : ι) :
    swapContraction E k i j =
      partialTrace (E.submatrix (insertEquiv k) (insertEquiv k)) i j := by
  unfold swapContraction
  rw [← Equiv.sum_comp (insertEquiv k), Fintype.sum_prod_type]
  simp_rw [insertEquiv_at, update_insertEquiv]
  rw [Finset.sum_comm]
  simp [partialTrace, Matrix.submatrix_apply]

/-- Symmetric compression makes all genuine one-body reductions equal. -/
theorem swapContraction_compressed {n : ℕ}
    (P : SymmetricProjectorInput ι (n + 1))
    (E : Matrix (Fin (n + 1) → ι) (Fin (n + 1) → ι) ℂ)
    (hE : E = P.projector.matrix * E * P.projector.matrix)
    (k : Fin (n + 1)) (i j : ι) : swapContraction E k i j = oneBody E i j := by
  rw [swapContraction_eq]
  change (∑ z : Fin n → ι, E ((Fin.cons (α := fun _ => ι) i z) ∘ Equiv.swap 0 k)
    ((Fin.cons (α := fun _ => ι) j z) ∘ Equiv.swap 0 k)) = ∑ z : Fin n → ι, E (Fin.cons (α := fun _ => ι) i z) (Fin.cons (α := fun _ => ι) j z)
  simp_rw [compressed_rows P E hE, compressed_cols P E hE]

def contraction {n : ℕ}
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ)
    (A : Matrix (Fin (n + 1) → ι) (Fin (n + 1) → ι) ℂ) (i j : ι) : ℂ :=
  ∑ x : Fin n → ι, ∑ y : Fin n → ι, A (Fin.cons (α := fun _ => ι) i x) (Fin.cons (α := fun _ => ι) j y) * E y x

/-- The exact matrix contraction underlying Appendix A.1.  There are no
diagonal-effect or commuting assumptions: every entry of `E` is retained. -/
theorem contraction_symmetric {n : ℕ}
    (P : SymmetricProjectorInput ι (n + 1))
    (Q : SymmetricProjectorInput ι (n + 2))
    (E : Matrix (Fin (n + 1) → ι) (Fin (n + 1) → ι) ℂ)
    (hE : E = P.projector.matrix * E * P.projector.matrix) (i j : ι) :
    contraction E Q.projector.matrix i j = ((n + 2 : ℕ) : ℂ)⁻¹ *
      ((Matrix.trace E) * (1 : Matrix ι ι ℂ) i j +
        ((n + 1 : ℕ) : ℂ) * oneBody E i j) := by
  have hPE : P.projector.matrix * E = E := by
    calc
      P.projector.matrix * E = P.projector.matrix * (P.projector.matrix * E * P.projector.matrix) := by
        rw [← hE]
      _ = P.projector.matrix * E * P.projector.matrix := by
        simp only [← Matrix.mul_assoc, P.projector.idempotent]
      _ = E := hE.symm
  have hc (p : Fin (n + 2)) (x : Fin (n + 1) → ι) :
      (∑ y : Fin (n + 1) → ι,
        (if (Fin.cons (α := fun _ => ι) j y) 0 = (Fin.cons (α := fun _ => ι) i x) p then
          P.projector.matrix (swappedTail (Fin.cons (α := fun _ => ι) i x) p) ((Fin.cons (α := fun _ => ι) j y) ∘ Fin.succ)
        else 0) * E y x) =
        if j = (Fin.cons (α := fun _ => ι) i x) p then E (swappedTail (Fin.cons (α := fun _ => ι) i x) p) x else 0 := by
    simp only [Fin.cons_zero, Fin.cons_succ, Function.comp_def]
    by_cases hp : j = (Fin.cons (α := fun _ => ι) i x) p
    · simp only [hp, ↓reduceIte]
      exact congrFun (congrFun hPE (swappedTail (Fin.cons (α := fun _ => ι) i x) p)) x
    · simp [hp]
  unfold contraction
  calc
    _ = ((n + 2 : ℕ) : ℂ)⁻¹ *
        ∑ x : Fin (n + 1) → ι, ∑ y : Fin (n + 1) → ι,
          ∑ p : Fin (n + 2),
            (if (Fin.cons (α := fun _ => ι) j y) 0 = (Fin.cons (α := fun _ => ι) i x) p then
              P.projector.matrix (swappedTail (Fin.cons (α := fun _ => ι) i x) p) ((Fin.cons (α := fun _ => ι) j y) ∘ Fin.succ)
            else 0) * E y x := by
      simp_rw [symmetric_projector_recurrence P Q]
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ = ((n + 2 : ℕ) : ℂ)⁻¹ *
        ∑ p : Fin (n + 2), ∑ x : Fin (n + 1) → ι,
          if j = (Fin.cons (α := fun _ => ι) i x) p then E (swappedTail (Fin.cons (α := fun _ => ι) i x) p) x else 0 := by
      congr 1
      conv_lhs => arg 2; intro x; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      simp_rw [hc]
    _ = _ := by
      congr 1
      rw [Fin.sum_univ_succ]
      have h0 : (∑ x : Fin (n + 1) → ι,
          if j = (Fin.cons (α := fun _ => ι) i x) 0 then E (swappedTail (Fin.cons (α := fun _ => ι) i x) 0) x else 0) =
          Matrix.trace E * (1 : Matrix ι ι ℂ) i j := by
        by_cases hij : i = j
        · subst j
          simp [swappedTail_cons_zero, Matrix.trace]
        · simp [hij, Ne.symm hij]
      rw [h0]
      congr 1
      have hk (k : Fin (n + 1)) :
          (∑ x : Fin (n + 1) → ι,
            if j = (Fin.cons (α := fun _ => ι) i x) k.succ then E (swappedTail (Fin.cons (α := fun _ => ι) i x) k.succ) x else 0) =
          oneBody E i j := by
        simpa only [Fin.cons_succ, swappedTail_cons_succ] using
          swapContraction_compressed P E hE k i j
      simp_rw [hk]
      simp

open HaarFrames PureCovariant

/-- The actual (complex-written) Born likelihood of a tensor effect. -/
def complexLikelihood {n : ℕ}
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) (U : Frame ι (Fin 1)) : ℂ :=
  Matrix.trace ((TensorCopies.density U.density n).matrix * E)

def likelihood {n : ℕ}
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) (U : Frame ι (Fin 1)) : ℝ :=
  (complexLikelihood E U).re

theorem likelihood_nonneg {n : ℕ}
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) (hE : E.PosSemidef)
    (U : Frame ι (Fin 1)) : 0 ≤ likelihood E U :=
  QuantumModel.trace_mul_effect_nonneg (TensorCopies.density U.density n) hE

theorem complexLikelihood_real {n : ℕ}
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) (hE : E.PosSemidef)
    (U : Frame ι (Fin 1)) : complexLikelihood E U = (likelihood E U : ℂ) := by
  apply Complex.ext
  · rfl
  · exact EnergyReality.trace_hermitian_product_im _ _
      (TensorCopies.density U.density n).hermitian.eq hE.isHermitian.eq

theorem complexLikelihood_integrable (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    {n : ℕ} (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) :
    Integrable (complexLikelihood E) μ := by
  unfold complexLikelihood
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact integrable_finset_sum _ fun x _ => integrable_finset_sum _ fun y _ =>
    (tensor_entry_integrable μ n x y).mul_const (E y x)

theorem likelihood_integrable (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    {n : ℕ} (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) :
    Integrable (likelihood E) μ := (complexLikelihood_integrable μ E).re

theorem tensor_entry_succ (U : Frame ι (Fin 1)) (n : ℕ) (i j : ι)
    (x y : Fin n → ι) :
    (TensorCopies.density U.density (n + 1)).matrix
      (Fin.cons (α := fun _ => ι) i x) (Fin.cons (α := fun _ => ι) j y) =
      U.density.matrix i j * (TensorCopies.density U.density n).matrix x y := by
  simp [TensorCopies.density_matrix, Fin.prod_univ_succ]

theorem complexLikelihood_mul_entry {n : ℕ}
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) (U : Frame ι (Fin 1)) (i j : ι) :
    complexLikelihood E U * U.density.matrix i j =
      ∑ x : Fin n → ι, ∑ y : Fin n → ι,
        (TensorCopies.density U.density (n + 1)).matrix
          (Fin.cons (α := fun _ => ι) i x) (Fin.cons (α := fun _ => ι) j y) * E y x := by
  simp only [complexLikelihood, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Finset.sum_mul, tensor_entry_succ]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem weighted_entry_integrable (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    {n : ℕ} (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) (i j : ι) :
    Integrable (fun U => complexLikelihood E U * U.density.matrix i j) μ := by
  simp_rw [complexLikelihood_mul_entry]
  exact integrable_finset_sum _ fun x _ => integrable_finset_sum _ fun y _ =>
    (tensor_entry_integrable μ (n + 1) _ _).mul_const (E y x)

/-- The denominator of the Bayesian posterior is obtained from the actual
`n`-copy Haar moment. -/
theorem likelihood_integral (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ} (P : SymmetricProjectorInput ι n)
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ)
    (hE : E = P.projector.matrix * E * P.projector.matrix) :
    (∫ U, complexLikelihood E U ∂μ) =
      ((dimension ι n : ℝ)⁻¹ : ℂ) * Matrix.trace E := by
  have hPE : P.projector.matrix * E = E := by
    calc
      P.projector.matrix * E = P.projector.matrix * (P.projector.matrix * E * P.projector.matrix) := by
        rw [← hE]
      _ = P.projector.matrix * E * P.projector.matrix := by
        simp only [← Matrix.mul_assoc, P.projector.idempotent]
      _ = E := hE.symm
  unfold complexLikelihood
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [integral_finset_sum _ (fun x _ => integrable_finset_sum _ fun y _ =>
    (tensor_entry_integrable μ n x y).mul_const (E y x))]
  simp_rw [integral_finset_sum _ (fun y _ =>
    (tensor_entry_integrable μ n _ y).mul_const (E y _)), integral_mul_const, H.moment n P]
  have he : (∑ x, ∑ y, ((dimension ι n : ℝ)⁻¹ : ℂ) * P.projector.matrix x y * E y x) =
      ((dimension ι n : ℝ)⁻¹ : ℂ) * Matrix.trace (P.projector.matrix * E) := by
    simp [Matrix.trace, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
  rw [he, hPE]
  rfl

/-- The `n+1` Haar moment is the actual unnormalized first posterior moment. -/
theorem weighted_entry_integral (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ} (Q : SymmetricProjectorInput ι (n + 1))
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) (i j : ι) :
    (∫ U, complexLikelihood E U * U.density.matrix i j ∂μ) =
      ((dimension ι (n + 1) : ℝ)⁻¹ : ℂ) * contraction E Q.projector.matrix i j := by
  simp_rw [complexLikelihood_mul_entry]
  rw [integral_finset_sum _ (fun x _ => integrable_finset_sum _ fun y _ =>
    (tensor_entry_integrable μ (n + 1) _ _).mul_const (E y x))]
  have hi (x : Fin n → ι) :
      (∫ U : Frame ι (Fin 1), ∑ y : Fin n → ι,
        (TensorCopies.density U.density (n + 1)).matrix
          (Fin.cons (α := fun _ => ι) i x) (Fin.cons (α := fun _ => ι) j y) * E y x ∂μ) =
      ∑ y : Fin n → ι, (∫ U : Frame ι (Fin 1),
        (TensorCopies.density U.density (n + 1)).matrix
          (Fin.cons (α := fun _ => ι) i x) (Fin.cons (α := fun _ => ι) j y) * E y x ∂μ) :=
    integral_finset_sum _ (fun y _ => (tensor_entry_integrable μ (n + 1) _ _).mul_const (E y x))
  simp_rw [hi, integral_mul_const, H.moment (n + 1) Q]
  simp [contraction, Finset.mul_sum, mul_assoc]

theorem likelihood_integral_real (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ} (P : SymmetricProjectorInput ι n)
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ)
    (hE : E = P.projector.matrix * E * P.projector.matrix) :
    (∫ U, likelihood E U ∂μ) = (dimension ι n : ℝ)⁻¹ * (Matrix.trace E).re := by
  have hi := integral_re (complexLikelihood_integrable μ E)
  simp only [RCLike.re_eq_complex_re] at hi
  rw [likelihood_integral μ H P E hE] at hi
  simpa [likelihood, Complex.mul_re] using hi

omit [DecidableEq ι] in
theorem dimension_inverse_recurrence [Nonempty ι] (n : ℕ) :
    ((dimension ι (n + 1) : ℝ)⁻¹ : ℂ) * ((n + 1 : ℕ) : ℂ)⁻¹ =
      ((dimension ι n : ℝ)⁻¹ : ℂ) * (((n : ℝ) + Fintype.card ι)⁻¹ : ℂ) := by
  have hD : (dimension ι n : ℂ) ≠ 0 := by exact_mod_cast (dimension_pos (ι := ι) n).ne'
  have hN : (dimension ι (n + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (dimension_pos (ι := ι) (n + 1)).ne'
  have hS : (n : ℂ) + Fintype.card ι ≠ 0 := by
    have hp : (0 : ℝ) < (n : ℝ) + Fintype.card ι := by
      have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
      positivity
    exact_mod_cast hp.ne'
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hr := dimension_recurrence (ι := ι) n
  have hc : (dimension ι n : ℂ) * ((n : ℂ) + Fintype.card ι) =
      (dimension ι (n + 1) : ℂ) * ((n + 1 : ℕ) : ℂ) := by exact_mod_cast hr
  push_cast
  field_simp
  simpa only [Nat.cast_add, Nat.cast_one] using hc

/-- The genuine unnormalized posterior first moment, with exact symmetric
dimension and copy-number constants. -/
theorem first_moment [Nonempty ι]
    (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ}
    (P : SymmetricProjectorInput ι (n + 1)) (Q : SymmetricProjectorInput ι (n + 2))
    (E : Matrix (Fin (n + 1) → ι) (Fin (n + 1) → ι) ℂ)
    (hE : E = P.projector.matrix * E * P.projector.matrix) (i j : ι) :
    (∫ U, complexLikelihood E U * U.density.matrix i j ∂μ) =
      ((dimension ι (n + 1) : ℝ)⁻¹ : ℂ) *
      ((((n + 1 : ℕ) : ℝ) + Fintype.card ι)⁻¹ : ℂ) *
      (Matrix.trace E * (1 : Matrix ι ι ℂ) i j + ((n + 1 : ℕ) : ℂ) * oneBody E i j) := by
  rw [weighted_entry_integral μ H Q E i j, contraction_symmetric P Q E hE i j,
    ← mul_assoc, dimension_inverse_recurrence (n + 1)]

/-- The entrywise actual Bayesian posterior mean.  Its denominator is the
integrated Born likelihood; its numerator integrates the actual input state. -/
def posteriorMeanMatrix (μ : Measure (Frame ι (Fin 1))) {n : ℕ}
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) : Matrix ι ι ℂ :=
  ((((∫ U, likelihood E U ∂μ) : ℝ)⁻¹ : ℝ) : ℂ) •
    (fun i j => ∫ U, (likelihood E U : ℂ) * U.density.matrix i j ∂μ)

/-- Appendix A.1, Equation (51), for every PSD symmetric-compressed effect
of positive trace.  The density `τ_E` is the actual normalized partial trace. -/
theorem equation_51 [Nonempty ι]
    (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ}
    (P : SymmetricProjectorInput ι (n + 1)) (Q : SymmetricProjectorInput ι (n + 2))
    (E : Matrix (Fin (n + 1) → ι) (Fin (n + 1) → ι) ℂ)
    (hE : E.PosSemidef) (hTr : 0 < (Matrix.trace E).re)
    (hComp : E = P.projector.matrix * E * P.projector.matrix) :
    posteriorMeanMatrix μ E =
      (PureMinimax.posteriorMean (reducedDensity E hE hTr) (n + 1) (by positivity)).matrix := by
  have ht : Matrix.trace E = ((Matrix.trace E).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using (Complex.nonneg_iff.mp hE.trace_nonneg).2.symm
  have hD : (dimension ι (n + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (dimension_pos (ι := ι) (n + 1)).ne'
  have hT : ((Matrix.trace E).re : ℂ) ≠ 0 := by exact_mod_cast hTr.ne'
  ext i j
  change ((((∫ U, likelihood E U ∂μ) : ℝ)⁻¹ : ℝ) : ℂ) *
    (∫ U, (likelihood E U : ℂ) * U.density.matrix i j ∂μ) = _
  rw [likelihood_integral_real μ H P E hComp]
  simp_rw [← complexLikelihood_real E hE]
  rw [first_moment μ H P Q E hComp i j,
    PureMinimax.posteriorMean_affine]
  rw [ht]
  simp only [Matrix.smul_apply, Matrix.add_apply, reducedDensity, Complex.ofReal_re,
    Complex.real_smul, smul_eq_mul]
  push_cast
  field_simp

theorem symmetric_projector_one (P : SymmetricProjectorInput ι 1) :
    P.projector.matrix = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [Matrix.one_mulVec]
  apply (P.fixed_vectors _).2
  intro e x
  have he : e = 1 := Subsingleton.elim _ _
  rw [he]
  rfl

/-- The zero-data prior first moment is the actual uniform density. -/
theorem prior_mean [Nonempty ι]
    (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) (P : SymmetricProjectorInput ι 1) (i j : ι) :
    (∫ U, U.density.matrix i j ∂μ) =
      (AdaptiveCollectiveEmbedding.uniformState ι).matrix i j := by
  have h := H.moment 1 P (fun _ => i) (fun _ => j)
  rw [symmetric_projector_one P] at h
  have hd : dimension ι 1 = Fintype.card ι := by
    unfold dimension
    have he : 1 + Fintype.card ι - 1 = Fintype.card ι := by omega
    rw [he, Nat.choose_one_right]
  simpa [TensorCopies.density_matrix, AdaptiveCollectiveEmbedding.uniformState,
    hd, Matrix.one_apply, funext_iff] using h

theorem complexLikelihood_zero
    (E : Matrix (Fin 0 → ι) (Fin 0 → ι) ℂ) (U : Frame ι (Fin 1)) :
    complexLikelihood E U = Matrix.trace E := by
  have h0 : (TensorCopies.density U.density 0).matrix = 1 := by
    ext x y
    simp [TensorCopies.density_matrix, Matrix.one_apply, Subsingleton.elim x y]
  simp [complexLikelihood, h0]

/-- The no-copy posterior is uniform; no nonempty symmetric-reduction
coordinate or artificial `τ_E` is used in this branch. -/
theorem equation_51_zero [Nonempty ι]
    (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) (P : SymmetricProjectorInput ι 1)
    (E : Matrix (Fin 0 → ι) (Fin 0 → ι) ℂ) (hTr : 0 < (Matrix.trace E).re) :
    posteriorMeanMatrix μ E = (AdaptiveCollectiveEmbedding.uniformState ι).matrix := by
  ext i j
  change ((((∫ U, likelihood E U ∂μ) : ℝ)⁻¹ : ℝ) : ℂ) *
    (∫ U, (likelihood E U : ℂ) * U.density.matrix i j ∂μ) = _
  simp only [likelihood, complexLikelihood_zero, integral_const,
    measureReal_univ_eq_one, one_smul]
  rw [integral_const_mul, prior_mean μ H P]
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hTr.ne', Complex.ofReal_one, one_mul]

/-- The scalar Born likelihood is Borel on the actual frame space. -/
theorem likelihood_measurable {n : ℕ}
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) : Measurable (likelihood E) := by
  unfold likelihood complexLikelihood
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Measurable.re (𝕜 := ℂ)
  exact Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ =>
    (PureTensorSuccess.measurable_frame_tensor_entry n x y).mul_const (E y x)

def evidence (μ : Measure (Frame ι (Fin 1))) {n : ℕ}
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) : ℝ := ∫ U, likelihood E U ∂μ

def posteriorWeight (μ : Measure (Frame ι (Fin 1))) {n : ℕ}
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) (U : Frame ι (Fin 1)) : ℝ :=
  (evidence μ E)⁻¹ * likelihood E U

/-- Bayes' posterior on the actual pure-state frame space. -/
def posteriorMeasure (μ : Measure (Frame ι (Fin 1))) {n : ℕ}
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) : Measure (Frame ι (Fin 1)) :=
  μ.withDensity (fun U => ENNReal.ofReal (posteriorWeight μ E U))

theorem evidence_pos [Nonempty ι]
    (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ} (P : SymmetricProjectorInput ι n)
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ)
    (hComp : E = P.projector.matrix * E * P.projector.matrix)
    (hTr : 0 < (Matrix.trace E).re) : 0 < evidence μ E := by
  rw [evidence, likelihood_integral_real μ H P E hComp]
  exact mul_pos (inv_pos.mpr (by exact_mod_cast dimension_pos (ι := ι) n)) hTr

theorem posteriorWeight_nonneg (μ : Measure (Frame ι (Fin 1))) {n : ℕ}
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) (hE : E.PosSemidef)
    (he : 0 < evidence μ E) (U : Frame ι (Fin 1)) : 0 ≤ posteriorWeight μ E U :=
  mul_nonneg (inv_nonneg.mpr he.le) (likelihood_nonneg E hE U)

theorem posteriorWeight_integrable (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    {n : ℕ} (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) : Integrable (posteriorWeight μ E) μ :=
  (likelihood_integrable μ E).const_mul _

theorem integral_posteriorWeight (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    {n : ℕ} (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) (he : 0 < evidence μ E) :
    (∫ U, posteriorWeight μ E U ∂μ) = 1 := by
  unfold posteriorWeight
  rw [integral_const_mul]
  exact inv_mul_cancel₀ he.ne'

theorem posteriorMeasure_probability (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    {n : ℕ} (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) (hE : E.PosSemidef)
    (he : 0 < evidence μ E) : IsProbabilityMeasure (posteriorMeasure μ E) := by
  constructor
  rw [posteriorMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (posteriorWeight_integrable μ E)
      (ae_of_all _ (posteriorWeight_nonneg μ E hE he)), integral_posteriorWeight μ E he]
  simp only [ENNReal.ofReal_one]

theorem posteriorMeanMatrix_eq_integral (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    {n : ℕ} (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) (hE : E.PosSemidef)
    (he : 0 < evidence μ E) (i j : ι) :
    posteriorMeanMatrix μ E i j =
      ∫ U, U.density.matrix i j ∂posteriorMeasure μ E := by
  have hm : Measurable (fun U => ENNReal.ofReal (posteriorWeight μ E U)) :=
    ((likelihood_measurable E).const_mul _).ennreal_ofReal
  rw [posteriorMeasure, integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (posteriorWeight_nonneg μ E hE he _),
    posteriorWeight, Complex.real_smul, Complex.ofReal_mul]
  simp_rw [mul_assoc, integral_const_mul]
  rfl

/-- Equation (51) as an actual expectation under the normalized posterior
probability measure, rather than just a ratio of unnormalized moments. -/
theorem equation_51_integral [Nonempty ι]
    (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ}
    (P : SymmetricProjectorInput ι (n + 1)) (Q : SymmetricProjectorInput ι (n + 2))
    (E : Matrix (Fin (n + 1) → ι) (Fin (n + 1) → ι) ℂ)
    (hE : E.PosSemidef) (hTr : 0 < (Matrix.trace E).re)
    (hComp : E = P.projector.matrix * E * P.projector.matrix) (i j : ι) :
    (∫ U, U.density.matrix i j ∂posteriorMeasure μ E) =
      (PureMinimax.posteriorMean (reducedDensity E hE hTr) (n + 1) (by positivity)).matrix i j := by
  rw [← posteriorMeanMatrix_eq_integral μ E hE (evidence_pos μ H P E hComp hTr),
    equation_51 μ H P Q E hE hTr hComp]

end Paper26.PurePosterior

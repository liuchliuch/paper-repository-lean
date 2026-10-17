import Paper13.Singlet
import Paper13.MatrixDimension
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic

/-!
# Multi-angle algebra: ambient space, Lie closure, and dimension

We realize the real Lie algebras of Paper 13 as real subspaces of `Op n`
closed under the commutator `[A, B] = A * B - B * A`.

* `bitFlip n` is the global bit flip `F = X^{⊗ n}`, a Hermitian involution.
* `scSpace n` is the ambient space of paper eq. (16): skew-Hermitian operators
  commuting with `F` and traceless on each parity block.  Equivalently
  skew-Hermitian, `[A, F] = 0`, `tr A = 0`, `tr (A F) = 0`.
  The paper claims real dimension `2^{2n-1} - 2`; that dimension theorem remains open here.
* `lieClosure S` is the smallest real subspace containing `S` and closed under
  commutator (intersection of all Lie subspaces containing `S`).
* `gMa` is the multi-angle algebra `Lie_ℝ ( { i X_v } ∪ { i Z_u Z_v } )`.
* `gStd` is the standard algebra `Lie_ℝ { i H_X, i H_ZZ }`.

The external classification identifying `gMa` with this ambient space is not asserted here.
The former placeholder generation and dimension proofs have been removed from production.
-/

noncomputable section

open Matrix
open scoped BigOperators

namespace Paper13

/-! ## Global bit flip -/

/-- Basis action of the global bit flip. -/
def flipState {n : ℕ} (x : QubitBasis n) : QubitBasis n := fun w => 1 - x w

lemma flipState_involutive {n : ℕ} (x : QubitBasis n) :
    flipState (flipState x) = x := by
  funext w
  simp [flipState]

lemma flipState_inj {n : ℕ} {x y : QubitBasis n} (h : flipState x = flipState y) :
    x = y := by
  rw [← flipState_involutive x, ← flipState_involutive y, h]

lemma flipState_ne_self {n : ℕ} {x : QubitBasis n} (hne : Nonempty (Fin n)) :
    flipState x ≠ x := by
  intro hc
  obtain ⟨w⟩ := hne
  have := congr_fun hc w
  simp only [flipState] at this
  generalize hb : x w = b at this
  fin_cases b <;> norm_num at this

/-- Hermitian involution `F = X^{⊗ n}`: sends `|x⟩` to `|flip x⟩`. -/
def bitFlip (n : ℕ) : Op n :=
  fun x y => if y = flipState x then (1 : ℂ) else 0

lemma bitFlip_mul_self (n : ℕ) : bitFlip n * bitFlip n = 1 := by
  ext x y
  simp only [Matrix.mul_apply, bitFlip]
  rw [Fintype.sum_eq_single (flipState x)]
  · simp [flipState_involutive, Matrix.one_apply, eq_comm]
  · intro z hz; simp [hz]


lemma bitFlip_conjTranspose (n : ℕ) : conjTranspose (bitFlip n) = bitFlip n := by
  ext x y
  have h : x = flipState y ↔ y = flipState x := by
    constructor
    · intro h; rw [h, flipState_involutive]
    · intro h; rw [h, flipState_involutive]
  simp only [Matrix.conjTranspose_apply, bitFlip]
  simp only [h]
  split_ifs <;> simp


lemma bitFlip_isHerm (n : ℕ) : IsHerm (bitFlip n) :=
  bitFlip_conjTranspose n

lemma bitFlip_sq_one (n : ℕ) : bitFlip n * bitFlip n = 1 :=
  bitFlip_mul_self n

/-! ## Ambient space `sc` (skew, commutes with `F`, block-traceless) -/

/-- Skew-Hermitian operators on `n` qubits (real form `u(2^n)`). -/
def SkewHermOp (n : ℕ) : Submodule ℝ (Op n) where
  carrier := {A | IsSkewHerm A}
  zero_mem' := by simp [IsSkewHerm]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, IsSkewHerm, conjTranspose_add] at ha hb ⊢
    rw [ha, hb, neg_add]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, IsSkewHerm, conjTranspose_smul] at ha ⊢
    rw [star_trivial, ha, smul_neg]

lemma mem_skewHermOp {n : ℕ} {A : Op n} :
    A ∈ SkewHermOp n ↔ IsSkewHerm A :=
  Iff.rfl

/-- Operators commuting with the global bit flip. -/
def CommuteBitFlip (n : ℕ) : Submodule ℝ (Op n) where
  carrier := {A | A * bitFlip n = bitFlip n * A}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [add_mul, mul_add, ha, hb]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [Matrix.smul_mul, Matrix.mul_smul, ha]

lemma mem_commuteBitFlip {n : ℕ} {A : Op n} :
    A ∈ CommuteBitFlip n ↔ A * bitFlip n = bitFlip n * A :=
  Iff.rfl

/-- Global-traceless operators. -/
def TracelessOp (n : ℕ) : Submodule ℝ (Op n) where
  carrier := {A | Matrix.trace A = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [Matrix.trace_add, ha, hb, add_zero]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [Matrix.trace_smul, ha, smul_zero]

lemma mem_tracelessOp {n : ℕ} {A : Op n} :
    A ∈ TracelessOp n ↔ Matrix.trace A = 0 :=
  Iff.rfl

/-- Operators whose trace against `F` also vanishes.
Together with `TracelessOp` this is exactly block-tracelessness:
`tr (A P_±) = (tr A ± tr (A F)) / 2`. -/
def TracelessFlip (n : ℕ) : Submodule ℝ (Op n) where
  carrier := {A | Matrix.trace (A * bitFlip n) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [add_mul, Matrix.trace_add, ha, hb, add_zero]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [Matrix.smul_mul, Matrix.trace_smul, ha, smul_zero]

lemma mem_tracelessFlip {n : ℕ} {A : Op n} :
    A ∈ TracelessFlip n ↔ Matrix.trace (A * bitFlip n) = 0 :=
  Iff.rfl

/-- The ambient space `sc`: skew-Hermitian, commutes with `F`, block-traceless.
Paper eq. (16) identifies the multi-angle algebra with `su(2^{n-1}) ⊕ su(2^{n-1})`,
a real form of this space. -/
def scSpace (n : ℕ) : Submodule ℝ (Op n) :=
  SkewHermOp n ⊓ CommuteBitFlip n ⊓ TracelessOp n ⊓ TracelessFlip n

lemma mem_scSpace {n : ℕ} {A : Op n} :
    A ∈ scSpace n ↔
      IsSkewHerm A ∧ A * bitFlip n = bitFlip n * A ∧
        Matrix.trace A = 0 ∧ Matrix.trace (A * bitFlip n) = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact mem_skewHermOp.mp h.1.1.1
    · exact mem_commuteBitFlip.mp h.1.1.2
    · exact mem_tracelessOp.mp h.1.2
    · exact mem_tracelessFlip.mp h.2
  · intro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact mem_skewHermOp.mpr h1
    · exact mem_commuteBitFlip.mpr h2
    · exact mem_tracelessOp.mpr h3
    · exact mem_tracelessFlip.mpr h4

/-! ## Lie closure as an intersection of Lie subspaces -/

/-- A real subspace closed under commutator. -/
def IsLieSub (n : ℕ) (L : Submodule ℝ (Op n)) : Prop :=
  ∀ A B : Op n, A ∈ L → B ∈ L → comm A B ∈ L

/-- Real Lie algebra generated by `S`: smallest real subspace containing `S`
and closed under commutator. -/
def lieClosure {n : ℕ} (S : Set (Op n)) : Submodule ℝ (Op n) :=
  sInf {L : Submodule ℝ (Op n) | S ⊆ L ∧ IsLieSub n L}

lemma subset_lieClosure {n : ℕ} {S : Set (Op n)} : S ⊆ lieClosure S := by
  intro A hA
  apply Submodule.mem_sInf.mpr
  intro L hL
  exact hL.1 hA

lemma lieClosure_le {n : ℕ} {S : Set (Op n)} {L : Submodule ℝ (Op n)}
    (hS : S ⊆ L) (hL : IsLieSub n L) : lieClosure S ≤ L := by
  apply sInf_le
  exact ⟨hS, hL⟩

lemma lieClosure_comm {n : ℕ} {S : Set (Op n)} {A B : Op n}
    (hA : A ∈ lieClosure S) (hB : B ∈ lieClosure S) :
    comm A B ∈ lieClosure S := by
  apply Submodule.mem_sInf.mpr
  intro L hL
  exact hL.2 A B (lieClosure_le hL.1 hL.2 hA) (lieClosure_le hL.1 hL.2 hB)

lemma isLieSub_lieClosure {n : ℕ} (S : Set (Op n)) : IsLieSub n (lieClosure S) :=
  fun _ _ => lieClosure_comm

lemma lieClosure_mono {n : ℕ} {S T : Set (Op n)} (h : S ⊆ T) :
    lieClosure S ≤ lieClosure T := by
  apply lieClosure_le
  · exact h.trans subset_lieClosure
  · exact isLieSub_lieClosure T

/-! ## Generators and the multi-angle algebra -/

/-- Scalar `Complex.I` as an operator coefficient. -/
def iMul {n : ℕ} (A : Op n) : Op n := Complex.I • A

/-- Standard QAOA generators `i H_X`, `i H_ZZ`. -/
def stdGens {n : ℕ} (HX HZZ : Op n) : Set (Op n) :=
  {iMul HX, iMul HZZ}

/-- Multi-angle generators `{ i X_v } ∪ { i Z_u Z_v }` for a graph with edge set `E`. -/
def maGens {n : ℕ} (E : Finset (Fin n × Fin n)) : Set (Op n) :=
  (Set.range fun v : Fin n => iMul (Xv v)) ∪
    {A | ∃ e ∈ E, A = iMul (ZZ e.1 e.2)}

/-- The multi-angle algebra `g_ma = Lie_ℝ ( { i X_v } ∪ { i Z_u Z_v } )`. -/
def gMa {n : ℕ} (E : Finset (Fin n × Fin n)) : Submodule ℝ (Op n) :=
  lieClosure (maGens E)

/-- The standard algebra `g_std = Lie_ℝ { i H_X, i H_ZZ }`. -/
def gStd {n : ℕ} (HX HZZ : Op n) : Submodule ℝ (Op n) :=
  lieClosure (stdGens HX HZZ)

lemma mem_stdGens_iff {n : ℕ} {HX HZZ A : Op n} :
    A ∈ stdGens HX HZZ ↔ A = iMul HX ∨ A = iMul HZZ := by
  simp [stdGens]

/-! ## Generator membership in `sc` -/

lemma iMul_skew {n : ℕ} {A : Op n} (hA : IsHerm A) : IsSkewHerm (iMul A) := by
  change conjTranspose (Complex.I • A) = -(Complex.I • A)
  rw [conjTranspose_smul, hA]
  -- goal: star I • A = -(I • A)
  have hI : star (Complex.I : ℂ) = -Complex.I := by
    simp only [Complex.star_def, Complex.conj_I]
  rw [hI, neg_smul]


/-- The commutant of any matrix is closed under Lie brackets. -/
lemma lieClosure_commutes {n : ℕ} (S : Set (Op n)) (P : Op n)
    (hS : ∀ A ∈ S, A * P = P * A) :
    ∀ A ∈ lieClosure S, A * P = P * A := by
  let L : Submodule ℝ (Op n) :=
    { carrier := {A | A * P = P * A}
      zero_mem' := by simp
      add_mem' := by intro A B hA hB; simp only [Set.mem_setOf_eq] at *; rw [add_mul, mul_add, hA, hB]
      smul_mem' := by intro r A hA; simp only [Set.mem_setOf_eq] at *; rw [Matrix.smul_mul, Matrix.mul_smul, hA] }
  apply lieClosure_le (L := L) hS
  intro A B hA hB
  change (A*B-B*A)*P=P*(A*B-B*A)
  change A*P=P*A at hA
  change B*P=P*B at hB
  rw [sub_mul, mul_sub]
  have hAB : A*B*P = P*(A*B) := by rw [mul_assoc, hB, ← mul_assoc, hA, mul_assoc]
  have hBA : B*A*P = P*(B*A) := by rw [mul_assoc, hA, ← mul_assoc, hB, mul_assoc]
  rw [hAB, hBA]

/-- The standard algebra preserves every operator commuting with both generators. -/
theorem gStd_commutes {n : ℕ} (HX HZZ P : Op n)
    (hX : HX*P=P*HX) (hZZ : HZZ*P=P*HZZ) :
    ∀ A ∈ gStd HX HZZ, A*P=P*A := by
  apply lieClosure_commutes
  intro A hA
  rcases mem_stdGens_iff.mp hA with rfl | rfl
  · simp only [iMul, Matrix.smul_mul, Matrix.mul_smul, hX]
  · simp only [iMul, Matrix.smul_mul, Matrix.mul_smul, hZZ]

/-- Real dimension of the skew-Hermitian operator space, without an assumed dimension formula. -/
lemma skewHermOp_finrank (n : ℕ) : Module.finrank ℝ (SkewHermOp n) = 2^(2*n) := by
  have heq : SkewHermOp n = skewAdjoint.submodule ℝ (Op n) := by
    ext A; rfl
  rw [heq]
  calc
    _ = (Fintype.card (QubitBasis n))^2 := skewAdjoint_finrank (QubitBasis n)
    _ = (2^n)^2 := by simp [QubitBasis]
    _ = 2^(2*n) := by rw [← pow_mul, Nat.mul_comm n 2]

end Paper13

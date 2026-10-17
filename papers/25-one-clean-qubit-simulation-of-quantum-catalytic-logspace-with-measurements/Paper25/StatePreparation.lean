import Paper25.OneCleanQubit
import Paper25.Liouville
import Paper25.SourceBias

/-!
# Bell-pair and basis-state preparation for Sections 2 and 4.3

Preparations are products of explicit Hadamard, Pauli and CNOT matrices. Their
computational-basis columns, including the sign `XZX = -Z`, are proved below.
-/

noncomputable section
open scoped ComplexConjugate
open Matrix
namespace Paper25.StatePreparation

abbrev Bit := Fin 2
abbrev Bits (s : ℕ) := Fin s → Bit

instance bitsDecidableEq (s : ℕ) : DecidableEq (Bits s) := Fintype.decidablePiFintype
abbrev Op (s : ℕ) := Matrix (Bits s) (Bits s) ℂ

def zeroBits (s : ℕ) : Bits s := fun _ => 0

def bitSumUnit : Bit ≃ (Unit ⊕ Unit) where
  toFun b := if b = 0 then Sum.inl () else Sum.inr ()
  invFun b := match b with | Sum.inl _ => 0 | Sum.inr _ => 1
  left_inv b := by fin_cases b <;> simp
  right_inv b := by rcases b with ⟨⟩ | ⟨⟩ <;> simp

lemma unitary_reindex {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (U : Matrix b b ℂ)
    (hU : OneCleanQubit.Unitary U) : OneCleanQubit.Unitary (U.submatrix e e) := by
  constructor <;> simp only [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  · rw [hU.1, Matrix.submatrix_one_equiv]
  · rw [hU.2, Matrix.submatrix_one_equiv]

lemma unitary_tensor {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (U : Matrix a a ℂ) (V : Matrix b b ℂ)
    (hU : OneCleanQubit.Unitary U) (hV : OneCleanQubit.Unitary V) :
    OneCleanQubit.Unitary (Matrix.kronecker U V) := by
  constructor <;> simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  · rw [hU.1, hV.1, Matrix.one_kronecker_one]
  · rw [hU.2, hV.2, Matrix.one_kronecker_one]

lemma unitary_one {a : Type*} [Fintype a] [DecidableEq a] :
    OneCleanQubit.Unitary (1 : Matrix a a ℂ) := by constructor <;> simp

/-- The ordinary one-qubit Hadamard, reusing the checked normalized probe gate. -/
def H2 : Matrix Bit Bit ℂ :=
  (OneCleanQubit.hadamard : OneCleanQubit.ProbeMatrix Unit).submatrix bitSumUnit bitSumUnit

lemma H2_unitary : OneCleanQubit.Unitary H2 :=
  unitary_reindex _ _ OneCleanQubit.hadamard_unitary

lemma H2_apply (i j : Bit) :
    H2 i j = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (if i = 1 ∧ j = 1 then -1 else 1) := by
  fin_cases i <;> fin_cases j <;>
    simp [H2, bitSumUnit, OneCleanQubit.hadamard, Matrix.submatrix_apply,
      Matrix.fromBlocks, Matrix.smul_apply]

lemma H2_zero_column (i : Bit) : H2 i 0 = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
  simp [H2_apply]

/-- Pauli gates, with the exact source convention. -/
def X2 : Matrix Bit Bit ℂ := Paper25.pauliX

def Z2 : Matrix Bit Bit ℂ := Paper25.pauliZ

lemma X2_unitary : OneCleanQubit.Unitary X2 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [X2, pauliX, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Matrix.one_apply]

lemma Z2_unitary : OneCleanQubit.Unitary Z2 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Z2, pauliZ, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Matrix.one_apply]

lemma XZX_signed : X2 * Z2 * X2 = Matrix.diagonal (fun b : Bit => if b = 1 then 1 else -1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [X2, Z2, pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal]

/-- Controlled bit-flip on an ordered pair: first bit is the control. -/
def CNOT : Matrix (Bit × Bit) (Bit × Bit) ℂ :=
  fun i j => if i.1 = j.1 ∧ i.2 = (if j.1 = 0 then j.2 else 1 - j.2) then 1 else 0

lemma CNOT_unitary : OneCleanQubit.Unitary CNOT := by
  constructor <;> ext ⟨a,b⟩ ⟨c,d⟩ <;>
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      norm_num [CNOT, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply]

/-- The chronological sequence H on the first qubit, followed by CNOT. -/
def bellPair : Matrix (Bit × Bit) (Bit × Bit) ℂ :=
  CNOT * Matrix.kronecker H2 (1 : Matrix Bit Bit ℂ)

lemma bellPair_unitary : OneCleanQubit.Unitary bellPair :=
  OneCleanQubit.unitary_mul CNOT_unitary (unitary_tensor H2 1 H2_unitary unitary_one)

lemma bellPair_column (a b : Bit) :
    bellPair (a,b) (0,0) = if a = b then (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [bellPair, CNOT, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.kronecker_apply, H2_apply, Matrix.one_apply]

/-- Split the first physical qubit from a bit string. -/
def splitBits (s : ℕ) : Bits (s + 1) ≃ (Bit × Bits s) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by rcases p with ⟨i,f⟩; rfl

@[simp] lemma splitBits_zero (s : ℕ) : splitBits s (zeroBits (s+1)) = (0, zeroBits s) := rfl

@[simp] lemma splitBits_symm_zero (s : ℕ) :
    (splitBits s).symm (0, zeroBits s) = zeroBits (s+1) := by
  apply (splitBits s).injective
  simp

lemma bits_eq_iff (s : ℕ) (x y : Bits (s+1)) :
    x = y ↔ x 0 = y 0 ∧ (fun i : Fin s => x i.succ) = (fun i : Fin s => y i.succ) := by
  constructor
  · intro h; subst y; exact ⟨rfl,rfl⟩
  · intro h
    apply (splitBits s).injective
    exact Prod.ext h.1 h.2

/-- A wire shuffle placing the first work-copy Bell pair before the remaining pairs. -/
def pairShuffle (s : ℕ) :
    (Bits (s+1) × Bits (s+1)) ≃ ((Bit × Bit) × (Bits s × Bits s)) where
  toFun p := ((p.1 0,p.2 0), (fun i => p.1 i.succ, fun i => p.2 i.succ))
  invFun p := (Fin.cons p.1.1 p.2.1, Fin.cons p.1.2 p.2.2)
  left_inv p := by
    apply Prod.ext <;> funext i <;> refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by rcases p with ⟨⟨a,b⟩,x,y⟩; rfl

/-- Exactly s two-qubit Bell preparations, with a computational wire shuffle. -/
def bellPrep : (s : ℕ) → Matrix (Bits s × Bits s) (Bits s × Bits s) ℂ
  | 0 => 1
  | s+1 => (Matrix.kronecker bellPair (bellPrep s)).submatrix (pairShuffle s) (pairShuffle s)

lemma bellPrep_unitary (s : ℕ) : OneCleanQubit.Unitary (bellPrep s) := by
  induction s with
  | zero => exact unitary_one
  | succ s ih => exact unitary_reindex _ _ (unitary_tensor _ _ bellPair_unitary ih)

lemma bellPrep_column (s : ℕ) (x y : Bits s) :
    bellPrep s (x,y) (zeroBits s,zeroBits s) =
      if x = y then ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ s) else 0 := by
  induction s with
  | zero =>
    have h : x = y := Subsingleton.elim _ _
    have hx : x = zeroBits 0 := Subsingleton.elim _ _
    subst y; subst x
    simp [bellPrep, Matrix.one_apply]
  | succ s ih =>
    change bellPair (x 0,y 0) (0,0) *
      bellPrep s ((fun i => x i.succ),(fun i => y i.succ)) (zeroBits s,zeroBits s) = _
    rw [bellPair_column, ih]
    simp only [bits_eq_iff s]
    by_cases h0 : x 0 = y 0 <;>
      by_cases ht : (fun i : Fin s => x i.succ) = (fun i : Fin s => y i.succ) <;>
        simp [h0,ht,pow_succ,mul_comm]

lemma sqrt_two_pow (s : ℕ) : Real.sqrt ((2 : ℝ)^s) = Real.sqrt 2 ^ s := by
  induction s with
  | zero => simp
  | succ s ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

lemma bell_amplitude_normalization (s : ℕ) :
    ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ s) = (Real.sqrt (Fintype.card (Bits s)) : ℂ)⁻¹ := by
  simp only [Bits, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  rw [sqrt_two_pow]
  push_cast
  simp [inv_pow]

abbrev WorkSpace (s : ℕ) := Bit × Bits s

def zeroWork (s : ℕ) : WorkSpace s := (0,zeroBits s)

def workPairBasis (s : ℕ) :
    (WorkSpace s × WorkSpace s) ≃ (Bits (s+1) × Bits (s+1)) :=
  (splitBits s).symm.prodCongr (splitBits s).symm

def firstWorkBit (s : ℕ) :
    (WorkSpace s × WorkSpace s) ≃ (Bit × (Bits s × WorkSpace s)) :=
  Equiv.prodAssoc Bit (Bits s) (WorkSpace s)

/-- Exact X-Z-X on the first output half, including the minus sign relative to Z. -/
def signGate (s : ℕ) : Matrix (WorkSpace s × WorkSpace s) (WorkSpace s × WorkSpace s) ℂ :=
  (Matrix.kronecker (X2 * Z2 * X2) (1 : Matrix (Bits s × WorkSpace s) _ ℂ)).submatrix
    (firstWorkBit s) (firstWorkBit s)

lemma signGate_unitary (s : ℕ) : OneCleanQubit.Unitary (signGate s) :=
  unitary_reindex _ _ (unitary_tensor _ _
    (OneCleanQubit.unitary_mul (OneCleanQubit.unitary_mul X2_unitary Z2_unitary) X2_unitary)
    unitary_one)

lemma signGate_diagonal (s : ℕ) : signGate s =
    Matrix.diagonal (fun p => SourceBias.sign p.1.1) := by
  rw [signGate, XZX_signed]
  ext ⟨⟨a,x⟩,y⟩ ⟨⟨b,u⟩,v⟩
  simp only [Matrix.submatrix_apply, Matrix.kronecker_apply, firstWorkBit,
    Equiv.prodAssoc_apply, Matrix.diagonal_apply, Matrix.one_apply, Prod.mk.injEq,
    SourceBias.sign]
  by_cases hab : a = b <;> by_cases hxu : x = u <;> by_cases hyv : y = v <;>
    simp [hab,hxu,hyv]

/-- Bell preparation followed by the actual signed Pauli sequence on the output half. -/
def signedBellPrep (s : ℕ) :
    Matrix (WorkSpace s × WorkSpace s) (WorkSpace s × WorkSpace s) ℂ :=
  signGate s * (bellPrep (s+1)).submatrix (workPairBasis s) (workPairBasis s)

lemma signedBellPrep_unitary (s : ℕ) : OneCleanQubit.Unitary (signedBellPrep s) :=
  OneCleanQubit.unitary_mul (signGate_unitary s)
    (unitary_reindex _ _ (bellPrep_unitary (s+1)))

/-- Section 2's signed vector is prepared as an actual unitary column. -/
theorem signedBellPrep_column (s : ℕ) (p : WorkSpace s × WorkSpace s) :
    signedBellPrep s p (zeroWork s,zeroWork s) =
      (SourceBias.zVector (α := Bits s)) p := by
  rw [signedBellPrep, signGate_diagonal, Matrix.diagonal_mul]
  change SourceBias.sign p.1.1 *
    bellPrep (s+1) ((splitBits s).symm p.1,(splitBits s).symm p.2)
      ((splitBits s).symm (0,zeroBits s),(splitBits s).symm (0,zeroBits s)) = _
  rw [splitBits_symm_zero, bellPrep_column, bell_amplitude_normalization]
  have heq : (splitBits s).symm p.1 = (splitBits s).symm p.2 ↔ p.1 = p.2 :=
    (splitBits s).symm.injective.eq_iff
  have hcard : Fintype.card (Bits (s+1)) = Fintype.card (SourceBias.Work (Bits s)) :=
    Fintype.card_congr (splitBits s)
  simp only [heq,hcard]
  simp only [SourceBias.zVector, SourceBias.vecOp, SourceBias.observable,
    Matrix.diagonal_apply]
  by_cases h : p.1 = p.2 <;> simp [h,div_eq_mul_inv]

lemma X2_zero_column (b : Bit) : X2 b 0 = if b = 1 then 1 else 0 := by
  fin_cases b <;> norm_num [X2,pauliX]

lemma basisFlip_column (a b : Bit) :
    (if b = 0 then (1 : Matrix Bit Bit ℂ) else X2) a 0 = if a = b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> norm_num [X2,pauliX,Matrix.one_apply]

/-- Basis preparation is a recursive tensor of identity or Pauli-X gates. -/
def basisPrep : (s : ℕ) → Bits s → Op s
  | 0, _ => 1
  | s+1,t => (Matrix.kronecker (if t 0 = 0 then 1 else X2)
      (basisPrep s (fun i => t i.succ))).submatrix (splitBits s) (splitBits s)

lemma basisPrep_unitary (s : ℕ) (t : Bits s) : OneCleanQubit.Unitary (basisPrep s t) := by
  induction s with
  | zero => exact unitary_one
  | succ s ih =>
    apply unitary_reindex
    apply unitary_tensor
    · split_ifs
      · exact unitary_one
      · exact X2_unitary
    · exact ih _

lemma basisPrep_column (s : ℕ) (t x : Bits s) :
    basisPrep s t x (zeroBits s) = if x = t then 1 else 0 := by
  induction s with
  | zero =>
    have hx : x = zeroBits 0 := Subsingleton.elim _ _
    have ht : t = zeroBits 0 := Subsingleton.elim _ _
    subst x; subst t
    simp [basisPrep,Matrix.one_apply]
  | succ s ih =>
    change (if t 0 = 0 then (1 : Matrix Bit Bit ℂ) else X2) (x 0) 0 *
      basisPrep s (fun i => t i.succ) (fun i => x i.succ) (zeroBits s) = _
    rw [basisFlip_column, ih]
    simp only [bits_eq_iff s]
    by_cases h0 : x 0 = t 0 <;>
      by_cases ht : (fun i : Fin s => x i.succ) = (fun i : Fin s => t i.succ) <;> simp [h0,ht]

abbrev Small (ell s r : ℕ) := Bit × (Bits ell × ((WorkSpace s × WorkSpace s) × Bits r))

def smallZero (ell s r : ℕ) : Small ell s r :=
  (0,(zeroBits ell,((zeroWork s,zeroWork s),zeroBits r)))

/-- The actual F from equation (S4.Ex12): flip h, set the clock, prepare z, leave
all block/phase/rotation ancillas at zero. -/
def F (ell s r : ℕ) (t : Bits ell) : Matrix (Small ell s r) (Small ell s r) ℂ :=
  Matrix.kronecker X2 (Matrix.kronecker (basisPrep ell t)
    (Matrix.kronecker (signedBellPrep s) (1 : Op r)))

lemma F_unitary (ell s r : ℕ) (t : Bits ell) : OneCleanQubit.Unitary (F ell s r t) :=
  unitary_tensor _ _ X2_unitary (unitary_tensor _ _ (basisPrep_unitary ell t)
    (unitary_tensor (signedBellPrep s) (1 : Op r) (signedBellPrep_unitary s) unitary_one))

/-- Exact target column, retaining the signed z-vector and every zero ancillary coordinate. -/
theorem F_column (ell s r : ℕ) (t : Bits ell) (p : Small ell s r) :
    F ell s r t p (smallZero ell s r) =
      (if p.1 = 1 then 1 else 0) * (if p.2.1 = t then 1 else 0) *
        (SourceBias.zVector (α := Bits s)) p.2.2.1 *
          (if p.2.2.2 = zeroBits r then 1 else 0) := by
  rcases p with ⟨h,clock,work,anc⟩
  simp only [F,smallZero,Matrix.kronecker,Matrix.kroneckerMap_apply,X2_zero_column,basisPrep_column,
    signedBellPrep_column,Matrix.one_apply]
  ring

/-- A chronological list of explicit gates, evaluated by left action. -/
def sequenceMatrix {a : Type*} [Fintype a] [DecidableEq a] :
    List (Matrix a a ℂ) → Matrix a a ℂ
  | [] => 1
  | U :: Us => sequenceMatrix Us * U

lemma sequenceMatrix_append {a : Type*} [Fintype a] [DecidableEq a]
    (Us Vs : List (Matrix a a ℂ)) :
    sequenceMatrix (Us ++ Vs) = sequenceMatrix Vs * sequenceMatrix Us := by
  induction Us with
  | nil => simp [sequenceMatrix]
  | cons U Us ih => simp only [List.cons_append,sequenceMatrix,ih,mul_assoc]

lemma sequenceMatrix_reindex {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (Us : List (Matrix b b ℂ)) :
    sequenceMatrix (Us.map (fun U => U.submatrix e e)) =
      (sequenceMatrix Us).submatrix e e := by
  induction Us with
  | nil => simp [sequenceMatrix,Matrix.submatrix_one_equiv]
  | cons U Us ih => simp only [List.map_cons,sequenceMatrix,ih,Matrix.submatrix_mul_equiv]

lemma sequenceMatrix_tensorLeft {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (Us : List (Matrix a a ℂ)) :
    sequenceMatrix (Us.map (fun U => Matrix.kronecker U (1 : Matrix b b ℂ))) =
      Matrix.kronecker (sequenceMatrix Us) (1 : Matrix b b ℂ) := by
  induction Us with
  | nil => simp [sequenceMatrix,Matrix.one_kronecker_one]
  | cons U Us ih =>
    simp only [List.map_cons,sequenceMatrix]
    rw [ih]
    simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,one_mul]

lemma sequenceMatrix_tensorRight {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (Vs : List (Matrix b b ℂ)) :
    sequenceMatrix (Vs.map (fun V => Matrix.kronecker (1 : Matrix a a ℂ) V)) =
      Matrix.kronecker (1 : Matrix a a ℂ) (sequenceMatrix Vs) := by
  induction Vs with
  | nil => simp [sequenceMatrix,Matrix.one_kronecker_one]
  | cons V Vs ih =>
    simp only [List.map_cons,sequenceMatrix]
    rw [ih]
    simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,one_mul]

/-- Execute disjoint gate lists on the left and right registers. -/
def tensorSequence {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b]
    (Us : List (Matrix a a ℂ)) (Vs : List (Matrix b b ℂ)) :
    List (Matrix (a × b) (a × b) ℂ) :=
  Us.map (fun U => Matrix.kronecker U (1 : Matrix b b ℂ)) ++
    Vs.map (fun V => Matrix.kronecker (1 : Matrix a a ℂ) V)

lemma tensorSequence_matrix {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b]
    (Us : List (Matrix a a ℂ)) (Vs : List (Matrix b b ℂ)) :
    sequenceMatrix (tensorSequence Us Vs) =
      Matrix.kronecker (sequenceMatrix Us) (sequenceMatrix Vs) := by
  rw [tensorSequence,sequenceMatrix_append,sequenceMatrix_tensorLeft,sequenceMatrix_tensorRight]
  simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,one_mul,mul_one]

@[simp] lemma tensorSequence_length {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b]
    (Us : List (Matrix a a ℂ)) (Vs : List (Matrix b b ℂ)) :
    (tensorSequence Us Vs).length = Us.length + Vs.length := by simp [tensorSequence]

/-- The two primitive gates of each Bell pair. -/
def bellPairSequence : List (Matrix (Bit × Bit) (Bit × Bit) ℂ) :=
  [Matrix.kronecker H2 (1 : Matrix Bit Bit ℂ),CNOT]

lemma bellPairSequence_matrix : sequenceMatrix bellPairSequence = bellPair := by
  simp [bellPairSequence,sequenceMatrix,bellPair]

/-- An explicit list consisting only of H and CNOT with identity extensions and
specified physical wire regroupings. -/
def bellSequence : (s : ℕ) → List (Matrix (Bits s × Bits s) (Bits s × Bits s) ℂ)
  | 0 => []
  | s+1 => (tensorSequence bellPairSequence (bellSequence s)).map
      (fun U => U.submatrix (pairShuffle s) (pairShuffle s))

lemma bellSequence_matrix (s : ℕ) : sequenceMatrix (bellSequence s) = bellPrep s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [bellSequence,sequenceMatrix_reindex,tensorSequence_matrix,bellPairSequence_matrix,ih]
    rfl

lemma bellSequence_length (s : ℕ) : (bellSequence s).length = 2*s := by
  induction s with
  | zero => rfl
  | succ s ih => simp [bellSequence,bellPairSequence,ih]; omega

/-- The three literal Pauli gates X, Z, X on the output half. -/
def signSequence (s : ℕ) :
    List (Matrix (WorkSpace s × WorkSpace s) (WorkSpace s × WorkSpace s) ℂ) :=
  (tensorSequence [X2,Z2,X2] ([] : List (Matrix (Bits s × WorkSpace s) _ ℂ))).map
    (fun U => U.submatrix (firstWorkBit s) (firstWorkBit s))

lemma signSequence_matrix (s : ℕ) : sequenceMatrix (signSequence s) = signGate s := by
  rw [signSequence,sequenceMatrix_reindex,tensorSequence_matrix]
  simp [sequenceMatrix,signGate]

@[simp] lemma signSequence_length (s : ℕ) : (signSequence s).length = 3 := by
  simp [signSequence]

def signedBellSequence (s : ℕ) :
    List (Matrix (WorkSpace s × WorkSpace s) (WorkSpace s × WorkSpace s) ℂ) :=
  (bellSequence (s+1)).map (fun U => U.submatrix (workPairBasis s) (workPairBasis s)) ++
    signSequence s

lemma signedBellSequence_matrix (s : ℕ) :
    sequenceMatrix (signedBellSequence s) = signedBellPrep s := by
  rw [signedBellSequence,sequenceMatrix_append,signSequence_matrix,
    sequenceMatrix_reindex,bellSequence_matrix]
  rfl

lemma signedBellSequence_length (s : ℕ) : (signedBellSequence s).length = 2*s+5 := by
  simp [signedBellSequence,bellSequence_length]
  omega

/-- Basis-state preparation as a literal list of only X gates. -/
def basisSequence : (s : ℕ) → Bits s → List (Op s)
  | 0,_ => []
  | s+1,t => (tensorSequence (if t 0 = 0 then [] else [X2])
      (basisSequence s (fun i => t i.succ))).map
        (fun U => U.submatrix (splitBits s) (splitBits s))

lemma basisSequence_matrix (s : ℕ) (t : Bits s) :
    sequenceMatrix (basisSequence s t) = basisPrep s t := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [basisSequence,sequenceMatrix_reindex,tensorSequence_matrix,ih]
    by_cases h : t 0 = 0 <;> simp [h,sequenceMatrix,basisPrep]

lemma basisSequence_length (s : ℕ) (t : Bits s) : (basisSequence s t).length ≤ s := by
  induction s with
  | zero => simp [basisSequence]
  | succ s ih =>
    simp only [basisSequence,List.length_map,tensorSequence_length]
    split_ifs <;> simp only [List.length_nil,List.length_singleton]
    · simpa only [zero_add] using le_trans (ih (fun i => t i.succ)) (Nat.le_succ s)
    · have h := ih (fun i => t i.succ); omega

/-- A complete concrete primitive sequence implementing F. -/
def FSequence (ell s r : ℕ) (t : Bits ell) :
    List (Matrix (Small ell s r) (Small ell s r) ℂ) :=
  tensorSequence [X2] (tensorSequence (basisSequence ell t)
    (tensorSequence (signedBellSequence s) ([] : List (Op r))))

lemma FSequence_matrix (ell s r : ℕ) (t : Bits ell) :
    sequenceMatrix (FSequence ell s r t) = F ell s r t := by
  simp only [FSequence,tensorSequence_matrix,basisSequence_matrix,
    signedBellSequence_matrix,sequenceMatrix,mul_one,one_mul]
  rfl

/-- F uses one selector flip, at most ell clock flips, 2(s+1) Bell gates,
and the three output Pauli gates. All remaining ancillas are untouched. -/
theorem FSequence_length (ell s r : ℕ) (t : Bits ell) :
    (FSequence ell s r t).length ≤ ell + 2*s + 6 := by
  simp only [FSequence,tensorSequence_length,List.length_singleton,List.length_nil,
    signedBellSequence_length]
  have h := basisSequence_length ell t
  omega

/-- Every matrix occurring in the explicit list is a legal unitary gate. -/
def sequenceLegal {a : Type*} [Fintype a] [DecidableEq a]
    (Us : List (Matrix a a ℂ)) : Prop := ∀ U ∈ Us, OneCleanQubit.Unitary U

lemma sequenceLegal_nil {a : Type*} [Fintype a] [DecidableEq a] :
    sequenceLegal ([] : List (Matrix a a ℂ)) := by intro U h; cases h

lemma sequenceLegal_reindex {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (Us : List (Matrix b b ℂ))
    (hUs : sequenceLegal Us) : sequenceLegal (Us.map (fun U => U.submatrix e e)) := by
  intro V hV
  obtain ⟨U,hU,rfl⟩ := List.mem_map.mp hV
  exact unitary_reindex e U (hUs U hU)

lemma sequenceLegal_append {a : Type*} [Fintype a] [DecidableEq a]
    (Us Vs : List (Matrix a a ℂ)) (hUs : sequenceLegal Us) (hVs : sequenceLegal Vs) :
    sequenceLegal (Us ++ Vs) := by
  intro U hU
  rcases List.mem_append.mp hU with h | h
  · exact hUs U h
  · exact hVs U h

lemma sequenceLegal_tensor {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b]
    (Us : List (Matrix a a ℂ)) (Vs : List (Matrix b b ℂ))
    (hUs : sequenceLegal Us) (hVs : sequenceLegal Vs) :
    sequenceLegal (tensorSequence Us Vs) := by
  apply sequenceLegal_append
  · intro W hW
    obtain ⟨U,hU,rfl⟩ := List.mem_map.mp hW
    exact unitary_tensor _ _ (hUs U hU) unitary_one
  · intro W hW
    obtain ⟨V,hV,rfl⟩ := List.mem_map.mp hW
    exact unitary_tensor _ _ unitary_one (hVs V hV)

lemma bellPairSequence_legal : sequenceLegal bellPairSequence := by
  intro U hU
  simp only [bellPairSequence,List.mem_cons,List.not_mem_nil,or_false] at hU
  rcases hU with rfl | rfl
  · exact unitary_tensor _ _ H2_unitary unitary_one
  · exact CNOT_unitary

lemma bellSequence_legal (s : ℕ) : sequenceLegal (bellSequence s) := by
  induction s with
  | zero => exact sequenceLegal_nil
  | succ s ih =>
    apply sequenceLegal_reindex
    exact sequenceLegal_tensor _ _ bellPairSequence_legal ih

lemma signSequence_legal (s : ℕ) : sequenceLegal (signSequence s) := by
  apply sequenceLegal_reindex
  apply sequenceLegal_tensor
  · intro U hU
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hU
    rcases hU with rfl | rfl | rfl
    · exact X2_unitary
    · exact Z2_unitary
    · exact X2_unitary
  · exact sequenceLegal_nil

lemma signedBellSequence_legal (s : ℕ) : sequenceLegal (signedBellSequence s) :=
  sequenceLegal_append _ _ (sequenceLegal_reindex _ _ (bellSequence_legal (s+1)))
    (signSequence_legal s)

lemma basisSequence_legal (s : ℕ) (t : Bits s) : sequenceLegal (basisSequence s t) := by
  induction s with
  | zero => exact sequenceLegal_nil
  | succ s ih =>
    apply sequenceLegal_reindex
    apply sequenceLegal_tensor
    · split_ifs
      · exact sequenceLegal_nil
      · intro U hU
        simp only [List.mem_singleton] at hU
        subst U
        exact X2_unitary
    · exact ih _

lemma FSequence_legal (ell s r : ℕ) (t : Bits ell) : sequenceLegal (FSequence ell s r t) := by
  unfold FSequence
  apply sequenceLegal_tensor
  · intro U hU
    simp only [List.mem_singleton] at hU
    subst U
    exact X2_unitary
  · exact sequenceLegal_tensor _ _ (basisSequence_legal ell t)
      (sequenceLegal_tensor _ _ (signedBellSequence_legal s) sequenceLegal_nil)

/-- A gate-list version of equation (S4.Ex12), with a concrete gate count. -/
theorem FSequence_prepares (ell s r : ℕ) (t : Bits ell) :
    sequenceLegal (FSequence ell s r t) ∧
    (FSequence ell s r t).length ≤ ell+2*s+6 ∧
    ∀ p : Small ell s r,
      sequenceMatrix (FSequence ell s r t) p (smallZero ell s r) =
        (if p.1 = 1 then 1 else 0) * (if p.2.1 = t then 1 else 0) *
          (SourceBias.zVector (α := Bits s)) p.2.2.1 *
            (if p.2.2.2 = zeroBits r then 1 else 0) := by
  refine ⟨FSequence_legal _ _ _ _,FSequence_length _ _ _ _,?_⟩
  intro p
  rw [FSequence_matrix]
  exact F_column _ _ _ _ p

end Paper25.StatePreparation

import Paper25.WalkCompilation

/-! Phase-sensitive zero-register reflections from actual H/X local lists.
No initialized workspace is added. In particular the scalar minus sign is
implemented by gates, so it remains correct when the circuit is controlled. -/
noncomputable section
open Matrix
namespace Paper25.OperationalModel.LocalCompilation

lemma hadamard_flip_hadamard {n : Type*} [Fintype n] [DecidableEq n] :
    (OneCleanQubit.hadamard : OneCleanQubit.ProbeMatrix n) * probeFlip *
      OneCleanQubit.hadamard = Matrix.fromBlocks 1 0 0 (-1) := by
  have hs : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = (1/2:ℂ) := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  unfold OneCleanQubit.hadamard probeFlip
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hs,
    Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.smul_apply, Matrix.one_apply, two_smul] <;>
    split_ifs <;> norm_num

lemma negative_probe_product {n : Type*} [Fintype n] [DecidableEq n] :
    (OneCleanQubit.hadamard : OneCleanQubit.ProbeMatrix n) * probeFlip *
      OneCleanQubit.hadamard * probeFlip * OneCleanQubit.hadamard * probeFlip *
        OneCleanQubit.hadamard * probeFlip = -1 := by
  calc
    _ = ((OneCleanQubit.hadamard * probeFlip * OneCleanQubit.hadamard) * probeFlip *
      ((OneCleanQubit.hadamard * probeFlip * OneCleanQubit.hadamard) * probeFlip) :
        OneCleanQubit.ProbeMatrix n) := by
        simp only [mul_assoc]
    _ = -1 := by
      rw [hadamard_flip_hadamard]
      simp only [probeFlip, Matrix.fromBlocks_multiply]
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [Matrix.fromBlocks, Matrix.one_apply]

def negativeCircuit {G : EffectiveGateSet} (conv : GateConvention G) (q : ℕ) :
    EffectiveCircuit G (q+1) :=
  flipCircuit conv q ++ conv.hadamardAt q ++ flipCircuit conv q ++ conv.hadamardAt q ++
    flipCircuit conv q ++ conv.hadamardAt q ++ flipCircuit conv q ++ conv.hadamardAt q

theorem negativeCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) (q : ℕ) :
    (negativeCircuit conv q).matrix = -1 := by
  simp only [negativeCircuit, EffectiveCircuit.matrix_append, flipCircuit_matrix,
    conv.hadamard_matrix, physicalHadamard, physicalFlip, Matrix.submatrix_mul_equiv]
  have h := congrArg (fun M : OneCleanQubit.ProbeMatrix (Basis q) =>
    M.submatrix (probeBasis q) (probeBasis q)) (negative_probe_product (n := Basis q))
  have hn : ((-1 : OneCleanQubit.ProbeMatrix (Basis q)).submatrix
      (probeBasis q) (probeBasis q)) = -1 := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply, (probeBasis q).injective.eq_iff]
  simpa only [mul_assoc] using h.trans hn

lemma negativeCircuit_length {G : EffectiveGateSet} (conv : GateConvention G) (q : ℕ) :
    (negativeCircuit conv q).length ≤ 4*(conv.X.length+conv.bound) := by
  simp only [negativeCircuit, List.length_append, flipCircuit, embedCircuit_length]
  have h := conv.hadamard_length q
  omega

/-- Enumerate all small-register labels, retaining identity on the all-zero
label and minus identity on the others. Only the first data bit is used by
the scalar-phase implementation; every other data bit is untouched. -/
def zeroReflectionCircuit {G : EffectiveGateSet} (conv : GateConvention G) (ell q : ℕ) :
    EffectiveCircuit G (ell+(q+1)) :=
  selectCircuit conv (fun label : Basis ell =>
    if label = (fun _ => 0) then [] else negativeCircuit conv q)

theorem zeroReflectionCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G)
    (ell q : ℕ) :
    (zeroReflectionCircuit conv ell q).matrix =
      (projectorReflection (OneCleanQubit.ancillaryProjector (n := Basis (q+1))
        (Basis ell) (fun _ => 0))).submatrix (registerBasis ell (q+1))
          (registerBasis ell (q+1)) := by
  rw [zeroReflectionCircuit, selectCircuit_matrix]
  have hb (label : Basis ell) :
      EffectiveCircuit.matrix (if label = (fun _ => 0) then [] else negativeCircuit conv q) =
        if label = (fun _ => 0) then (1 : Operator (q+1)) else -1 := by
    by_cases h : label = (fun _ => 0)
    · simp only [if_pos h, EffectiveCircuit.matrix]
    · simp only [if_neg h, negativeCircuit_matrix]
  simp_rw [hb]
  congr 1
  ext ⟨a,i⟩ ⟨b,j⟩
  by_cases ha : a = (fun _ => 0) <;> by_cases hab : a = b <;> by_cases hij : i = j <;>
    simp [ha, hab, hij,
      Paper25.selectMatrix, projectorReflection, OneCleanQubit.ancillaryProjector,
      Matrix.diagonal_apply, Matrix.one_apply, two_smul, Prod.ext_iff] <;> aesop

theorem zeroReflectionCircuit_length {G : EffectiveGateSet} (conv : GateConvention G)
    (ell q : ℕ) :
    (zeroReflectionCircuit conv ell q).length ≤
      2^ell * conv.bound^(ell+1) * (4*(conv.X.length+conv.bound)) := by
  apply selectCircuit_length
  intro label
  split_ifs
  · simp
  · exact negativeCircuit_length conv q

/-- A minus Z on the first data bit. This bit may itself be one of the
small-register bits being tested, so the catalyst need not contain any qubit. -/
def negativeZCircuit {G : EffectiveGateSet} (conv : GateConvention G) (q : ℕ) :
    EffectiveCircuit G (q+1) :=
  conv.hadamardAt q ++ flipCircuit conv q ++ conv.hadamardAt q ++ negativeCircuit conv q

theorem negativeZCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) (q : ℕ) :
    (negativeZCircuit conv q).matrix =
      Matrix.diagonal (fun x : Basis (q+1) => if x 0 = 0 then (-1:ℂ) else 1) := by
  simp only [negativeZCircuit, EffectiveCircuit.matrix_append, negativeCircuit_matrix,
    conv.hadamard_matrix, flipCircuit_matrix, physicalHadamard, physicalFlip,
    Matrix.submatrix_mul_equiv]
  rw [neg_one_mul, ← mul_assoc, hadamard_flip_hadamard]
  ext x y
  have he : x = y ↔ x 0 = y 0 ∧
      (fun i : Fin q => x i.succ) = (fun i : Fin q => y i.succ) := by
    constructor
    · intro h; subst y; exact ⟨rfl,rfl⟩
    · rintro ⟨h0,ht⟩
      funext i
      refine Fin.cases h0 (fun j => ?_) i
      exact congrFun ht j
  have hb : ∀ b : Fin 2, b = 0 ∨ b = 1 := by intro b; fin_cases b <;> simp
  rcases hb (x 0) with hx | hx <;> rcases hb (y 0) with hy | hy <;>
    simp [Matrix.submatrix_apply, probeBasis, probeTensor, OneCleanQubit.tensorBasis,
      Matrix.fromBlocks, Matrix.one_apply, Matrix.diagonal_apply, he,hx,hy] <;>
    split_ifs <;> simp_all only [neg_zero]

def zeroSmallProjector (ell q : ℕ) :
    Matrix (Basis ell × Basis (q+1)) (Basis ell × Basis (q+1)) ℂ :=
  Matrix.diagonal (fun p => if p.1 = (fun _ => 0) ∧ p.2 0 = 0 then 1 else 0)

def negativeDataCircuit {G : EffectiveGateSet} (conv : GateConvention G) (ell q : ℕ) :
    EffectiveCircuit G (ell+(q+1)) :=
  tensorCircuit ([] : EffectiveCircuit G ell) (negativeCircuit conv q)

lemma negativeDataCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G)
    (ell q : ℕ) : (negativeDataCircuit conv ell q).matrix = -1 := by
  rw [negativeDataCircuit, tensorCircuit_matrix, negativeCircuit_matrix]
  simp only [EffectiveCircuit.matrix]
  have hk : kronecker (1 : Operator ell) (-1 : Operator (q+1)) =
      -(1 : Matrix (Basis ell × Basis (q+1)) (Basis ell × Basis (q+1)) ℂ) := by
    ext ⟨a,i⟩ ⟨b,j⟩
    by_cases ha : a=b <;> by_cases hi : i=j <;>
      simp [Matrix.kronecker,Matrix.one_apply,ha,hi,Prod.ext_iff]
  rw [hk]
  ext x y
  simp [Matrix.submatrix_apply,Matrix.one_apply,(tensorBits ell (q+1)).injective.eq_iff]

/-- Reflection about ell+1 small zero bits, with q arbitrary remaining bits.
This construction also works for q=0 and adds no register. -/
def zeroSmallReflectionCircuit {G : EffectiveGateSet} (conv : GateConvention G)
    (ell q : ℕ) : EffectiveCircuit G (ell+(q+1)) :=
  patternCircuit conv ell (fun _ => 0) (negativeZCircuit conv q) ++
    negativeDataCircuit conv ell q

theorem zeroSmallReflectionCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G)
    (ell q : ℕ) :
    (zeroSmallReflectionCircuit conv ell q).matrix =
      (projectorReflection (zeroSmallProjector ell q)).submatrix
        (registerBasis ell (q+1)) (registerBasis ell (q+1)) := by
  rw [zeroSmallReflectionCircuit, EffectiveCircuit.matrix_append, negativeDataCircuit_matrix,
    neg_one_mul, patternCircuit_matrix, negativeZCircuit_matrix]
  have h : -(patternBlock (fun _ => 0)
      (Matrix.diagonal (fun x : Basis (q+1) => if x 0 = 0 then (-1:ℂ) else 1))) =
      projectorReflection (zeroSmallProjector ell q) := by
    ext ⟨a,i⟩ ⟨b,j⟩
    by_cases ha : a = (fun _ => 0) <;> by_cases hab : a = b <;>
      by_cases hij : i = j <;> by_cases hi : i 0 = 0 <;>
      simp [patternBlock, Paper25.selectMatrix, zeroSmallProjector, projectorReflection,
        Matrix.diagonal_apply, Matrix.one_apply, two_smul, ha,hab,hij,hi,Prod.ext_iff] <;> aesop
  exact congrArg (fun M => M.submatrix (registerBasis ell (q+1))
    (registerBasis ell (q+1))) h

theorem zeroSmallReflectionCircuit_length {G : EffectiveGateSet} (conv : GateConvention G)
    (ell q : ℕ) :
    (zeroSmallReflectionCircuit conv ell q).length ≤
      conv.bound^(ell+1)*(5*conv.X.length+6*conv.bound)+4*(conv.X.length+conv.bound) := by
  rw [zeroSmallReflectionCircuit, List.length_append]
  have hz : (negativeZCircuit conv q).length ≤ 5*conv.X.length+6*conv.bound := by
    simp only [negativeZCircuit, List.length_append, flipCircuit, embedCircuit_length]
    have hh := conv.hadamard_length q
    have hn := negativeCircuit_length conv q
    omega
  have hp := (patternCircuit_length conv ell (fun _ => 0) (negativeZCircuit conv q)).trans
    (Nat.mul_le_mul_left _ hz)
  simpa only [negativeDataCircuit, tensorCircuit_length, List.length_nil, zero_add] using
    Nat.add_le_add hp (negativeCircuit_length conv q)

end Paper25.OperationalModel.LocalCompilation

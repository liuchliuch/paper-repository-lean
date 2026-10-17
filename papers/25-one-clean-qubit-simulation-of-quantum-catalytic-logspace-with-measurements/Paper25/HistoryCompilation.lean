import Paper25.LocalCompilation
import Paper25.HistoryEncoding
import Paper25.ReflectionCompilation
import Paper25.ClockCompilation

/-! Actual finite local gate lists for the two nested history multiplexers and
the final weighted selector. The inputs are component source-term circuits and
standard one-register PREPARE/increment circuits; the history and A circuits are
constructed here rather than assumed as full-space implementation inputs. -/
noncomputable section
open Matrix
namespace Paper25.OperationalModel.LocalCompilation
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1200000

lemma tensorBits_eq_registerBasis (q r : ℕ) : tensorBits q r = registerBasis q r := by
  apply Equiv.ext
  intro x
  apply Prod.ext <;> funext i <;> rfl

lemma kronecker_reindex {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    (e : a ≃ b) (f : c ≃ d) (A : Matrix b b ℂ) (B : Matrix d d ℂ) :
    Matrix.kronecker (A.submatrix e e) (B.submatrix f f) =
      (Matrix.kronecker A B).submatrix (e.prodCongr f) (e.prodCongr f) := by
  ext i j
  rfl

lemma selectMatrix_reindex {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (f : c ≃ d)
    (K : b → Matrix d d ℂ) :
    Paper25.selectMatrix (fun i => (K (e i)).submatrix f f) =
      (Paper25.selectMatrix K).submatrix (e.prodCongr f) (e.prodCongr f) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  simp [Paper25.selectMatrix,Matrix.submatrix_apply,e.injective.eq_iff]

lemma lcuMatrix_reindex {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d]
    (e : a ≃ b) (f : c ≃ d) (P : Matrix b b ℂ) (K : b → Matrix d d ℂ) :
    Paper25.lcuMatrix (P.submatrix e e) (fun i => (K (e i)).submatrix f f) =
      (Paper25.lcuMatrix P K).submatrix (e.prodCongr f) (e.prodCongr f) := by
  have hid : (1 : Matrix c c ℂ) = (1 : Matrix d d ℂ).submatrix f f :=
    (Matrix.submatrix_one_equiv f).symm
  unfold Paper25.lcuMatrix
  rw [hid,kronecker_reindex,selectMatrix_reindex,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
  rfl

/-- PREPARE, explicit finite SELECT, and the actual inverse PREPARE list. -/
def lcuCircuit {G : EffectiveGateSet} (conv : GateConvention G) {ell q : ℕ}
    (prepare : EffectiveCircuit G (ell+q)) (branches : Basis ell → EffectiveCircuit G q) :
    EffectiveCircuit G (ell+q) := coherentFilterCircuit conv prepare (selectCircuit conv branches)

lemma lcuCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) {ell q : ℕ}
    (prepare : EffectiveCircuit G (ell+q)) (branches : Basis ell → EffectiveCircuit G q) :
    (lcuCircuit conv prepare branches).matrix =
      prepare.matrix.conjTranspose *
        (Paper25.selectMatrix (fun j => (branches j).matrix)).submatrix
          (registerBasis ell q) (registerBasis ell q) * prepare.matrix := by
  rw [lcuCircuit,coherentFilterCircuit_matrix,selectCircuit_matrix]

lemma lcuCircuit_realizes {G : EffectiveGateSet} (conv : GateConvention G) {ell q : ℕ}
    (prepare : EffectiveCircuit G (ell+q)) (branches : Basis ell → EffectiveCircuit G q)
    (P : Operator ell) (K : Basis ell → Operator q)
    (hp : prepare.matrix = (Matrix.kronecker P (1 : Operator q)).submatrix
      (registerBasis ell q) (registerBasis ell q))
    (hk : ∀ j, (branches j).matrix = K j) :
    (lcuCircuit conv prepare branches).matrix =
      (Paper25.lcuMatrix P K).submatrix (registerBasis ell q) (registerBasis ell q) := by
  rw [lcuCircuit_matrix,hp]
  simp only [hk,Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv]
  rfl

lemma lcuCircuit_length {G : EffectiveGateSet} (conv : GateConvention G) {ell q : ℕ}
    (prepare : EffectiveCircuit G (ell+q)) (branches : Basis ell → EffectiveCircuit G q)
    (B : ℕ) (hb : ∀ j, (branches j).length ≤ B) :
    (lcuCircuit conv prepare branches).length ≤
      (conv.bound+1)*prepare.length + 2^ell*conv.bound^(ell+1)*B := by
  dsimp [lcuCircuit,coherentFilterCircuit]
  simp only [List.length_append]
  have ha := adjointCircuit_length conv prepare
  have hs := selectCircuit_length conv branches B hb
  nlinarith

/-- Three physical Hadamards, with the same binary order as Selector3. -/
def uniform3Circuit {G : EffectiveGateSet} (conv : GateConvention G) : EffectiveCircuit G 3 :=
  tensorCircuit (conv.hadamardAt 0)
    (tensorCircuit (conv.hadamardAt 0) (conv.hadamardAt 0))

def uniform3Layout : Basis 3 ≃ Paper25.Selector3 :=
  (tensorBits 1 2).trans
    (oneBit.prodCongr ((tensorBits 1 1).trans (oneBit.prodCongr oneBit)))

lemma hadamard_one : physicalHadamard 0 = Paper25.StatePreparation.H2.submatrix oneBit oneBit := by
  ext x y
  have hb : ∀ b : Fin 2, b = 0 ∨ b = 1 := by intro b; fin_cases b <;> simp
  have ht : (fun i : Fin 0 => x i.succ) = (fun i : Fin 0 => y i.succ) := Subsingleton.elim _ _
  rcases hb (x 0) with hx | hx <;> rcases hb (y 0) with hy | hy <;>
    simp [physicalHadamard,probeBasis,probeTensor,OneCleanQubit.tensorBasis,
      OneCleanQubit.hadamard,Matrix.submatrix_apply,Matrix.fromBlocks,Matrix.one_apply,
      oneBit,Paper25.StatePreparation.H2_apply,hx,hy,ht]

lemma uniform3Circuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) :
    (uniform3Circuit conv).matrix =
      Paper25.uniformPrepare3.submatrix uniform3Layout uniform3Layout := by
  simp only [uniform3Circuit,tensorCircuit_matrix,conv.hadamard_matrix,hadamard_one,
    kronecker_reindex]
  ext x y
  rfl

lemma uniform3Circuit_length {G : EffectiveGateSet} (conv : GateConvention G) :
    (uniform3Circuit conv).length ≤ 3*conv.bound := by
  simp only [uniform3Circuit,tensorCircuit,List.length_append,List.length_map]
  have h := conv.hadamard_length 0
  omega

def selectorLayout (q : ℕ) : Basis (3+q) ≃ (Paper25.Selector3 × Basis q) :=
  (registerBasis 3 q).trans (uniform3Layout.prodCongr (Equiv.refl _))

def selectorPrepareCircuit {G : EffectiveGateSet} (conv : GateConvention G) (q : ℕ) :
    EffectiveCircuit G (3+q) := tensorCircuit (uniform3Circuit conv) ([] : EffectiveCircuit G q)

lemma selectorPrepareCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) (q : ℕ) :
    (selectorPrepareCircuit conv q).matrix =
      (Matrix.kronecker Paper25.uniformPrepare3 (1 : Operator q)).submatrix
        (selectorLayout q) (selectorLayout q) := by
  rw [selectorPrepareCircuit,tensorCircuit_matrix,uniform3Circuit_matrix,EffectiveCircuit.matrix]
  rw [show (1 : Operator q) = (1 : Operator q).submatrix (Equiv.refl _) (Equiv.refl _) by simp]
  rw [kronecker_reindex]
  ext x y
  simp [selectorLayout,tensorBits_eq_registerBasis,Matrix.submatrix_apply]

/-- The paper's actual eight-term selector schedule. -/
def sourceLCUCircuit {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (K : Fin 8 → EffectiveCircuit G q) : EffectiveCircuit G (3+q) :=
  lcuCircuit conv (selectorPrepareCircuit conv q)
    (fun j => K (Paper25.selectorIndex3 (uniform3Layout j)))

lemma sourceLCUCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (K : Fin 8 → EffectiveCircuit G q) :
    (sourceLCUCircuit conv K).matrix =
      (Paper25.eightLCU (fun j => (K j).matrix)).submatrix (selectorLayout q) (selectorLayout q) := by
  rw [sourceLCUCircuit,lcuCircuit_matrix,selectorPrepareCircuit_matrix]
  have hs := selectMatrix_reindex uniform3Layout (Equiv.refl (Basis q))
    (fun j : Paper25.Selector3 => (K (Paper25.selectorIndex3 j)).matrix)
  have hsel :
      (Paper25.selectMatrix (fun j => (K (Paper25.selectorIndex3 (uniform3Layout j))).matrix)).submatrix
        (registerBasis 3 q) (registerBasis 3 q) =
      (Paper25.selectMatrix (fun j : Paper25.Selector3 => (K (Paper25.selectorIndex3 j)).matrix)).submatrix
        (selectorLayout q) (selectorLayout q) := by
    have hs' := congrArg (fun M : Matrix (Basis 3 × Basis q) (Basis 3 × Basis q) ℂ =>
      M.submatrix (registerBasis 3 q) (registerBasis 3 q)) hs
    simpa only [Matrix.submatrix_submatrix,selectorLayout,Equiv.trans_apply,
      Function.comp_def,Equiv.refl_apply] using hs'
  rw [hsel,Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
  rfl

lemma sourceLCUCircuit_length {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (K : Fin 8 → EffectiveCircuit G q) (B : ℕ) (hB : ∀ j, (K j).length ≤ B) :
    (sourceLCUCircuit conv K).length ≤ (conv.bound+1)*(3*conv.bound) +
      8*conv.bound^4*B := by
  have hp : (selectorPrepareCircuit conv q).length ≤ 3*conv.bound := by
    simpa [selectorPrepareCircuit] using uniform3Circuit_length conv
  have h := lcuCircuit_length conv (selectorPrepareCircuit conv q)
    (fun j => K (Paper25.selectorIndex3 (uniform3Layout j))) B (fun j => hB _)
  dsimp [sourceLCUCircuit]
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hp) _)

/-- Inactive clock values have four I and four -I branches, literally. -/
def inactiveCircuits {G : EffectiveGateSet} {q : ℕ} (negative : EffectiveCircuit G q) :
    Fin 8 → EffectiveCircuit G q := fun j => if j.val < 4 then [] else negative

lemma inactiveCircuits_matrix {G : EffectiveGateSet} {q : ℕ} (negative : EffectiveCircuit G q)
    (hn : negative.matrix = -1) (j : Fin 8) :
    (inactiveCircuits negative j).matrix = Paper25.inactiveTerms j := by
  fin_cases j <;> simp [inactiveCircuits,EffectiveCircuit.matrix,hn,Paper25.inactiveTerms]

/-- A fixed clock scan; its active branch queries the indexed source term list. -/
def clockBranchCircuit {G : EffectiveGateSet} (conv : GateConvention G) {ell q J : ℕ}
    (T : ℕ) (clockIndex : Basis ell ≃ Fin J) (negative : EffectiveCircuit G q)
    (K : ℕ → Fin 8 → EffectiveCircuit G q) (r : Basis ell) : EffectiveCircuit G (3+q) :=
  sourceLCUCircuit conv (if (clockIndex r).val < T then K (clockIndex r).val else inactiveCircuits negative)

def clockLayout {ell q J : ℕ} (clockIndex : Basis ell ≃ Fin J) :
    Basis (ell+(3+q)) ≃ (Fin J × (Paper25.Selector3 × Basis q)) :=
  (registerBasis ell (3+q)).trans (clockIndex.prodCongr (selectorLayout q))

def clockSelectCircuit {G : EffectiveGateSet} (conv : GateConvention G) {ell q J : ℕ}
    (T : ℕ) (clockIndex : Basis ell ≃ Fin J) (negative : EffectiveCircuit G q)
    (K : ℕ → Fin 8 → EffectiveCircuit G q) : EffectiveCircuit G (ell+(3+q)) :=
  selectCircuit conv (clockBranchCircuit conv T clockIndex negative K)

/-- The actual history circuit advances the clock after the nested selectors. -/
def rawHistoryCircuit {G : EffectiveGateSet} (conv : GateConvention G) {ell q J : ℕ}
    (T : ℕ) (clockIndex : Basis ell ≃ Fin J) (negative : EffectiveCircuit G q)
    (K : ℕ → Fin 8 → EffectiveCircuit G q) (increment : EffectiveCircuit G ell) :
    EffectiveCircuit G (ell+(3+q)) :=
  clockSelectCircuit conv T clockIndex negative K ++
    tensorCircuit increment ([] : EffectiveCircuit G (3+q))

lemma clockBranchCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) {ell q J : ℕ}
    (T : ℕ) (clockIndex : Basis ell ≃ Fin J) (negative : EffectiveCircuit G q)
    (hn : negative.matrix = -1) (K : ℕ → Fin 8 → EffectiveCircuit G q) (r : Basis ell) :
    (clockBranchCircuit conv T clockIndex negative K r).matrix =
      (Paper25.HistoryEncoding.clockSelected (T := T) (fun t a => (K t a).matrix) (clockIndex r)).submatrix
        (selectorLayout q) (selectorLayout q) := by
  unfold clockBranchCircuit Paper25.HistoryEncoding.clockSelected
  split_ifs with h
  · exact sourceLCUCircuit_matrix conv _
  · rw [sourceLCUCircuit_matrix]
    simp only [inactiveCircuits_matrix negative hn]

lemma clockSelectCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) {ell q J : ℕ}
    (T : ℕ) (clockIndex : Basis ell ≃ Fin J) (negative : EffectiveCircuit G q)
    (hn : negative.matrix = -1) (K : ℕ → Fin 8 → EffectiveCircuit G q) :
    (clockSelectCircuit conv T clockIndex negative K).matrix =
      (Paper25.selectMatrix (Paper25.HistoryEncoding.clockSelected (T := T)
        (fun t a => (K t a).matrix))).submatrix
        (clockLayout clockIndex) (clockLayout clockIndex) := by
  rw [clockSelectCircuit,selectCircuit_matrix]
  simp only [clockBranchCircuit_matrix conv T clockIndex negative hn K]
  rw [selectMatrix_reindex]
  rfl

lemma reversibleGate_prod {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ a) :
    Matrix.kronecker (Paper25.KrausChannel.reversibleGate e) (1 : Matrix b b ℂ) =
      Paper25.KrausChannel.reversibleGate (e.prodCongr (Equiv.refl b)) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  by_cases hi : e.symm i = j <;> by_cases hx : x = y <;>
    simp [Matrix.kronecker,Paper25.KrausChannel.reversibleGate,Matrix.one_apply,hi,hx]

lemma increment_extended_matrix {G : EffectiveGateSet} {ell q J : ℕ}
    (clockIndex : Basis ell ≃ Fin J) (increment : EffectiveCircuit G ell)
    (hinc : increment.matrix = (Paper25.KrausChannel.reversibleGate (finRotate J)).submatrix
      clockIndex clockIndex) :
    (tensorCircuit increment ([] : EffectiveCircuit G (3+q))).matrix =
      (Paper25.KrausChannel.reversibleGate (Paper25.HistoryEncoding.clockAdvance J)).submatrix
        (clockLayout (q := q) clockIndex) (clockLayout (q := q) clockIndex) := by
  rw [tensorCircuit_matrix,hinc,EffectiveCircuit.matrix]
  have hid : (1 : Operator (3+q)) = (1 : Matrix (Paper25.Selector3 × Basis q) _ ℂ).submatrix
      (selectorLayout q) (selectorLayout q) := (Matrix.submatrix_one_equiv _).symm
  rw [hid,kronecker_reindex,reversibleGate_prod]
  rfl

/-- This equality is proved from the individual native source terms and the
native increment, with no assumed implementation of the history operator. -/
theorem rawHistoryCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) {ell q J : ℕ}
    (T : ℕ) (clockIndex : Basis ell ≃ Fin J) (negative : EffectiveCircuit G q)
    (hn : negative.matrix = -1) (K : ℕ → Fin 8 → EffectiveCircuit G q)
    (increment : EffectiveCircuit G ell)
    (hinc : increment.matrix = (Paper25.KrausChannel.reversibleGate (finRotate J)).submatrix
      clockIndex clockIndex) :
    (rawHistoryCircuit conv T clockIndex negative K increment).matrix =
      (Paper25.HistoryEncoding.rawHistoryUnitary T J (fun t a => (K t a).matrix)).submatrix
        (clockLayout clockIndex) (clockLayout clockIndex) := by
  rw [rawHistoryCircuit,EffectiveCircuit.matrix_append,
    increment_extended_matrix clockIndex increment hinc,
    clockSelectCircuit_matrix conv T clockIndex negative hn K,Matrix.submatrix_mul_equiv]
  rfl

lemma inactiveCircuits_length {G : EffectiveGateSet} {q : ℕ} (negative : EffectiveCircuit G q)
    (j : Fin 8) : (inactiveCircuits negative j).length ≤ negative.length := by
  simp only [inactiveCircuits]
  split_ifs <;> simp

lemma clockBranchCircuit_length {G : EffectiveGateSet} (conv : GateConvention G) {ell q J : ℕ}
    (T : ℕ) (clockIndex : Basis ell ≃ Fin J) (negative : EffectiveCircuit G q)
    (K : ℕ → Fin 8 → EffectiveCircuit G q) (B : ℕ)
    (hn : negative.length ≤ B) (hK : ∀ t < T, ∀ a, (K t a).length ≤ B) (r : Basis ell) :
    (clockBranchCircuit conv T clockIndex negative K r).length ≤
      (conv.bound+1)*(3*conv.bound) + 8*conv.bound^4*B := by
  apply sourceLCUCircuit_length
  intro j
  split_ifs with h
  · exact hK _ h j
  · exact (inactiveCircuits_length negative j).trans hn

lemma rawHistoryCircuit_length {G : EffectiveGateSet} (conv : GateConvention G) {ell q J : ℕ}
    (T : ℕ) (clockIndex : Basis ell ≃ Fin J) (negative : EffectiveCircuit G q)
    (K : ℕ → Fin 8 → EffectiveCircuit G q) (increment : EffectiveCircuit G ell) (B : ℕ)
    (hn : negative.length ≤ B) (hK : ∀ t < T, ∀ a, (K t a).length ≤ B) :
    (rawHistoryCircuit conv T clockIndex negative K increment).length ≤
      2^ell*conv.bound^(ell+1)*((conv.bound+1)*(3*conv.bound)+8*conv.bound^4*B) +
        increment.length := by
  rw [rawHistoryCircuit,List.length_append,tensorCircuit_length,List.length_nil,Nat.add_zero]
  exact Nat.add_le_add_right (selectCircuit_length conv _ _
    (clockBranchCircuit_length conv T clockIndex negative K B hn hK)) _

/-- Relabeling physical positions maps local placements, rather than inserting
an arbitrary basis permutation as a new quantum gate. -/
def rewireBasis {q r : ℕ} (e : Fin q ≃ Fin r) : Basis r ≃ Basis q where
  toFun x i := x (e i)
  invFun y j := y (e.symm j)
  left_inv x := by funext i; simp
  right_inv y := by funext i; simp

def rewireCircuit {G : EffectiveGateSet} {q r : ℕ} (e : Fin q ≃ Fin r)
    (C : EffectiveCircuit G q) : EffectiveCircuit G r :=
  embedCircuit (placementOfEmbedding e.toEmbedding) C

lemma rewireCircuit_matrix {G : EffectiveGateSet} {q r : ℕ} (e : Fin q ≃ Fin r)
    (C : EffectiveCircuit G q) : (rewireCircuit e C).matrix =
      C.matrix.submatrix (rewireBasis e) (rewireBasis e) := by
  rw [rewireCircuit,embedCircuit_matrix]
  ext x y
  rw [lift_apply]
  have h : Inactive (active (placementOfEmbedding e.toEmbedding)) x y := by
    intro j hj
    exfalso
    apply hj
    exact ⟨e.symm j, by simp⟩
  simp only [h,ite_true,mul_one,active_placementOfEmbedding,Matrix.submatrix_apply]
  rfl

@[simp] lemma rewireCircuit_length {G : EffectiveGateSet} {q r : ℕ} (e : Fin q ≃ Fin r)
    (C : EffectiveCircuit G q) : (rewireCircuit e C).length = C.length := by
  simp [rewireCircuit]

/-- Swap two initial physical registers and retain the data positions. -/
def swapPrefix (a b c : ℕ) : Fin (a+(b+c)) ≃ Fin (b+(a+c)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm)).trans
    ((Equiv.sumAssoc _ _ _).symm.trans
      ((Equiv.sumCongr (Equiv.sumComm _ _) (Equiv.refl _)).trans
        ((Equiv.sumAssoc _ _ _).trans
          ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv))))

def historyLayout {ell q J : ℕ} (clockIndex : Basis ell ≃ Fin J) :
    Basis (3+(ell+q)) ≃ (Paper25.Selector3 × (Fin J × Basis q)) :=
  (registerBasis 3 (ell+q)).trans (uniform3Layout.prodCongr
    ((registerBasis ell q).trans (clockIndex.prodCongr (Equiv.refl _))))

lemma historyLayout_swap {ell q J : ℕ} (clockIndex : Basis ell ≃ Fin J)
    (x : Basis (3+(ell+q))) :
    clockLayout clockIndex (rewireBasis (swapPrefix ell 3 q) x) =
      Paper25.HistoryEncoding.selectorClockOrder J (historyLayout clockIndex x) := by
  dsimp [clockLayout,selectorLayout,historyLayout,registerBasis,
    Paper25.HistoryEncoding.selectorClockOrder]
  apply Prod.ext
  · dsimp only
    apply congrArg clockIndex
    funext i
    simp [rewireBasis,swapPrefix,registerBasis]
  · apply Prod.ext
    · dsimp only
      apply congrArg uniform3Layout
      funext i
      simp [rewireBasis,swapPrefix,registerBasis]
    · funext i
      simp [rewireBasis,swapPrefix,registerBasis]

/-- The actual wire relabeling puts the three block ancillas first. -/
def historyCircuit {G : EffectiveGateSet} (conv : GateConvention G) {ell q J : ℕ}
    (T : ℕ) (clockIndex : Basis ell ≃ Fin J) (negative : EffectiveCircuit G q)
    (K : ℕ → Fin 8 → EffectiveCircuit G q) (increment : EffectiveCircuit G ell) :
    EffectiveCircuit G (3+(ell+q)) :=
  rewireCircuit (swapPrefix ell 3 q)
    (rawHistoryCircuit conv T clockIndex negative K increment)

theorem historyCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) {ell q J : ℕ}
    (T : ℕ) (clockIndex : Basis ell ≃ Fin J) (negative : EffectiveCircuit G q)
    (hn : negative.matrix = -1) (K : ℕ → Fin 8 → EffectiveCircuit G q)
    (increment : EffectiveCircuit G ell)
    (hinc : increment.matrix = (Paper25.KrausChannel.reversibleGate (finRotate J)).submatrix
      clockIndex clockIndex) :
    (historyCircuit conv T clockIndex negative K increment).matrix =
      (Paper25.HistoryEncoding.historyUnitary T J (fun t a => (K t a).matrix)).submatrix
        (historyLayout clockIndex) (historyLayout clockIndex) := by
  rw [historyCircuit,rewireCircuit_matrix,rawHistoryCircuit_matrix conv T clockIndex negative hn K increment hinc]
  ext x y
  simp only [Matrix.submatrix_apply,historyLayout_swap,Paper25.HistoryEncoding.historyUnitary]

/-- A one-qubit PREPARE followed by the two branches I and -C, then its
actual inverse. The PREPARE can be a rational-angle approximation. -/
def differenceBranches {G : EffectiveGateSet} {q : ℕ}
    (C negative : EffectiveCircuit G q) (j : Basis 1) : EffectiveCircuit G q :=
  if oneBit j = 0 then [] else C ++ negative

def weightedDifferenceCircuit {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (prepare : EffectiveCircuit G 1) (C negative : EffectiveCircuit G q) :
    EffectiveCircuit G (1+q) :=
  lcuCircuit conv (tensorCircuit prepare ([] : EffectiveCircuit G q)) (differenceBranches C negative)

def differenceLayout (q : ℕ) : Basis (1+q) ≃ (Fin 2 × Basis q) :=
  (registerBasis 1 q).trans (oneBit.prodCongr (Equiv.refl _))

lemma differenceBranches_matrix {G : EffectiveGateSet} {q : ℕ}
    (C negative : EffectiveCircuit G q) (hn : negative.matrix = -1) (j : Basis 1) :
    (differenceBranches C negative j).matrix = (![1,-C.matrix] : Fin 2 → Operator q) (oneBit j) := by
  have hj : oneBit j = 0 ∨ oneBit j = 1 := by
    have hb : ∀ b : Fin 2, b = 0 ∨ b = 1 := by intro b; fin_cases b <;> simp
    exact hb _
  rcases hj with hj | hj
  · simp [differenceBranches,hj,EffectiveCircuit.matrix]
  · simp [differenceBranches,hj,EffectiveCircuit.matrix_append,hn]

lemma weightedDifferenceCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (prepare : EffectiveCircuit G 1) (C negative : EffectiveCircuit G q)
    (hn : negative.matrix = -1) (P : Matrix (Fin 2) (Fin 2) ℂ)
    (hp : prepare.matrix = P.submatrix oneBit oneBit) :
    (weightedDifferenceCircuit conv prepare C negative).matrix =
      (Paper25.lcuMatrix P ![1,-C.matrix]).submatrix (differenceLayout q) (differenceLayout q) := by
  rw [weightedDifferenceCircuit,lcuCircuit_matrix,tensorCircuit_matrix,hp,EffectiveCircuit.matrix]
  rw [show (1 : Operator q) = (1 : Operator q).submatrix (Equiv.refl _) (Equiv.refl _) by simp]
  rw [kronecker_reindex]
  have hs := selectMatrix_reindex oneBit (Equiv.refl (Basis q))
    (![1,-C.matrix] : Fin 2 → Operator q)
  have hsel :
      (Paper25.selectMatrix (fun j => (differenceBranches C negative j).matrix)).submatrix
        (registerBasis 1 q) (registerBasis 1 q) =
      (Paper25.selectMatrix (![1,-C.matrix] : Fin 2 → Operator q)).submatrix
        (differenceLayout q) (differenceLayout q) := by
    simp only [differenceBranches_matrix C negative hn]
    have hs' := congrArg (fun M : Matrix (Basis 1 × Basis q) (Basis 1 × Basis q) ℂ =>
      M.submatrix (registerBasis 1 q) (registerBasis 1 q)) hs
    simpa only [Matrix.submatrix_submatrix,differenceLayout,Equiv.trans_apply,
      Function.comp_def,Equiv.refl_apply] using hs'
  rw [hsel]
  rw [tensorBits_eq_registerBasis]
  simp only [Matrix.conjTranspose_submatrix,Matrix.submatrix_submatrix]
  change ((Matrix.kronecker P (1 : Operator q)).conjTranspose).submatrix
      (differenceLayout q) (differenceLayout q) *
    (Paper25.selectMatrix (![1,-C.matrix] : Fin 2 → Operator q)).submatrix
      (differenceLayout q) (differenceLayout q) *
    (Matrix.kronecker P (1 : Operator q)).submatrix
      (differenceLayout q) (differenceLayout q) = _
  rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
  rfl

lemma weightedDifferenceCircuit_length {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (prepare : EffectiveCircuit G 1) (C negative : EffectiveCircuit G q) :
    (weightedDifferenceCircuit conv prepare C negative).length ≤
      (conv.bound+1)*prepare.length + 2*conv.bound^2*(C.length+negative.length) := by
  have hb : ∀ j, (differenceBranches C negative j).length ≤ C.length+negative.length := by
    intro j
    simp only [differenceBranches]
    split_ifs <;> simp
  simpa [weightedDifferenceCircuit] using lcuCircuit_length conv
    (tensorCircuit prepare ([] : EffectiveCircuit G q)) (differenceBranches C negative)
    (C.length+negative.length) hb

/-- The paper's A construction, with all history layers compiled above and one
explicit one-qubit PREPARE argument. No full A implementation is an input. -/
def historyACircuit {G : EffectiveGateSet} (conv : GateConvention G) {ell q J : ℕ}
    (T : ℕ) (clockIndex : Basis ell ≃ Fin J) (negative : EffectiveCircuit G q)
    (K : ℕ → Fin 8 → EffectiveCircuit G q) (increment : EffectiveCircuit G ell)
    (prepare : EffectiveCircuit G 1) (negativeHistory : EffectiveCircuit G (3+(ell+q))) :
    EffectiveCircuit G (1+(3+(ell+q))) :=
  weightedDifferenceCircuit conv prepare (historyCircuit conv T clockIndex negative K increment) negativeHistory

def historyALayout {ell q J : ℕ} (clockIndex : Basis ell ≃ Fin J) :
    Basis (1+(3+(ell+q))) ≃ (Fin 2 × (Paper25.Selector3 × (Fin J × Basis q))) :=
  (differenceLayout (3+(ell+q))).trans ((Equiv.refl _).prodCongr (historyLayout clockIndex))

/-- Exact lower-level statement; the rational PREPARE approximation uses the
same actual gate list and replaces P by its computed rational-angle matrix. -/
theorem historyACircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) {ell q J : ℕ}
    (T : ℕ) (clockIndex : Basis ell ≃ Fin J) (negative : EffectiveCircuit G q)
    (hn : negative.matrix = -1) (K : ℕ → Fin 8 → EffectiveCircuit G q)
    (increment : EffectiveCircuit G ell)
    (hinc : increment.matrix = (Paper25.KrausChannel.reversibleGate (finRotate J)).submatrix
      clockIndex clockIndex) (prepare : EffectiveCircuit G 1)
    (negativeHistory : EffectiveCircuit G (3+(ell+q))) (hnh : negativeHistory.matrix = -1)
    (P : Matrix (Fin 2) (Fin 2) ℂ) (hp : prepare.matrix = P.submatrix oneBit oneBit) :
    (historyACircuit conv T clockIndex negative K increment prepare negativeHistory).matrix =
      (Paper25.lcuMatrix P ![1,-(Paper25.HistoryEncoding.historyUnitary T J
        (fun t a => (K t a).matrix))]).submatrix (historyALayout clockIndex) (historyALayout clockIndex) := by
  rw [historyACircuit,weightedDifferenceCircuit_matrix conv prepare _ negativeHistory hnh P hp,
    historyCircuit_matrix conv T clockIndex negative hn K increment hinc]
  have hs := lcuMatrix_reindex (Equiv.refl (Fin 2)) (historyLayout (q := q) clockIndex) P
    (![1,-(Paper25.HistoryEncoding.historyUnitary T J (fun t a => (K t a).matrix))])
  have he : (fun j : Fin 2 =>
      ((![1,-(Paper25.HistoryEncoding.historyUnitary T J (fun t a => (K t a).matrix))]) j).submatrix
        (historyLayout (q := q) clockIndex) (historyLayout (q := q) clockIndex)) =
      ![1,-((Paper25.HistoryEncoding.historyUnitary T J (fun t a => (K t a).matrix)).submatrix
        (historyLayout clockIndex) (historyLayout clockIndex))] := by
    funext j
    fin_cases j
    · simp
    · rfl
  change Paper25.lcuMatrix P (fun j : Fin 2 =>
    ((![1,-(Paper25.HistoryEncoding.historyUnitary T J (fun t a => (K t a).matrix))]) j).submatrix
      (historyLayout clockIndex) (historyLayout clockIndex)) = _ at hs
  rw [he] at hs
  have hs' := congrArg (fun M : Matrix (Fin 2 × Basis (3+(ell+q))) _ ℂ =>
    M.submatrix (differenceLayout (3+(ell+q))) (differenceLayout (3+(ell+q)))) hs
  simpa only [Matrix.submatrix_submatrix,historyALayout,Equiv.trans_apply,Function.comp_def] using hs'

lemma historyCircuit_length {G : EffectiveGateSet} (conv : GateConvention G) {ell q J : ℕ}
    (T : ℕ) (clockIndex : Basis ell ≃ Fin J) (negative : EffectiveCircuit G q)
    (K : ℕ → Fin 8 → EffectiveCircuit G q) (increment : EffectiveCircuit G ell) (B : ℕ)
    (hn : negative.length ≤ B) (hK : ∀ t < T, ∀ a, (K t a).length ≤ B) :
    (historyCircuit conv T clockIndex negative K increment).length ≤
      2^ell*conv.bound^(ell+1)*((conv.bound+1)*(3*conv.bound)+8*conv.bound^4*B) +
        increment.length := by
  simpa only [historyCircuit,rewireCircuit_length] using
    rawHistoryCircuit_length conv T clockIndex negative K increment B hn hK

lemma historyACircuit_length {G : EffectiveGateSet} (conv : GateConvention G) {ell q J : ℕ}
    (T : ℕ) (clockIndex : Basis ell ≃ Fin J) (negative : EffectiveCircuit G q)
    (K : ℕ → Fin 8 → EffectiveCircuit G q) (increment : EffectiveCircuit G ell)
    (prepare : EffectiveCircuit G 1) (negativeHistory : EffectiveCircuit G (3+(ell+q)))
    (B : ℕ) (hn : negative.length ≤ B) (hK : ∀ t < T, ∀ a, (K t a).length ≤ B) :
    (historyACircuit conv T clockIndex negative K increment prepare negativeHistory).length ≤
      (conv.bound+1)*prepare.length + 2*conv.bound^2 *
        (2^ell*conv.bound^(ell+1)*((conv.bound+1)*(3*conv.bound)+8*conv.bound^4*B) +
          increment.length + negativeHistory.length) := by
  apply (weightedDifferenceCircuit_length conv prepare _ negativeHistory).trans
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _
    (Nat.add_le_add_right (historyCircuit_length conv T clockIndex negative K increment B hn hK) _)) _

/-- Scalar minus identity on any nonempty physical register, using the explicit
H/X commutator construction rather than an ignored global phase. -/
def negativeOn {G : EffectiveGateSet} (conv : GateConvention G) (q : ℕ) (hq : 0 < q) :
    EffectiveCircuit G q :=
  rewireCircuit (finCongr (show q-1+1=q by omega)) (negativeCircuit conv (q-1))

lemma negativeOn_matrix {G : EffectiveGateSet} (conv : GateConvention G) (q : ℕ) (hq : 0 < q) :
    (negativeOn conv q hq).matrix = -1 := by
  rw [negativeOn,rewireCircuit_matrix,negativeCircuit_matrix]
  ext x y
  simp [Matrix.submatrix_apply,Matrix.one_apply,(rewireBasis (finCongr (show q-1+1=q by omega))).injective.eq_iff]

lemma negativeOn_length {G : EffectiveGateSet} (conv : GateConvention G) (q : ℕ) (hq : 0 < q) :
    (negativeOn conv q hq).length ≤ 4*(conv.X.length+conv.bound) := by
  simpa only [negativeOn,rewireCircuit_length] using negativeCircuit_length conv (q-1)

/-- Fully constructed native history/A gate list. The only variable quantum
components are the indexed source-term lists and the one-qubit PREPARE list;
clock increment, scalar phases and both finite multiplexers are constructed. -/
def nativeHistoryACircuit {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (hq : 0 < q) (T ell : ℕ) (K : ℕ → Fin 8 → EffectiveCircuit G q)
    (prepare : EffectiveCircuit G 1) : EffectiveCircuit G (1+(3+(ell+q))) :=
  historyACircuit conv T (Paper25.SelectedFilter.clockIndex ell) (negativeOn conv q hq) K
    (Paper25.OperationalModel.ClockCompilation.increment conv ell) prepare
    (negativeOn conv (3+(ell+q)) (by omega))

theorem nativeHistoryACircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (hq : 0 < q) (T ell : ℕ) (K : ℕ → Fin 8 → EffectiveCircuit G q)
    (prepare : EffectiveCircuit G 1) (P : Matrix (Fin 2) (Fin 2) ℂ)
    (hp : prepare.matrix = P.submatrix oneBit oneBit) :
    (nativeHistoryACircuit conv hq T ell K prepare).matrix =
      (Paper25.lcuMatrix P ![1,-(Paper25.HistoryEncoding.historyUnitary T
        (Fintype.card (Basis ell)) (fun t a => (K t a).matrix))]).submatrix
        (historyALayout (Paper25.SelectedFilter.clockIndex ell))
        (historyALayout (Paper25.SelectedFilter.clockIndex ell)) := by
  apply historyACircuit_matrix conv T _ _ (negativeOn_matrix conv q hq) K _
    (Paper25.OperationalModel.ClockCompilation.increment_clockIndex_matrix conv ell)
    prepare _ (negativeOn_matrix conv _ _) P hp

lemma nativeHistoryACircuit_length {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (hq : 0 < q) (T ell : ℕ) (K : ℕ → Fin 8 → EffectiveCircuit G q)
    (prepare : EffectiveCircuit G 1) (B : ℕ)
    (hn : 4*(conv.X.length+conv.bound) ≤ B) (hK : ∀ t < T, ∀ a, (K t a).length ≤ B) :
    (nativeHistoryACircuit conv hq T ell K prepare).length ≤
      (conv.bound+1)*prepare.length + 2*conv.bound^2 *
        (2^ell*conv.bound^(ell+1)*((conv.bound+1)*(3*conv.bound)+8*conv.bound^4*B) +
          (2^ell)^(conv.bound+1)*conv.X.length + 4*(conv.X.length+conv.bound)) := by
  apply (historyACircuit_length conv T _ _ K _ prepare _ B
    ((negativeOn_length conv q hq).trans hn) hK).trans
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  exact Nat.add_le_add (Nat.add_le_add_left
    (Paper25.OperationalModel.ClockCompilation.increment_length_states conv ell) _)
      (negativeOn_length conv _ _)

end Paper25.OperationalModel.LocalCompilation

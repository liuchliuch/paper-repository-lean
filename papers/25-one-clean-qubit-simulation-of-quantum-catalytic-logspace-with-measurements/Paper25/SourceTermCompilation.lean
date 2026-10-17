import Paper25.SourceCoordinates
import Paper25.ReflectionCompilation

/-! Native gate lists for the eight unitary terms of actual source operations.
Conjugation is applied only to source primitive gates. Reset phases are realized
exactly by ZX = iY, preserving all phases under subsequent controls. -/
noncomputable section
open Matrix
open scoped ComplexConjugate
namespace Paper25.SourceTermCompilation
open OperationalModel OperationalModel.LocalCompilation ElementaryEncoding
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 512

variable {G : EffectiveGateSet}

def doubleEmbedding {q k : ℕ} (p : Placement q k) : Fin (k+k) ↪ Fin (q+q) where
  toFun i := finSumFinEquiv (Sum.map (active p) (active p) (finSumFinEquiv.symm i))
  inj' := by
    intro i j h
    apply finSumFinEquiv.symm.injective
    apply (Sum.map_injective.mpr ⟨(active p).injective,(active p).injective⟩)
    exact finSumFinEquiv.injective h

def doublePlacement {q k : ℕ} (p : Placement q k) : Placement (q+q) (k+k) :=
  placementOfEmbedding (doubleEmbedding p)

lemma doubleEmbedding_left {q k : ℕ} (p : Placement q k) (i : Fin k) :
    doubleEmbedding p (Fin.castAdd k i) = Fin.castAdd q (active p i) := by
  simp only [doubleEmbedding,Function.Embedding.coeFn_mk,finSumFinEquiv_symm_apply_castAdd,
    Sum.map_inl,finSumFinEquiv_apply_left]

lemma doubleEmbedding_right {q k : ℕ} (p : Placement q k) (i : Fin k) :
    doubleEmbedding p (Fin.natAdd k i) = Fin.natAdd q (active p i) := by
  simp only [doubleEmbedding,Function.Embedding.coeFn_mk,finSumFinEquiv_symm_apply_natAdd,
    Sum.map_inr,finSumFinEquiv_apply_right]

lemma inactive_double {q k : ℕ} (p : Placement q k) (x y : Basis (q+q)) :
    Inactive (doubleEmbedding p) x y ↔
      Inactive (active p) (tensorBits q q x).1 (tensorBits q q y).1 ∧
      Inactive (active p) (tensorBits q q x).2 (tensorBits q q y).2 := by
  constructor
  · intro h
    constructor
    · intro j hj
      apply h (Fin.castAdd q j)
      rintro ⟨a,ha⟩
      revert ha
      refine Fin.addCases (fun i ha => ?_) (fun i ha => ?_) a
      · exact hj ⟨i,by simpa only [doubleEmbedding_left,Fin.castAdd_inj] using ha⟩
      · have hv := congrArg Fin.val ha
        simp only [doubleEmbedding_right] at hv
        change q + (active p i).val = j.val at hv
        omega
    · intro j hj
      apply h (Fin.natAdd q j)
      rintro ⟨a,ha⟩
      revert ha
      refine Fin.addCases (fun i ha => ?_) (fun i ha => ?_) a
      · have hv := congrArg Fin.val ha
        simp only [doubleEmbedding_left] at hv
        change (active p i).val = q + j.val at hv
        have hi := (active p i).isLt
        omega
      · exact hj ⟨i,by simpa only [doubleEmbedding_right,Fin.natAdd_inj] using ha⟩
  · rintro ⟨hL,hR⟩ j
    refine Fin.addCases (fun i hi => ?_) (fun i hi => ?_) j
    · apply hL i
      rintro ⟨a,ha⟩
      apply hi
      exact ⟨Fin.castAdd k a,by rw [doubleEmbedding_left,ha]⟩
    · apply hR i
      rintro ⟨a,ha⟩
      apply hi
      exact ⟨Fin.natAdd k a,by rw [doubleEmbedding_right,ha]⟩

/-- The doubled embedding selects the same physical source wires in each copy. -/
theorem doublePlacement_lift {q k : ℕ} (p : Placement q k)
    (S : Matrix (Basis k × Basis k) (Basis k × Basis k) ℂ) :
    (doublePlacement p).lift (S.submatrix (tensorBits k k) (tensorBits k k)) =
      (liftLiouville p S).submatrix (tensorBits q q) (tensorBits q q) := by
  ext x y
  rw [lift_apply]
  simp only [doublePlacement,active_placementOfEmbedding_eq,inactive_double,
    Matrix.submatrix_apply, liftLiouville,Matrix.kronecker,Matrix.kroneckerMap_apply,
    Matrix.one_apply,reshuffleEquiv,Equiv.prodCongr_apply]
  have hxL : (tensorBits k k (fun i => x (doubleEmbedding p i))).1 =
      (p.split (tensorBits q q x).1).1 := by
    funext i
    change x (doubleEmbedding p (Fin.castAdd k i)) = x (Fin.castAdd q (active p i))
    rw [doubleEmbedding_left]
  have hxR : (tensorBits k k (fun i => x (doubleEmbedding p i))).2 =
      (p.split (tensorBits q q x).2).1 := by
    funext i
    change x (doubleEmbedding p (Fin.natAdd k i)) = x (Fin.natAdd q (active p i))
    rw [doubleEmbedding_right]
  have hyL : (tensorBits k k (fun i => y (doubleEmbedding p i))).1 =
      (p.split (tensorBits q q y).1).1 := by
    funext i
    change y (doubleEmbedding p (Fin.castAdd k i)) = y (Fin.castAdd q (active p i))
    rw [doubleEmbedding_left]
  have hyR : (tensorBits k k (fun i => y (doubleEmbedding p i))).2 =
      (p.split (tensorBits q q y).2).1 := by
    funext i
    change y (doubleEmbedding p (Fin.natAdd k i)) = y (Fin.natAdd q (active p i))
    rw [doubleEmbedding_right]
  have hx : tensorBits k k (fun i => x (doubleEmbedding p i)) =
      ((p.split (tensorBits q q x).1).1,(p.split (tensorBits q q x).2).1) := Prod.ext hxL hxR
  have hy : tensorBits k k (fun i => y (doubleEmbedding p i)) =
      ((p.split (tensorBits q q y).1).1,(p.split (tensorBits q q y).2).1) := Prod.ext hyL hyR
  rw [hx,hy]
  simp [rest_eq_iff]

/-- Native implementation of a unitary channel's non-padding term U tensor U*. -/
def unitaryLiouvilleCircuit (conv : GateConvention G) {q : ℕ}
    (C : EffectiveCircuit G q) : EffectiveCircuit G (q+q) :=
  tensorCircuit C (conjugateCircuit conv C)

lemma unitaryLiouvilleCircuit_matrix (conv : GateConvention G) {q : ℕ}
    (C : EffectiveCircuit G q) :
    (unitaryLiouvilleCircuit conv C).matrix =
      (Matrix.kronecker C.matrix (C.matrix.map conj)).submatrix
        (tensorBits q q) (tensorBits q q) := by
  rw [unitaryLiouvilleCircuit,tensorCircuit_matrix,conjugateCircuit_matrix]

lemma lift_neg {q k : ℕ} (p : Placement q k) (U : Operator k) :
    p.lift (-U) = -(p.lift U) := by
  ext x y
  simp [Placement.lift,Matrix.kronecker,Matrix.kroneckerMap_apply]

/-- Four copies of U tensor U*, then I,-I,I,-I, each an actual chronological list. -/
def unitaryTermCircuit (conv : GateConvention G) {q : ℕ}
    (hq : 0 < q) (C : EffectiveCircuit G q) (j : Fin 8) : EffectiveCircuit G (q+q) :=
  if j.val < 4 then unitaryLiouvilleCircuit conv C
  else if j.val % 2 = 0 then []
  else embedCircuit (placementOfEmbedding {
    toFun := fun _ : Fin 1 => (⟨0,by omega⟩ : Fin (q+q))
    inj' := fun _ _ _ => Subsingleton.elim _ _ }) (negativeCircuit conv 0)

lemma unitaryTermCircuit_matrix (conv : GateConvention G) {q : ℕ}
    (hq : 0 < q) (C : EffectiveCircuit G q) (j : Fin 8) :
    (unitaryTermCircuit conv hq C j).matrix =
      (unitaryPaddingTerms (Matrix.kronecker C.matrix (C.matrix.map conj)) j).submatrix
        (tensorBits q q) (tensorBits q q) := by
  fin_cases j <;>
    simp [unitaryTermCircuit,unitaryLiouvilleCircuit_matrix,unitaryPaddingTerms,
      EffectiveCircuit.matrix,embedCircuit_matrix,negativeCircuit_matrix,
      lift_neg,lift_one,Matrix.submatrix_neg,Matrix.submatrix_one_equiv]


lemma bit_cases (b : OperationalModel.Bit) : b = 0 ∨ b = 1 := by
  fin_cases b <;> simp

lemma x_matrix (conv : GateConvention G) :
    conv.X.matrix = Paper25.pauliX.submatrix oneBit oneBit := by
  rw [conv.X_matrix]
  ext i j
  have hi : i 0 = 0 ∨ i 0 = 1 := bit_cases (i 0)
  have hj : j 0 = 0 ∨ j 0 = 1 := bit_cases (j 0)
  rcases hi with hi | hi <;> rcases hj with hj | hj <;>
    simp [OperationalModel.LocalCompilation.pauliX,oneBit,Paper25.pauliX,hi,hj]

/-- Z is H-X-H, with the exact source Pauli convention. -/
def zCircuit (conv : GateConvention G) : EffectiveCircuit G 1 :=
  conv.hadamardAt 0 ++ flipCircuit conv 0 ++ conv.hadamardAt 0

lemma zCircuit_matrix (conv : GateConvention G) :
    (zCircuit conv).matrix = Paper25.pauliZ.submatrix oneBit oneBit := by
  simp only [zCircuit,EffectiveCircuit.matrix_append,conv.hadamard_matrix,
    flipCircuit_matrix,physicalHadamard,physicalFlip,Matrix.submatrix_mul_equiv]
  rw [←mul_assoc,hadamard_flip_hadamard]
  ext i j
  have hi : i 0 = 0 ∨ i 0 = 1 := bit_cases (i 0)
  have hj : j 0 = 0 ∨ j 0 = 1 := bit_cases (j 0)
  rcases hi with hi | hi <;> rcases hj with hj | hj <;>
    simp [Matrix.submatrix_apply,probeBasis,probeTensor,OneCleanQubit.tensorBasis,
      Matrix.fromBlocks,Matrix.one_apply,Paper25.pauliZ,oneBit,hi,hj] <;>
      exact Subsingleton.elim _ _

/-- ZX equals iY exactly, so no uncontrolled global-phase cancellation is used. -/
def iyCircuit (conv : GateConvention G) : EffectiveCircuit G 1 := conv.X ++ zCircuit conv

lemma iyCircuit_matrix (conv : GateConvention G) :
    (iyCircuit conv).matrix = (Complex.I • Paper25.pauliY).submatrix oneBit oneBit := by
  rw [iyCircuit,EffectiveCircuit.matrix_append,zCircuit_matrix,x_matrix,
    Matrix.submatrix_mul_equiv]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Paper25.pauliZ,Paper25.pauliX,Paper25.pauliY,Matrix.mul_apply,
      Fin.sum_univ_two,Matrix.smul_apply]

def pairIndex : Basis (1+1) ≃ (OperationalModel.Bit × OperationalModel.Bit) :=
  (tensorBits 1 1).trans (oneBit.prodCongr oneBit)

def resetLocalCircuit (conv : GateConvention G) (j : Fin 8) : EffectiveCircuit G (1+1) :=
  ![tensorCircuit [] [],tensorCircuit [] (zCircuit conv),
    tensorCircuit (zCircuit conv) [],tensorCircuit (zCircuit conv) (zCircuit conv),
    tensorCircuit conv.X conv.X,tensorCircuit conv.X (iyCircuit conv),
    tensorCircuit (iyCircuit conv) conv.X,tensorCircuit (iyCircuit conv) (iyCircuit conv)] j

lemma tensor_pair_matrix (C D : EffectiveCircuit G 1)
    (A B : Matrix OperationalModel.Bit OperationalModel.Bit ℂ)
    (hC : C.matrix = A.submatrix oneBit oneBit)
    (hD : D.matrix = B.submatrix oneBit oneBit) :
    (tensorCircuit C D).matrix = (Matrix.kronecker A B).submatrix pairIndex pairIndex := by
  rw [tensorCircuit_matrix,hC,hD]
  rfl

lemma resetLocalCircuit_matrix (conv : GateConvention G) (j : Fin 8) :
    (resetLocalCircuit conv j).matrix = (Paper25.resetTerms j).submatrix pairIndex pairIndex := by
  have hi : (1 : Operator 1) = Paper25.pauliI.submatrix oneBit oneBit := by
    simp only [Paper25.pauliI,Matrix.submatrix_one_equiv]
  fin_cases j
  · change (tensorCircuit [] []).matrix = (Matrix.kronecker Paper25.pauliI Paper25.pauliI).submatrix pairIndex pairIndex
    exact tensor_pair_matrix [] [] _ _ hi hi
  · change (tensorCircuit [] (zCircuit conv)).matrix = (Matrix.kronecker Paper25.pauliI Paper25.pauliZ).submatrix pairIndex pairIndex
    exact tensor_pair_matrix [] (zCircuit conv) _ _ hi (zCircuit_matrix conv)
  · change (tensorCircuit (zCircuit conv) []).matrix = (Matrix.kronecker Paper25.pauliZ Paper25.pauliI).submatrix pairIndex pairIndex
    exact tensor_pair_matrix (zCircuit conv) [] _ _ (zCircuit_matrix conv) hi
  · change (tensorCircuit (zCircuit conv) (zCircuit conv)).matrix = (Matrix.kronecker Paper25.pauliZ Paper25.pauliZ).submatrix pairIndex pairIndex
    exact tensor_pair_matrix (zCircuit conv) (zCircuit conv) _ _ (zCircuit_matrix conv) (zCircuit_matrix conv)
  · change (tensorCircuit conv.X conv.X).matrix = (Matrix.kronecker Paper25.pauliX Paper25.pauliX).submatrix pairIndex pairIndex
    exact tensor_pair_matrix conv.X conv.X _ _ (x_matrix conv) (x_matrix conv)
  · change (tensorCircuit conv.X (iyCircuit conv)).matrix =
      (Complex.I • Matrix.kronecker Paper25.pauliX Paper25.pauliY).submatrix pairIndex pairIndex
    rw [tensor_pair_matrix _ _ _ _ (x_matrix conv) (iyCircuit_matrix conv)]
    ext x y
    simp only [Matrix.submatrix_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  · change (tensorCircuit (iyCircuit conv) conv.X).matrix =
      (Complex.I • Matrix.kronecker Paper25.pauliY Paper25.pauliX).submatrix pairIndex pairIndex
    rw [tensor_pair_matrix _ _ _ _ (iyCircuit_matrix conv) (x_matrix conv)]
    ext x y
    simp only [Matrix.submatrix_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  · change (tensorCircuit (iyCircuit conv) (iyCircuit conv)).matrix =
      ((-1:ℂ) • Matrix.kronecker Paper25.pauliY Paper25.pauliY).submatrix pairIndex pairIndex
    rw [tensor_pair_matrix _ _ _ _ (iyCircuit_matrix conv) (iyCircuit_matrix conv)]
    ext x y
    simp only [Matrix.submatrix_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.smul_apply,smul_eq_mul]
    calc
      _ = (Complex.I * Complex.I) * (Paper25.pauliY (pairIndex x).1 (pairIndex y).1 *
        Paper25.pauliY (pairIndex x).2 (pairIndex y).2) := by ring
      _ = _ := by rw [Complex.I_mul_I]

lemma dephaseLocalCircuit_matrix_aux :
    Paper25.dephasingTerms =
      ![Matrix.kronecker Paper25.pauliI Paper25.pauliI,
        Matrix.kronecker Paper25.pauliI Paper25.pauliI,
        Matrix.kronecker Paper25.pauliZ Paper25.pauliZ,
        Matrix.kronecker Paper25.pauliZ Paper25.pauliZ,
        Matrix.kronecker Paper25.pauliI Paper25.pauliI,
        -Matrix.kronecker Paper25.pauliI Paper25.pauliI,
        Matrix.kronecker Paper25.pauliI Paper25.pauliI,
        -Matrix.kronecker Paper25.pauliI Paper25.pauliI] := rfl

def dephaseLocalCircuit (conv : GateConvention G) (j : Fin 8) : EffectiveCircuit G (1+1) :=
  if j.val = 2 ∨ j.val = 3 then tensorCircuit (zCircuit conv) (zCircuit conv)
  else if j.val = 5 ∨ j.val = 7 then negativeCircuit conv 1 else []

lemma dephaseLocalCircuit_matrix (conv : GateConvention G) (j : Fin 8) :
    (dephaseLocalCircuit conv j).matrix =
      (Paper25.dephasingTerms j).submatrix pairIndex pairIndex := by
  fin_cases j
  · change (1 : Operator 2) = (Matrix.kronecker Paper25.pauliI Paper25.pauliI).submatrix pairIndex pairIndex
    simp only [Paper25.pauliI,Matrix.kronecker,Matrix.one_kronecker_one,Matrix.submatrix_one_equiv]
  · change (1 : Operator 2) = (Matrix.kronecker Paper25.pauliI Paper25.pauliI).submatrix pairIndex pairIndex
    simp only [Paper25.pauliI,Matrix.kronecker,Matrix.one_kronecker_one,Matrix.submatrix_one_equiv]
  · change (tensorCircuit (zCircuit conv) (zCircuit conv)).matrix =
      (Matrix.kronecker Paper25.pauliZ Paper25.pauliZ).submatrix pairIndex pairIndex
    rw [tensorCircuit_matrix,zCircuit_matrix]
    rfl
  · change (tensorCircuit (zCircuit conv) (zCircuit conv)).matrix =
      (Matrix.kronecker Paper25.pauliZ Paper25.pauliZ).submatrix pairIndex pairIndex
    rw [tensorCircuit_matrix,zCircuit_matrix]
    rfl
  · change (1 : Operator 2) = (Matrix.kronecker Paper25.pauliI Paper25.pauliI).submatrix pairIndex pairIndex
    simp only [Paper25.pauliI,Matrix.kronecker,Matrix.one_kronecker_one,Matrix.submatrix_one_equiv]
  · change (negativeCircuit conv 1).matrix =
      (-Matrix.kronecker Paper25.pauliI Paper25.pauliI).submatrix pairIndex pairIndex
    simp only [negativeCircuit_matrix,Paper25.pauliI,Matrix.kronecker,
      Matrix.one_kronecker_one]
    change (-1 : Operator 2) = -((1 : Matrix (OperationalModel.Bit × OperationalModel.Bit) _ ℂ).submatrix pairIndex pairIndex)
    rw [Matrix.submatrix_one_equiv]
  · change (1 : Operator 2) = (Matrix.kronecker Paper25.pauliI Paper25.pauliI).submatrix pairIndex pairIndex
    simp only [Paper25.pauliI,Matrix.kronecker,Matrix.one_kronecker_one,Matrix.submatrix_one_equiv]
  · change (negativeCircuit conv 1).matrix =
      (-Matrix.kronecker Paper25.pauliI Paper25.pauliI).submatrix pairIndex pairIndex
    simp only [negativeCircuit_matrix,Paper25.pauliI,Matrix.kronecker,
      Matrix.one_kronecker_one]
    change (-1 : Operator 2) = -((1 : Matrix (OperationalModel.Bit × OperationalModel.Bit) _ ℂ).submatrix pairIndex pairIndex)
    rw [Matrix.submatrix_one_equiv]


lemma eightTerms_mpr_terms {a : Type*} [Fintype a] [DecidableEq a]
    {S T : Matrix a a ℂ} (hST : S = T) (h : EightTerms S = EightTerms T) (A : EightTerms T) :
    (h.mpr A).terms = A.terms := by
  subst T
  rfl

lemma relabel_terms {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {C : KrausChannel a} (A : EightChannelTerms C) (e : b ≃ a) (j : Fin 8) :
    (A.relabel e).terms j = (A.terms j).submatrix (e.prodCongr e) (e.prodCongr e) := by
  unfold EightChannelTerms.relabel
  simp only [eightTerms_mpr_terms rfl,eightTerms_mpr_terms (relabel_liouville e C),EightTerms.reindex]

lemma extendRight_terms {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {C : KrausChannel a} (A : EightChannelTerms C) (j : Fin 8) :
    (A.extendRight (ρ := b)).terms j =
      (Matrix.kronecker (A.terms j) (1 : Matrix (b×b) (b×b) ℂ)).submatrix
        reshuffleEquiv reshuffleEquiv := by
  unfold EightChannelTerms.extendRight
  simp only [eightTerms_mpr_terms rfl,eightTerms_mpr_terms (extendRight_liouville C),
    EightTerms.reindex,EightTerms.tensorRight]

lemma placement_terms {q k : ℕ} {C : KrausChannel (Basis k)}
    (A : EightChannelTerms C) (p : Placement q k) (j : Fin 8) :
    (A.placement p).terms j = liftLiouville p (A.terms j) := by
  rw [EightChannelTerms.placement,relabel_terms,extendRight_terms]
  rfl

def resetPlacedCircuit (conv : GateConvention G) {q : ℕ} (p : Placement q 1)
    (j : Fin 8) : EffectiveCircuit G (q+q) :=
  embedCircuit (doublePlacement p) (resetLocalCircuit conv j)

lemma resetPlacedCircuit_matrix (conv : GateConvention G) {q : ℕ} (p : Placement q 1)
    (j : Fin 8) :
    (resetPlacedCircuit conv p j).matrix =
      ((SourcePrimitive.reset p).encoding.terms j).submatrix (tensorBits q q) (tensorBits q q) := by
  rw [resetPlacedCircuit,embedCircuit_matrix,resetLocalCircuit_matrix]
  change (doublePlacement p).lift
    (((Paper25.resetTerms j).submatrix (oneBit.prodCongr oneBit) (oneBit.prodCongr oneBit)).submatrix
      (tensorBits 1 1) (tensorBits 1 1)) = _
  rw [doublePlacement_lift]
  simp only [SourcePrimitive.encoding,placement_terms,relabel_terms,dephaseTerms,resetTermsWitness]

def dephasePlacedCircuit (conv : GateConvention G) {q : ℕ} (p : Placement q 1)
    (j : Fin 8) : EffectiveCircuit G (q+q) :=
  embedCircuit (doublePlacement p) (dephaseLocalCircuit conv j)

lemma dephasePlacedCircuit_matrix (conv : GateConvention G) {q : ℕ} (p : Placement q 1)
    (j : Fin 8) :
    (dephasePlacedCircuit conv p j).matrix =
      ((SourcePrimitive.dephase p).encoding.terms j).submatrix (tensorBits q q) (tensorBits q q) := by
  rw [dephasePlacedCircuit,embedCircuit_matrix,dephaseLocalCircuit_matrix]
  change (doublePlacement p).lift
    (((Paper25.dephasingTerms j).submatrix (oneBit.prodCongr oneBit) (oneBit.prodCongr oneBit)).submatrix
      (tensorBits 1 1) (tensorBits 1 1)) = _
  rw [doublePlacement_lift]
  simp only [SourcePrimitive.encoding,placement_terms,relabel_terms,dephaseTerms,resetTermsWitness]

lemma unitaryGateTerm_matrix (conv : GateConvention G) {q : ℕ} (hq : 0 < q)
    (g : EffectiveLocalGate G q) (j : Fin 8) :
    (unitaryTermCircuit conv hq [g] j).matrix =
      ((SourcePrimitive.unitary g.placement (G.matrix g.kind g.payload)
        (Matrix.mem_unitaryGroup_iff'.mpr (G.unitary g.kind g.payload).1)).encoding.terms j).submatrix
          (tensorBits q q) (tensorBits q q) := by
  rw [unitaryTermCircuit_matrix]
  simp only [EffectiveCircuit.matrix,one_mul]
  change (unitaryPaddingTerms (Matrix.kronecker g.matrix (g.matrix.map conj)) j).submatrix
      (tensorBits q q) (tensorBits q q) = _
  rw [← ElementaryEncoding.unitary_liouville]
  rfl


lemma extendLeft_terms {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {C : KrausChannel a} (A : EightChannelTerms C) (j : Fin 8) :
    (A.extendLeft (ρ := b)).terms j =
      (Matrix.kronecker (1 : Matrix (b×b) (b×b) ℂ) (A.terms j)).submatrix
        reshuffleEquiv reshuffleEquiv := by
  unfold EightChannelTerms.extendLeft
  simp only [eightTerms_mpr_terms rfl,eightTerms_mpr_terms (extendLeft_liouville C),
    EightTerms.reindex,EightTerms.tensorLeft]

def secondPosition : Fin 1 ↪ Fin 2 where
  toFun _ := 1
  inj' _ _ _ := Subsingleton.elim _ _

def secondPlacement : Placement 2 1 := placementOfEmbedding secondPosition

lemma second_inactive (x y : Basis 2) :
    Inactive (active secondPlacement) x y ↔ x 0 = y 0 := by
  simp only [secondPlacement,active_placementOfEmbedding_eq]
  constructor
  · intro h
    apply h 0
    rintro ⟨i,hi⟩
    norm_num [secondPosition] at hi
  · intro h j hj
    fin_cases j
    · exact h
    · exact False.elim (hj ⟨0,rfl⟩)

lemma second_liftLiouville (S : Matrix (OperationalModel.Bit × OperationalModel.Bit)
    (OperationalModel.Bit × OperationalModel.Bit) ℂ) :
    liftLiouville secondPlacement (S.submatrix (oneBit.prodCongr oneBit) (oneBit.prodCongr oneBit)) =
      ((Matrix.kronecker (1 : Matrix (OperationalModel.Bit × OperationalModel.Bit)
        (OperationalModel.Bit × OperationalModel.Bit) ℂ) S).submatrix reshuffleEquiv reshuffleEquiv).submatrix
          ((finTwoArrowEquiv OperationalModel.Bit).prodCongr (finTwoArrowEquiv OperationalModel.Bit))
          ((finTwoArrowEquiv OperationalModel.Bit).prodCongr (finTwoArrowEquiv OperationalModel.Bit)) := by
  ext ⟨x,x'⟩ ⟨y,y'⟩
  simp only [liftLiouville,Matrix.submatrix_apply,Equiv.prodCongr_apply,
    Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,reshuffleEquiv]
  change S (x 1,x' 1) (y 1,y' 1) *
    (if ((secondPlacement.split x).2,(secondPlacement.split x').2) =
      ((secondPlacement.split y).2,(secondPlacement.split y').2) then 1 else 0) = _
  simp only [Prod.mk.injEq,rest_eq_iff,second_inactive]
  change S (x 1,x' 1) (y 1,y' 1) * (if x 0 = y 0 ∧ x' 0 = y' 0 then 1 else 0) =
    (if (x 0,x' 0) = (y 0,y' 0) then 1 else 0) * S (x 1,x' 1) (y 1,y' 1)
  simp only [Prod.mk.injEq,mul_comm]

def outcomeResetCircuit (conv : GateConvention G) {q : ℕ} (p : Placement q 2)
    (j : Fin 8) : EffectiveCircuit G (q+q) :=
  embedCircuit (doublePlacement p) (resetPlacedCircuit conv secondPlacement j)

lemma outcomeResetCircuit_matrix (conv : GateConvention G) {q : ℕ} (p : Placement q 2)
    (j : Fin 8) :
    (outcomeResetCircuit conv p j).matrix =
      ((SourcePrimitive.outcomeReset p).encoding.terms j).submatrix (tensorBits q q) (tensorBits q q) := by
  rw [outcomeResetCircuit,embedCircuit_matrix,resetPlacedCircuit_matrix]
  simp only [SourcePrimitive.encoding,placement_terms,relabel_terms,resetTermsWitness]
  rw [doublePlacement_lift,second_liftLiouville]
  simp only [liftTwoTerms,placement_terms,relabel_terms,extendLeft_terms,resetTermsWitness]

def outcomeDephaseCircuit (conv : GateConvention G) {q : ℕ} (p : Placement q 2)
    (j : Fin 8) : EffectiveCircuit G (q+q) :=
  embedCircuit (doublePlacement p) (dephasePlacedCircuit conv secondPlacement j)

lemma outcomeDephaseCircuit_matrix (conv : GateConvention G) {q : ℕ} (p : Placement q 2)
    (j : Fin 8) :
    (outcomeDephaseCircuit conv p j).matrix =
      ((SourcePrimitive.outcomeDephase p).encoding.terms j).submatrix (tensorBits q q) (tensorBits q q) := by
  rw [outcomeDephaseCircuit,embedCircuit_matrix,dephasePlacedCircuit_matrix]
  simp only [SourcePrimitive.encoding,placement_terms,relabel_terms,dephaseTerms]
  rw [doublePlacement_lift,second_liftLiouville]
  simp only [liftTwoTerms,placement_terms,relabel_terms,extendLeft_terms,dephaseTerms]


lemma cnot_matrix (conv : GateConvention G) :
    conv.CNOT.matrix = KrausChannel.copyGate.submatrix
      (finTwoArrowEquiv OperationalModel.Bit) (finTwoArrowEquiv OperationalModel.Bit) := by
  rw [conv.CNOT_matrix]
  ext x y
  have ht : (fun i : Fin 1 => x i.succ) = (fun i : Fin 1 => y i.succ) ↔ x 1 = y 1 := by
    constructor
    · intro h; exact congrFun h 0
    · intro h; funext i; fin_cases i; exact h
  rcases bit_cases (x 0) with hx | hx <;> rcases bit_cases (y 0) with hy | hy <;>
    rcases bit_cases (x 1) with hx1 | hx1 <;> rcases bit_cases (y 1) with hy1 | hy1 <;>
    simp [physicalControl,probeBasis,probeTensor,OneCleanQubit.tensorBasis,
      OneCleanQubit.controlled,Matrix.fromBlocks,Matrix.one_apply,
      OperationalModel.LocalCompilation.pauliX,KrausChannel.copyGate,
      finTwoArrowEquiv,hx,hy,hx1,hy1,ht]

lemma padding_reindex {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (e : a ≃ b) (S : Matrix b b ℂ) (j : Fin 8) :
    (unitaryPaddingTerms S j).submatrix e e = unitaryPaddingTerms (S.submatrix e e) j := by
  fin_cases j <;> first | rfl | skip
  all_goals ext x y
  all_goals
    first
    | change (if e x = e y then (1:ℂ) else 0) = if x = y then 1 else 0
      simp only [e.injective.eq_iff]
    | change -(if e x = e y then (1:ℂ) else 0) = -(if x = y then 1 else 0)
      simp only [e.injective.eq_iff]

lemma copyLocalCircuit_matrix (conv : GateConvention G) (j : Fin 8) :
    (unitaryTermCircuit conv (by decide : 0 < 2) conv.CNOT j).matrix =
      (((unitaryTerms KrausChannel.copyGate
        (Matrix.mem_unitaryGroup_iff'.mpr KrausChannel.copyGate_unitary)).relabel
          (finTwoArrowEquiv OperationalModel.Bit)).terms j).submatrix
            (tensorBits 2 2) (tensorBits 2 2) := by
  rw [unitaryTermCircuit_matrix,relabel_terms]
  simp only [unitaryTerms,ElementaryEncoding.unitary_liouville,padding_reindex,cnot_matrix]
  rfl

def copyPlacedCircuit (conv : GateConvention G) {q : ℕ} (p : Placement q 2)
    (j : Fin 8) : EffectiveCircuit G (q+q) :=
  embedCircuit (doublePlacement p) (unitaryTermCircuit conv (by decide : 0 < 2) conv.CNOT j)

lemma copyPlacedCircuit_matrix (conv : GateConvention G) {q : ℕ} (p : Placement q 2)
    (j : Fin 8) :
    (copyPlacedCircuit conv p j).matrix =
      ((SourcePrimitive.copyBasis p).encoding.terms j).submatrix (tensorBits q q) (tensorBits q q) := by
  rw [copyPlacedCircuit,embedCircuit_matrix,copyLocalCircuit_matrix,doublePlacement_lift]
  simp only [SourcePrimitive.encoding,liftTwoTerms,placement_terms]


/-- A fixed per-source-step bound; it depends only on the elementary convention. -/
def sourceTermBound (conv : GateConvention G) : ℕ :=
  (conv.bound+1)*(conv.CNOT.length+1) + 8*(conv.X.length+conv.bound)

lemma unitaryTermCircuit_length (conv : GateConvention G) {q : ℕ}
    (hq : 0 < q) (C : EffectiveCircuit G q) (j : Fin 8) :
    (unitaryTermCircuit conv hq C j).length ≤
      (conv.bound+1)*C.length + 4*(conv.X.length+conv.bound) := by
  unfold unitaryTermCircuit
  split_ifs
  · simp only [unitaryLiouvilleCircuit,tensorCircuit_length]
    have h := conjugateCircuit_length conv C
    nlinarith
  · simp
  · rw [embedCircuit_length]
    have h := negativeCircuit_length conv 0
    omega

lemma zCircuit_length (conv : GateConvention G) :
    (zCircuit conv).length ≤ conv.X.length+2*conv.bound := by
  simp only [zCircuit,List.length_append,flipCircuit,embedCircuit_length]
  have h := conv.hadamard_length 0
  omega

lemma iyCircuit_length (conv : GateConvention G) :
    (iyCircuit conv).length ≤ 2*(conv.X.length+conv.bound) := by
  simp only [iyCircuit,List.length_append]
  have h := zCircuit_length conv
  omega

lemma resetLocalCircuit_length (conv : GateConvention G) (j : Fin 8) :
    (resetLocalCircuit conv j).length ≤ 4*(conv.X.length+conv.bound) := by
  have hz := zCircuit_length conv
  have hy := iyCircuit_length conv
  fin_cases j <;> change (tensorCircuit _ _).length ≤ _
  all_goals rw [tensorCircuit_length]
  all_goals try simp only [List.length_nil]
  all_goals omega

lemma dephaseLocalCircuit_length (conv : GateConvention G) (j : Fin 8) :
    (dephaseLocalCircuit conv j).length ≤ 4*(conv.X.length+conv.bound) := by
  unfold dephaseLocalCircuit
  split_ifs
  · rw [tensorCircuit_length]
    have h := zCircuit_length conv
    omega
  · exact negativeCircuit_length conv 1
  · simp

/-- A primitive carries its actual local lists and their proved relation to the
pre-existing eight-term witness. This record is constructed below for every
real source-operation branch, rather than assumed for an arbitrary matrix. -/
structure NativePrimitive (conv : GateConvention G) (q : ℕ) where
  primitive : SourcePrimitive q
  terms : Fin 8 → EffectiveCircuit G (q+q)
  matrix : ∀ j, (terms j).matrix =
    (primitive.encoding.terms j).submatrix (tensorBits q q) (tensorBits q q)
  length : ∀ j, (terms j).length ≤ sourceTermBound conv

def nativeGate (conv : GateConvention G) {q : ℕ} (hq : 0 < q)
    (g : EffectiveLocalGate G q) : NativePrimitive conv q where
  primitive := .unitary g.placement (G.matrix g.kind g.payload)
    (Matrix.mem_unitaryGroup_iff'.mpr (G.unitary g.kind g.payload).1)
  terms := unitaryTermCircuit conv hq [g]
  matrix := unitaryGateTerm_matrix conv hq g
  length j := by
    have h := unitaryTermCircuit_length conv hq [g] j
    simp only [List.length_cons,List.length_nil] at h
    unfold sourceTermBound
    nlinarith

def nativeReset (conv : GateConvention G) {q : ℕ} (p : Placement q 1) : NativePrimitive conv q where
  primitive := .reset p
  terms := resetPlacedCircuit conv p
  matrix := resetPlacedCircuit_matrix conv p
  length j := by
    rw [resetPlacedCircuit,embedCircuit_length]
    exact (resetLocalCircuit_length conv j).trans (by unfold sourceTermBound;omega)

def nativeDephase (conv : GateConvention G) {q : ℕ} (p : Placement q 1) : NativePrimitive conv q where
  primitive := .dephase p
  terms := dephasePlacedCircuit conv p
  matrix := dephasePlacedCircuit_matrix conv p
  length j := by
    rw [dephasePlacedCircuit,embedCircuit_length]
    exact (dephaseLocalCircuit_length conv j).trans (by unfold sourceTermBound;omega)

def nativeOutcomeReset (conv : GateConvention G) {q : ℕ} (p : Placement q 2) : NativePrimitive conv q where
  primitive := .outcomeReset p
  terms := outcomeResetCircuit conv p
  matrix := outcomeResetCircuit_matrix conv p
  length j := by
    simp only [outcomeResetCircuit,resetPlacedCircuit,embedCircuit_length]
    exact (resetLocalCircuit_length conv j).trans (by unfold sourceTermBound;omega)

def nativeOutcomeDephase (conv : GateConvention G) {q : ℕ} (p : Placement q 2) : NativePrimitive conv q where
  primitive := .outcomeDephase p
  terms := outcomeDephaseCircuit conv p
  matrix := outcomeDephaseCircuit_matrix conv p
  length j := by
    simp only [outcomeDephaseCircuit,dephasePlacedCircuit,embedCircuit_length]
    exact (dephaseLocalCircuit_length conv j).trans (by unfold sourceTermBound;omega)

def nativeCopy (conv : GateConvention G) {q : ℕ} (p : Placement q 2) : NativePrimitive conv q where
  primitive := .copyBasis p
  terms := copyPlacedCircuit conv p
  matrix := copyPlacedCircuit_matrix conv p
  length j := by
    rw [copyPlacedCircuit,embedCircuit_length]
    have h := unitaryTermCircuit_length conv (by decide : 0 < 2) conv.CNOT j
    unfold sourceTermBound
    nlinarith

/-- Each retained measurement emits reset-outcome, copy-basis, dephase-outcome,
in exactly the same chronology as the previously proved semantic expansion. -/
def expandNativeOp (conv : GateConvention G) {q : ℕ} (hq : 0 < q) :
    EffectiveSourceOp G q → List (NativePrimitive conv q)
  | .gate g => [nativeGate conv hq g]
  | .dephase p => [nativeDephase conv p]
  | .reset p => [nativeReset conv p]
  | .measurement p => [nativeOutcomeReset conv p,nativeCopy conv p,nativeOutcomeDephase conv p]

lemma expandNativeOp_map (conv : GateConvention G) {q : ℕ} (hq : 0 < q)
    (g : EffectiveSourceOp G q) :
    (expandNativeOp conv hq g).map NativePrimitive.primitive = expandEffectiveSourceOp g := by
  cases g <;> rfl

def expandNativeCircuit (conv : GateConvention G) {q : ℕ} (hq : 0 < q)
    (C : EffectiveSourceCircuit G q) : List (NativePrimitive conv q) :=
  C.flatMap (expandNativeOp conv hq)

lemma expandNativeCircuit_map (conv : GateConvention G) {q : ℕ} (hq : 0 < q)
    (C : EffectiveSourceCircuit G q) :
    (expandNativeCircuit conv hq C).map NativePrimitive.primitive = expandEffectiveSourceCircuit C := by
  induction C with
  | nil => rfl
  | cons g gs ih =>
    simpa only [expandNativeCircuit,expandEffectiveSourceCircuit,List.flatMap_cons,List.map_append,
      expandNativeOp_map] using congrArg (fun tail => expandEffectiveSourceOp g ++ tail) ih

/-- Indexed actual native terms, padded by the same identity-channel convention. -/
def nativeTermAt (conv : GateConvention G) {q : ℕ} (hq : 0 < q)
    (C : EffectiveSourceCircuit G q) (t : ℕ) (j : Fin 8) : EffectiveCircuit G (q+q) :=
  match (expandNativeCircuit conv hq C)[t]? with
  | some g => g.terms j
  | none => unitaryTermCircuit conv hq [] j

lemma primitiveEncodingAt_terms {q : ℕ} (xs : List (SourcePrimitive q)) (t : ℕ) :
    (primitiveEncodingAt xs t).terms =
      match xs[t]? with
      | some g => g.encoding.terms
      | none => (unitaryTerms (1 : Operator q) (Matrix.unitaryGroup (Basis q) ℂ).one_mem).terms := by
  induction xs generalizing t with
  | nil => rfl
  | cons g gs ih =>
    cases t with
    | zero => rfl
    | succ t => exact ih t

theorem nativeTermAt_matrix (conv : GateConvention G) {q : ℕ} (hq : 0 < q)
    (C : EffectiveSourceCircuit G q) (t : ℕ) (j : Fin 8) :
    (nativeTermAt conv hq C t j).matrix =
      ((primitiveEncodingAt (expandEffectiveSourceCircuit C) t).terms j).submatrix
        (tensorBits q q) (tensorBits q q) := by
  have hm := expandNativeCircuit_map conv hq C
  cases h : (expandNativeCircuit conv hq C)[t]? with
  | none =>
    have hh : (expandEffectiveSourceCircuit C)[t]? = none := by
      rw [←hm,List.getElem?_map,h];rfl
    simp only [nativeTermAt,h]
    rw [unitaryTermCircuit_matrix]
    rw [primitiveEncodingAt_terms,hh]
    simp only [EffectiveCircuit.matrix,unitaryTerms,ElementaryEncoding.unitary_liouville]
  | some g =>
    have hh : (expandEffectiveSourceCircuit C)[t]? = some g.primitive := by
      rw [←hm,List.getElem?_map,h];rfl
    simp only [nativeTermAt,h]
    rw [g.matrix]
    rw [primitiveEncodingAt_terms,hh]

theorem nativeTermAt_length (conv : GateConvention G) {q : ℕ} (hq : 0 < q)
    (C : EffectiveSourceCircuit G q) (t : ℕ) (j : Fin 8) :
    (nativeTermAt conv hq C t j).length ≤ sourceTermBound conv := by
  unfold nativeTermAt
  split
  · exact NativePrimitive.length _ _
  · have h := unitaryTermCircuit_length conv hq [] j
    simp only [List.length_nil,mul_zero,zero_add] at h
    exact h.trans (by unfold sourceTermBound;omega)

open SourceCoordinates

def sourceQubits (S : EffectiveSourceComputation G) : ℕ := S.workQubits+S.catalystQubits

lemma sourceQubits_pos (S : EffectiveSourceComputation G) : 0 < sourceQubits S := by
  have h := S.outputQubit.isLt
  unfold sourceQubits
  omega

/-- The data interpretation used by the final native history circuit: two
physical source registers, read in the exact canonical Liouville coordinates. -/
def nativeDataIndex (S : EffectiveSourceComputation G) :
    Basis (sourceQubits S+sourceQubits S) ≃
      (Fin ((Fintype.card (StatePreparation.WorkSpace (restQubits S)))^2) ×
        SourceSimulation.CatalystData S.catalystQubits) :=
  (tensorBits (sourceQubits S) (sourceQubits S)).trans (canonicalRawOperatorIndex S).symm

def canonicalNativeTerm (conv : GateConvention G) (S : EffectiveSourceComputation G)
    (t : ℕ) (j : Fin 8) : EffectiveCircuit G (sourceQubits S+sourceQubits S) :=
  nativeTermAt conv (sourceQubits_pos S) S.gates t j

/-- Every native term is exactly the already-used canonicalK term after the
explicit doubled-register interpretation, including measurement branches. -/
theorem canonicalNativeTerm_matrix (conv : GateConvention G) (S : EffectiveSourceComputation G)
    (t : ℕ) (j : Fin 8) :
    (canonicalNativeTerm conv S t j).matrix =
      (canonicalK S t j).submatrix (nativeDataIndex S) (nativeDataIndex S) := by
  rw [canonicalNativeTerm,nativeTermAt_matrix]
  ext x y
  simp only [canonicalK,primitiveTermsAt,EightTerms.reindex,Matrix.submatrix_apply,
    nativeDataIndex,Equiv.trans_apply]
  exact congrArg₂ ((primitiveEncodingAt (expanded S) t).terms j)
    ((canonicalRawOperatorIndex S).apply_symm_apply _).symm
    ((canonicalRawOperatorIndex S).apply_symm_apply _).symm

theorem canonicalNativeTerm_length (conv : GateConvention G) (S : EffectiveSourceComputation G)
    (t : ℕ) (j : Fin 8) :
    (canonicalNativeTerm conv S t j).length ≤ sourceTermBound conv :=
  nativeTermAt_length conv (sourceQubits_pos S) S.gates t j

end Paper25.SourceTermCompilation

import Paper25.LocalCompilation
import Paper25.MatrixCompilationNorm
import Paper25.GlobalFilterError
import Paper25.SelectedPreparation
import Paper25.SelectorArithmetic
import Paper25.FourierCompilation

/-!
# Actual native coherent-filter circuits

The register order is phase bits, one rotation bit, then walk data. The native
list consists of an actual QFT list, enumerated controlled powers of the native
walk, actual represented rational label rotations, and their literal inverses.
The component approximation bounds below are propagated in the Euclidean
operator norm without any factor from the data-register dimension.
-/
noncomputable section
open Matrix
open scoped ComplexConjugate Matrix.Norms.L2Operator
namespace Paper25.OperationalModel.CoherentCompilation
open LocalCompilation MatrixCompilationNorm
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000

lemma tensorBits_register (q r : ℕ) : tensorBits q r = registerBasis q r := by
  apply Equiv.ext
  intro x
  rfl

lemma reindex_kronecker {a b c d : Type*} [Fintype a] [Fintype b]
    [Fintype c] [Fintype d] (e : a ≃ b) (f : c ≃ d)
    (A : Matrix b b ℂ) (B : Matrix d d ℂ) :
    kronecker (A.submatrix e e) (B.submatrix f f) =
      (kronecker A B).submatrix (e.prodCongr f) (e.prodCongr f) := by
  ext i j
  rfl

lemma reindex_select {a b c d : Type*} [Fintype a] [Fintype b]
    [Fintype c] [Fintype d] [DecidableEq a] [DecidableEq b]
    (e : a ≃ b) (f : c ≃ d) (K : b → Matrix d d ℂ) :
    selectMatrix (fun i => (K (e i)).submatrix f f) =
      (selectMatrix K).submatrix (e.prodCongr f) (e.prodCongr f) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  simp [selectMatrix, e.injective.eq_iff]

lemma reindex_pow {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (A : Matrix b b ℂ) (r : ℕ) :
    (A.submatrix e e)^r = (A^r).submatrix e e := by
  induction r with
  | zero => simp
  | succ r ih => rw [pow_succ, ih, pow_succ, Matrix.submatrix_mul_equiv]

lemma unitary_power_error {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A ∈ Matrix.unitaryGroup n ℂ)
    (hB : B ∈ Matrix.unitaryGroup n ℂ) (u : ℝ) (hAB : ‖A-B‖ ≤ u) (r : ℕ) :
    ‖A^r-B^r‖ ≤ (r:ℝ)*u := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, pow_succ]
    have h := unitary_product_error_le (A^r) (B^r) A B
      ((Matrix.unitaryGroup n ℂ).pow_mem hB r) hA ((r:ℝ)*u) u ih hAB
    convert h using 1 <;> push_cast <;> ring

/-- The actual native one-qubit rotation is placed immediately before walk data. -/
def labelCircuit {G : EffectiveGateSet} (conv : GateConvention G) (ell q : ℕ)
    (angle : Basis ell → RationalRep) : EffectiveCircuit G (ell+(1+q)) :=
  selectCircuit conv (fun j => tensorCircuit (conv.rotationRep (angle j)) ([] : EffectiveCircuit G q))

/-- Native walk on the data register, leaving the rotation bit untouched. -/
def rotationSpectator {G : EffectiveGateSet} {q : ℕ} (walk : EffectiveCircuit G q) :
    EffectiveCircuit G (1+q) := tensorCircuit ([] : EffectiveCircuit G 1) walk

/-- The actual PE list uses the binary value of the phase register as exponent. -/
def nativePE {G : EffectiveGateSet} (conv : GateConvention G) (ell : ℕ) {q : ℕ}
    (walk : EffectiveCircuit G q) (fourier : EffectiveCircuit G (ell+(1+q))) :
    EffectiveCircuit G (ell+(1+q)) :=
  phaseEstimationCircuit conv (fun j => (SelectedFilter.bitsBinaryIndex ell j).val)
    (rotationSpectator walk) fourier

/-- The full physical gate list: PE, represented label SELECT, inverse PE. -/
def nativeFilter {G : EffectiveGateSet} (conv : GateConvention G) (ell : ℕ) {q : ℕ}
    (walk : EffectiveCircuit G q) (fourier : EffectiveCircuit G (ell+(1+q)))
    (angle : Basis ell → RationalRep) : EffectiveCircuit G (ell+(1+q)) :=
  coherentFilterCircuit conv (nativePE conv ell walk fourier) (labelCircuit conv ell q angle)

lemma labelCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) (ell q : ℕ)
    (angle : Basis ell → RationalRep) :
    (labelCircuit conv ell q angle).matrix =
      (selectMatrix (fun j => (kronecker (rotationMatrix (angle j).value) (1 : Operator q)).submatrix
        (tensorBits 1 q) (tensorBits 1 q))).submatrix
          (registerBasis ell (1+q)) (registerBasis ell (1+q)) := by
  simp only [labelCircuit, selectCircuit_matrix, tensorCircuit_matrix, conv.rotationRep_matrix]
  rfl

/-- Ideal physical rotation SELECT, with exactly the same wire placement. -/
def physicalLabel (ell q : ℕ) (g : Basis ell → ℝ) : Operator (ell+(1+q)) :=
  (selectMatrix (fun j => (kronecker ((amplitudeRotation (g j)).submatrix oneBit oneBit)
    (1 : Operator q)).submatrix (tensorBits 1 q) (tensorBits 1 q))).submatrix
      (registerBasis ell (1+q)) (registerBasis ell (1+q))

lemma labelCircuit_error {G : EffectiveGateSet} (conv : GateConvention G) (ell q : ℕ)
    (angle : Basis ell → RationalRep) (g : Basis ell → ℝ) (σ : ℝ) (hσ : 0 ≤ σ)
    (herr : ∀ j, ‖angleRotation (angle j).value - amplitudeRotation (g j)‖ ≤ σ) :
    ‖(labelCircuit conv ell q angle).matrix - physicalLabel ell q g‖ ≤ σ := by
  rw [labelCircuit_matrix, physicalLabel, submatrix_equiv_error]
  apply selectMatrix_error _ _ σ hσ
  intro j
  rw [submatrix_equiv_error]
  apply (tensor_identity_error _ _).trans
  rw [rotationMatrix_eq_angleRotation, submatrix_equiv_error]
  exact herr j

/-- Ideal physical controlled powers, before either Fourier transform. -/
def physicalPowers (ell q : ℕ) (W : Operator (1+q)) : Operator (ell+(1+q)) :=
  (selectMatrix (fun j => W^(SelectedFilter.bitsBinaryIndex ell j).val)).submatrix
    (registerBasis ell (1+q)) (registerBasis ell (1+q))

def physicalPE (ell q : ℕ) (W : Operator (1+q)) : Operator (ell+(1+q)) :=
  (FourierCompilation.qftOnData ell (1+q)).conjTranspose * physicalPowers ell q W *
    FourierCompilation.qftOnData ell (1+q)

lemma physicalPowers_unitary (ell q : ℕ) (W : Operator (1+q))
    (hW : W ∈ Matrix.unitaryGroup (Basis (1+q)) ℂ) :
    physicalPowers ell q W ∈ Matrix.unitaryGroup (Basis (ell+(1+q))) ℂ := by
  exact unitary_reindex_matrix (registerBasis ell (1+q)) _
    (selectMatrix_unitary (fun j : Basis ell => W^(SelectedFilter.bitsBinaryIndex ell j).val)
      (fun j => (Matrix.unitaryGroup (Basis (1+q)) ℂ).pow_mem hW _))

lemma physicalPowers_error (ell q : ℕ) (W Z : Operator (1+q))
    (hW : W ∈ Matrix.unitaryGroup (Basis (1+q)) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Basis (1+q)) ℂ) (u : ℝ) (hu : 0 ≤ u)
    (herr : ‖W-Z‖ ≤ u) :
    ‖physicalPowers ell q W - physicalPowers ell q Z‖ ≤ (2^ell:ℕ)*u := by
  rw [physicalPowers, physicalPowers, submatrix_equiv_error]
  apply selectMatrix_error _ _ _ (by positivity)
  intro j
  apply (unitary_power_error W Z hW hZ u herr _).trans
  apply mul_le_mul_of_nonneg_right _ hu
  exact_mod_cast (SelectedFilter.bitsBinaryIndex ell j).isLt.le

lemma qftOnData_unitary (ell q : ℕ) :
    FourierCompilation.qftOnData ell q ∈ Matrix.unitaryGroup (Basis (ell+q)) ℂ := by
  apply unitary_reindex_matrix
  apply Matrix.kronecker_mem_unitary
  · exact unitary_reindex_matrix _ _
      (unitary.star_mem (inverseFourierMatrix_unitary (2^ell) (by positivity)))
  · exact (Matrix.unitaryGroup _ ℂ).one_mem

lemma physicalPE_unitary (ell q : ℕ) (W : Operator (1+q))
    (hW : W ∈ Matrix.unitaryGroup (Basis (1+q)) ℂ) :
    physicalPE ell q W ∈ Matrix.unitaryGroup (Basis (ell+(1+q))) ℂ := by
  exact (Matrix.unitaryGroup _ ℂ).mul_mem
    ((Matrix.unitaryGroup _ ℂ).mul_mem (unitary.star_mem (qftOnData_unitary ell (1+q)))
      (physicalPowers_unitary ell q W hW)) (qftOnData_unitary ell (1+q))

lemma nativePE_error {G : EffectiveGateSet} (conv : GateConvention G) (ell : ℕ) {q : ℕ}
    (walk : EffectiveCircuit G q) (fourier : EffectiveCircuit G (ell+(1+q)))
    (W : Operator (1+q)) (hW : W ∈ Matrix.unitaryGroup (Basis (1+q)) ℂ)
    (u f : ℝ) (hu : 0 ≤ u)
    (hwalk : ‖(rotationSpectator walk).matrix-W‖ ≤ u)
    (hfourier : ‖fourier.matrix-FourierCompilation.qftOnData ell (1+q)‖ ≤ f) :
    ‖(nativePE conv ell walk fourier).matrix-physicalPE ell q W‖ ≤
      2*f+(2^ell:ℕ)*u := by
  rw [nativePE, phaseEstimationCircuit_matrix]
  exact unitary_sandwich_total_error_le _ _ _ _ (fourier.unitary)
    (qftOnData_unitary ell (1+q))
    (physicalPowers_unitary ell q _ (rotationSpectator walk).unitary) f _ hfourier
    (physicalPowers_error ell q _ W (rotationSpectator walk).unitary hW u hu hwalk)

/-- The complete native list, with the three component errors propagated.
Its target will be identified with the paper's coherent walk filter below. -/
theorem nativeFilter_error_physical {G : EffectiveGateSet} (conv : GateConvention G)
    (ell : ℕ) {q : ℕ} (walk : EffectiveCircuit G q)
    (fourier : EffectiveCircuit G (ell+(1+q))) (angle : Basis ell → RationalRep)
    (W : Operator (1+q)) (hW : W ∈ Matrix.unitaryGroup (Basis (1+q)) ℂ)
    (g : Basis ell → ℝ) (u f σ : ℝ) (hu : 0 ≤ u) (hσ : 0 ≤ σ)
    (hwalk : ‖(rotationSpectator walk).matrix-W‖ ≤ u)
    (hfourier : ‖fourier.matrix-FourierCompilation.qftOnData ell (1+q)‖ ≤ f)
    (hlabel : ∀ j, ‖angleRotation (angle j).value-amplitudeRotation (g j)‖ ≤ σ) :
    ‖(nativeFilter conv ell walk fourier angle).matrix -
      (physicalPE ell q W).conjTranspose * physicalLabel ell q g * physicalPE ell q W‖ ≤
      2*(2^ell:ℕ)*u+4*f+σ := by
  rw [nativeFilter, coherentFilterCircuit_matrix]
  have h := unitary_sandwich_total_error_le _ _ _ _ (nativePE conv ell walk fourier).unitary
    (physicalPE_unitary ell q W hW) (labelCircuit conv ell q angle).unitary
    (2*f+(2^ell:ℕ)*u) σ (nativePE_error conv ell walk fourier W hW u f hu hwalk hfourier)
    (labelCircuit_error conv ell q angle g σ hσ hlabel)
  convert h using 1 <;> ring


section RegisterIdentities
variable {s n : Type*} [Fintype s] [Fintype n] [DecidableEq s] [DecidableEq n]

/-- Keep the rotation bit as an untouched spectator while exposing phase first. -/
def rotateLift (A : Matrix (s × n) (s × n) ℂ) :
    Matrix (s × (Fin 2 × n)) (s × (Fin 2 × n)) ℂ :=
  (phaseLift A).submatrix rotationIndex.symm rotationIndex.symm

lemma phaseLift_mul (A B : Matrix (s × n) (s × n) ℂ) :
    phaseLift (A*B) = phaseLift A * phaseLift B := by
  simp [phaseLift, Matrix.fromBlocks_multiply]

lemma rotateLift_mul (A B : Matrix (s × n) (s × n) ℂ) :
    rotateLift (A*B) = rotateLift A * rotateLift B := by
  unfold rotateLift
  rw [phaseLift_mul, Matrix.submatrix_mul_equiv]

lemma rotateLift_apply (A : Matrix (s × n) (s × n) ℂ) (j k : s) (b c : Fin 2) (x y : n) :
    rotateLift A (j,(b,x)) (k,(c,y)) = if b=c then A (j,x) (k,y) else 0 := by
  fin_cases b <;> fin_cases c <;> simp [rotateLift, phaseLift, rotationIndex]

lemma rotateLift_kronecker (A : Matrix s s ℂ) :
    rotateLift (kronecker A (1 : Matrix n n ℂ)) =
      kronecker A (1 : Matrix (Fin 2 × n) (Fin 2 × n) ℂ) := by
  ext ⟨j,b,x⟩ ⟨k,c,y⟩
  rw [rotateLift_apply]
  by_cases hb : b=c <;> by_cases hx : x=y <;>
    simp [Matrix.kronecker, Matrix.one_apply, hb, hx]

lemma rotateLift_select (K : s → Matrix n n ℂ) :
    rotateLift (selectMatrix K) = selectMatrix (fun j => kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (K j)) := by
  ext ⟨j,b,x⟩ ⟨k,c,y⟩
  rw [rotateLift_apply]
  by_cases hj : j=k <;> by_cases hb : b=c <;>
    simp [selectMatrix, Matrix.kronecker, Matrix.one_apply, hj, hb]

lemma identity_kronecker_pow (A : Matrix n n ℂ) (r : ℕ) :
    (kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) A)^r =
      kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (A^r) := by
  induction r with
  | zero => simp [Matrix.one_kronecker_one]
  | succ r ih =>
    rw [pow_succ, ih, pow_succ]
    simpa only [one_mul] using
      (Matrix.mul_kronecker_mul (1 : Matrix (Fin 2) (Fin 2) ℂ)
        (1 : Matrix (Fin 2) (Fin 2) ℂ) (A^r) A).symm

lemma phaseEstimation_rotation (V : Matrix n n ℂ) (M : ℕ) :
    phaseEstimationMatrix (kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) V) M =
      rotateLift (phaseEstimationMatrix V M) := by
  unfold phaseEstimationMatrix sandwichSelect
  rw [rotateLift_mul, rotateLift_mul, rotateLift_kronecker, rotateLift_kronecker,
    rotateLift_select]
  have hk : (fun j : Fin M => (kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) V)^j.val) =
      (fun j : Fin M => kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (V^j.val)) :=
    funext (fun j => identity_kronecker_pow V j.val)
  rw [hk]

lemma sandwichSelect_reindex {a b c d : Type*} [Fintype a] [Fintype b]
    [Fintype c] [Fintype d] [DecidableEq a] [DecidableEq b]
    [DecidableEq c] [DecidableEq d] (e : a ≃ b) (f : c ≃ d)
    (A B : Matrix b b ℂ) (K : b → Matrix d d ℂ) :
    sandwichSelect (A.submatrix e e) (B.submatrix e e) (fun j => (K (e j)).submatrix f f) =
      (sandwichSelect A B K).submatrix (e.prodCongr f) (e.prodCongr f) := by
  unfold sandwichSelect
  rw [reindex_select]
  have hA : kronecker (A.submatrix e e) (1 : Matrix c c ℂ) =
      (kronecker A (1 : Matrix d d ℂ)).submatrix (e.prodCongr f) (e.prodCongr f) := by
    simpa using reindex_kronecker e f A (1 : Matrix d d ℂ)
  have hB : kronecker (B.submatrix e e) (1 : Matrix c c ℂ) =
      (kronecker B (1 : Matrix d d ℂ)).submatrix (e.prodCongr f) (e.prodCongr f) := by
    simpa using reindex_kronecker e f B (1 : Matrix d d ℂ)
  rw [hA,hB, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

lemma phaseEstimation_reindex {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (V : Matrix b b ℂ) (M : ℕ) :
    phaseEstimationMatrix (V.submatrix e e) M =
      (phaseEstimationMatrix V M).submatrix ((Equiv.refl (Fin M)).prodCongr e)
        ((Equiv.refl (Fin M)).prodCongr e) := by
  unfold phaseEstimationMatrix
  simp only [reindex_pow]
  simpa only [Matrix.submatrix_id_id, Equiv.refl_apply] using
    sandwichSelect_reindex (Equiv.refl (Fin M)) e (inverseFourierMatrix M)
      (star (inverseFourierMatrix M)) (fun r : Fin M => V^r.val)

end RegisterIdentities

/-- The physical rotation-and-data coordinates. -/
def rotationDataIndex (q : ℕ) : Basis (1+q) ≃ (Fin 2 × Basis q) :=
  (tensorBits 1 q).trans (oneBit.prodCongr (Equiv.refl _))

/-- The phase binary index and untouched physical data coordinates. -/
def phaseDataIndex (ell q : ℕ) : Basis (ell+q) ≃ (Fin (2^ell) × Basis q) :=
  (registerBasis ell q).trans ((SelectedFilter.bitsBinaryIndex ell).prodCongr (Equiv.refl _))

/-- The exact physical-to-paper register permutation. Rotation zero is the left block. -/
def filterIndex (ell q : ℕ) : Basis (ell+(1+q)) ≃
    Sum (Fin (2^ell) × Basis q) (Fin (2^ell) × Basis q) :=
  ((registerBasis ell (1+q)).trans
    ((SelectedFilter.bitsBinaryIndex ell).prodCongr (rotationDataIndex q))).trans rotationIndex.symm

/-- Ideal walk with the actual untouched rotation wire. -/
def physicalWalk (q : ℕ) (V : Operator q) : Operator (1+q) :=
  (kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) V).submatrix (rotationDataIndex q) (rotationDataIndex q)

lemma physicalWalk_unitary (q : ℕ) (V : Operator q) (hV : V ∈ Matrix.unitaryGroup (Basis q) ℂ) :
    physicalWalk q V ∈ Matrix.unitaryGroup (Basis (1+q)) ℂ :=
  unitary_reindex_matrix _ _ (Matrix.kronecker_mem_unitary (Matrix.unitaryGroup _ ℂ).one_mem hV)

lemma rotationSpectator_error {G : EffectiveGateSet} {q : ℕ}
    (walk : EffectiveCircuit G q) (V : Operator q) (u : ℝ) (herr : ‖walk.matrix-V‖ ≤ u) :
    ‖(rotationSpectator walk).matrix-physicalWalk q V‖ ≤ u := by
  have hid : physicalWalk q V = (kronecker (1 : Operator 1) V).submatrix
      (tensorBits 1 q) (tensorBits 1 q) := by
    unfold physicalWalk rotationDataIndex
    ext x y
    simp [Matrix.kronecker, Matrix.one_apply, oneBit.injective.eq_iff]
  rw [rotationSpectator, tensorCircuit_matrix, hid]
  change ‖(kronecker (1 : Operator 1) walk.matrix).submatrix _ _ -
    (kronecker (1 : Operator 1) V).submatrix _ _‖ ≤ u
  rw [submatrix_equiv_error]
  have heq : kronecker (1 : Operator 1) walk.matrix - kronecker (1 : Operator 1) V =
      kronecker (1 : Operator 1) (walk.matrix-V) := by ext i j; simp [Matrix.kronecker, mul_sub]
  rw [heq]
  exact (identity_tensor_opNorm_le _).trans herr

lemma kronecker_identity_adjoint {a b : Type*} [DecidableEq b]
    (A : Matrix a a ℂ) : (kronecker A (1 : Matrix b b ℂ)).conjTranspose =
      kronecker A.conjTranspose (1 : Matrix b b ℂ) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  by_cases h : x=y <;> simp [Matrix.kronecker, Matrix.conjTranspose_apply, Matrix.one_apply, h, eq_comm]

lemma physicalPE_eq_phaseEstimation (ell q : ℕ) (W : Operator (1+q)) :
    physicalPE ell q W = (phaseEstimationMatrix W (2^ell)).submatrix
      (phaseDataIndex ell (1+q)) (phaseDataIndex ell (1+q)) := by
  unfold physicalPE physicalPowers FourierCompilation.qftOnData FourierCompilation.qftMatrix
  rw [Matrix.conjTranspose_submatrix, kronecker_identity_adjoint,
    Matrix.conjTranspose_submatrix, Matrix.conjTranspose_conjTranspose]
  rw [tensorBits_register]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  change _ = ((phaseEstimationMatrix W (2^ell)).submatrix
    ((SelectedFilter.bitsBinaryIndex ell).prodCongr (Equiv.refl (Basis (1+q))))
    ((SelectedFilter.bitsBinaryIndex ell).prodCongr (Equiv.refl (Basis (1+q))))).submatrix
      (registerBasis ell (1+q)) (registerBasis ell (1+q))
  apply congrArg (fun A : Matrix (Basis ell × Basis (1+q)) (Basis ell × Basis (1+q)) ℂ =>
    A.submatrix (registerBasis ell (1+q)) (registerBasis ell (1+q)))
  simpa only [sandwichSelect, phaseEstimationMatrix, Matrix.submatrix_id_id,
    Equiv.refl_apply, Matrix.star_eq_conjTranspose] using
    sandwichSelect_reindex (SelectedFilter.bitsBinaryIndex ell) (Equiv.refl (Basis (1+q)))
      (inverseFourierMatrix (2^ell)) (star (inverseFourierMatrix (2^ell)))
      (fun r : Fin (2^ell) => W^r.val)

lemma physicalPE_eq_phaseLift (ell q : ℕ) (V : Operator q) :
    physicalPE ell q (physicalWalk q V) =
      (phaseLift (phaseEstimationMatrix V (2^ell))).submatrix (filterIndex ell q) (filterIndex ell q) := by
  rw [physicalPE_eq_phaseEstimation, physicalWalk, phaseEstimation_reindex, phaseEstimation_rotation]
  rfl

lemma physicalLabel_eq_labelRotation (ell q : ℕ) (g : Fin (2^ell) → ℝ) :
    physicalLabel ell q (fun j => g (SelectedFilter.bitsBinaryIndex ell j)) =
      (labelRotation (n := Basis q) g).submatrix (filterIndex ell q) (filterIndex ell q) := by
  ext x y
  simp [physicalLabel, labelRotation, filterIndex, rotationDataIndex, Matrix.submatrix_apply,
    selectMatrix, Matrix.kronecker, (SelectedFilter.bitsBinaryIndex ell).injective.eq_iff]
  rfl

lemma physicalFilter_eq_phaseFilter (ell q : ℕ) (V : Operator q) (g : Fin (2^ell) → ℝ) :
    (physicalPE ell q (physicalWalk q V)).conjTranspose *
      physicalLabel ell q (fun j => g (SelectedFilter.bitsBinaryIndex ell j)) *
      physicalPE ell q (physicalWalk q V) =
    (phaseFilterCircuit (phaseEstimationMatrix V (2^ell)) g).submatrix
      (filterIndex ell q) (filterIndex ell q) := by
  rw [physicalPE_eq_phaseLift, physicalLabel_eq_labelRotation, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rfl

/-- The exact semantic target is the original full coherent walk-filter matrix. -/
lemma physicalFilter_eq_coherentWalkFilter (ell q : ℕ) (V : Operator q) (δ : ℝ) :
    (physicalPE ell q (physicalWalk q V)).conjTranspose *
      physicalLabel ell q (fun j => filterG δ (2*Real.pi*((SelectedFilter.bitsBinaryIndex ell j : ℕ):ℝ)/(2^ell:ℕ))) *
      physicalPE ell q (physicalWalk q V) =
    (coherentWalkFilter V (2^ell) δ).submatrix (filterIndex ell q) (filterIndex ell q) := by
  have hg : (fun j : Fin (2^ell) => filterG δ (2*Real.pi*((j:ℝ)/(2^ell:ℕ)))) =
      (fun j : Fin (2^ell) => filterG δ (2*Real.pi*(j:ℝ)/(2^ell:ℕ))) := by
    funext j
    congr 1
    ring
  exact (physicalFilter_eq_phaseFilter ell q V
    (fun j : Fin (2^ell) => filterG δ (2*Real.pi*(j:ℝ)/(2^ell:ℕ)))).trans
      (congrArg (fun g : Fin (2^ell) → ℝ =>
        (phaseFilterCircuit (phaseEstimationMatrix V (2^ell)) g).submatrix
          (filterIndex ell q) (filterIndex ell q)) hg.symm)

/-- Full native-filter error relative to the original paper matrix, with no
assumed filter implementation or final compression error. -/
theorem nativeFilter_error {G : EffectiveGateSet} (conv : GateConvention G)
    (ell : ℕ) {q : ℕ} (walk : EffectiveCircuit G q)
    (fourier : EffectiveCircuit G (ell+(1+q))) (angle : Basis ell → RationalRep)
    (V : Operator q) (hV : V ∈ Matrix.unitaryGroup (Basis q) ℂ)
    (δ u f σ : ℝ) (hu : 0 ≤ u) (hσ : 0 ≤ σ)
    (hwalk : ‖walk.matrix-V‖ ≤ u)
    (hfourier : ‖fourier.matrix-FourierCompilation.qftOnData ell (1+q)‖ ≤ f)
    (hlabel : ∀ j, ‖angleRotation (angle j).value-amplitudeRotation
      (filterG δ (2*Real.pi*((SelectedFilter.bitsBinaryIndex ell j : ℕ):ℝ)/(2^ell:ℕ)))‖ ≤ σ) :
    ‖(nativeFilter conv ell walk fourier angle).matrix -
      (coherentWalkFilter V (2^ell) δ).submatrix (filterIndex ell q) (filterIndex ell q)‖ ≤
      2*(2^ell:ℕ)*u+4*f+σ := by
  rw [← physicalFilter_eq_coherentWalkFilter]
  exact nativeFilter_error_physical conv ell walk fourier angle (physicalWalk q V)
    (physicalWalk_unitary q V hV) _ u f σ hu hσ
    (rotationSpectator_error walk V u hwalk) hfourier hlabel

/-- Actual raw rational label-angle outputs. No canonical rational encoding is
substituted for the bytes returned by the elementary numerical algorithms. -/
def representedAngles (E : ElementaryAnalyticInputs) (δ : RationalRep) (ell n k : ℕ) :
    Basis ell → RationalRep := fun j => representedLabelFilterAngle E δ
      (RationalRep.ofRat (2^ell:ℕ))
      (RationalRep.ofRat (SelectedFilter.bitsBinaryIndex ell j).val) n k

/-- The final native filter includes the actual compiled QFT network and actual
represented rational rotations at every enumerated phase label. -/
def compiledFilter {G : EffectiveGateSet} (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (precision ell : ℕ) {q : ℕ} (walk : EffectiveCircuit G q) (δ : RationalRep) (n k : ℕ) :
    EffectiveCircuit G (ell+(1+q)) :=
  nativeFilter conv ell walk (FourierCompilation.circuitOnData conv E precision ell (1+q))
    (representedAngles E δ ell n k)

/-- The native filter's complete error follows from a native walk error and
explicit elementary numerical precision budgets. QFT correctness is precisely
the independently disclosed fixed-network external input. -/
theorem compiledFilter_error {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (standard : FourierCompilation.StandardQFTCorrectness)
    (precision ell : ℕ) {q : ℕ} (walk : EffectiveCircuit G q) (V : Operator q)
    (hV : V ∈ Matrix.unitaryGroup (Basis q) ℂ) (δ : RationalRep) (n k : ℕ)
    (u σ : ℝ) (hu : 0 ≤ u) (hσ : 0 ≤ σ) (hδ : 0 < δ.value)
    (hwalk : ‖walk.matrix-V‖ ≤ u)
    (hk : bitError k ≤ σ/4) (hn : bitError n ≤ (δ.value:ℝ)*σ/40) :
    ‖(compiledFilter conv E precision ell walk δ n k).matrix -
      (coherentWalkFilter V (2^ell) δ.value).submatrix (filterIndex ell q) (filterIndex ell q)‖ ≤
      2*(2^ell:ℕ)*u+16*(ell*(ell+2):ℕ)*bitError precision+σ := by
  unfold compiledFilter
  have h := nativeFilter_error conv ell walk
    (FourierCompilation.circuitOnData conv E precision ell (1+q)) (representedAngles E δ ell n k)
    V hV δ.value u (4*(ell*(ell+2):ℕ)*bitError precision) σ hu hσ hwalk
    (FourierCompilation.circuitOnData_error conv E standard precision ell (1+q)) (by
      intro j
      have hjM : ((SelectedFilter.bitsBinaryIndex ell j).val:ℚ) ≤ (2^ell:ℕ) := by
        exact_mod_cast (SelectedFilter.bitsBinaryIndex ell j).isLt.le
      simpa only [representedAngles, RationalRep.ofRat_value, Rat.cast_natCast] using
        representedLabelFilterAngle_error_of_budget E δ
          (RationalRep.ofRat (2^ell:ℕ))
          (RationalRep.ofRat (SelectedFilter.bitsBinaryIndex ell j).val) n k σ hδ
          (by simp only [RationalRep.ofRat_value]; positivity)
          (by simp only [RationalRep.ofRat_value]; positivity)
          (by simpa only [RationalRep.ofRat_value] using hjM) hk hn)
  convert h using 1 <;> ring


/-- Reindexing data wires commutes with adding the rotation spectator. -/
lemma phaseLift_reindex {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (M : ℕ)
    (P : Matrix (Fin M × b) (Fin M × b) ℂ) :
    phaseLift (P.submatrix ((Equiv.refl (Fin M)).prodCongr e) ((Equiv.refl (Fin M)).prodCongr e)) =
      (phaseLift P).submatrix
        (Equiv.sumCongr ((Equiv.refl (Fin M)).prodCongr e) ((Equiv.refl (Fin M)).prodCongr e))
        (Equiv.sumCongr ((Equiv.refl (Fin M)).prodCongr e) ((Equiv.refl (Fin M)).prodCongr e)) := by
  ext x y
  rcases x with x|x <;> rcases y with y|y <;> rfl

lemma labelRotation_reindex {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (M : ℕ) (g : Fin M → ℝ) :
    labelRotation (n := a) g = (labelRotation (n := b) g).submatrix
      (Equiv.sumCongr ((Equiv.refl (Fin M)).prodCongr e) ((Equiv.refl (Fin M)).prodCongr e))
      (Equiv.sumCongr ((Equiv.refl (Fin M)).prodCongr e) ((Equiv.refl (Fin M)).prodCongr e)) := by
  ext x y
  rcases x with ⟨j,x⟩|⟨j,x⟩ <;> rcases y with ⟨k,y⟩|⟨k,y⟩ <;>
    simp [labelRotation, rotationIndex, selectMatrix, Matrix.kronecker, Matrix.one_apply, e.injective.eq_iff]

/-- Naturality of the full coherent filter under an arbitrary finite data
basis equivalence; it uses no spectral or approximation input. -/
theorem coherentWalkFilter_reindex {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (V : Matrix b b ℂ) (M : ℕ) (δ : ℝ) :
    coherentWalkFilter (V.submatrix e e) M δ = (coherentWalkFilter V M δ).submatrix
      (Equiv.sumCongr ((Equiv.refl (Fin M)).prodCongr e) ((Equiv.refl (Fin M)).prodCongr e))
      (Equiv.sumCongr ((Equiv.refl (Fin M)).prodCongr e) ((Equiv.refl (Fin M)).prodCongr e)) := by
  unfold coherentWalkFilter phaseFilterCircuit
  rw [phaseEstimation_reindex, phaseLift_reindex, labelRotation_reindex e,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rfl

end Paper25.OperationalModel.CoherentCompilation

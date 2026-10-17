import Paper25.LocalCompilation
import Paper25.SelectedPreparation
import Paper25.RepresentedAnalytic
import Paper25.GlobalFilterError
import Paper25.Synthesis
import Paper25.MatrixCompilationNorm
import Paper25.UniformCompilation

/-!
# The fixed QFT network and its rational-angle native compilation

The standard external input is restricted to the ideal fixed network below:
Cleve, Ekert, Macchiavello, Mosca, *Quantum Algorithms Revisited*,
arXiv:quant-ph/9708016v1, Section 4, printed pp. 8--9, Figure 5 and
(4.1)--(4.6), https://arxiv.org/pdf/quant-ph/9708016 . The figure applies H to
each wire in increasing order, then controlled R_k from the later wires, and
finally reverses wire order. R_k=diag(1,exp(2πi/2^k)).

No Fourier-family compiler, PE correctness or P25 conclusion is supplied by
that input. The actual rational phases, native local gate lists, gatewise
approximation and accumulation, workspace, count and counter templates are
separate constructions proved here.
-/

noncomputable section
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator Kronecker
open Matrix
namespace Paper25.OperationalModel.FourierCompilation
open LocalCompilation
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1200000

/-- A specified physical one-wire placement, with no additional workspace. -/
def oneWire {ell : ℕ} (i : Fin ell) : Placement ell 1 :=
  placementOfEmbedding ⟨fun _ => i, by intro a b _; exact Subsingleton.elim _ _⟩

/-- Ordered two-wire placement: the first wire is the control. -/
def twoWires {ell : ℕ} (i j : Fin ell) (hij : i ≠ j) : Placement ell 2 :=
  placementOfEmbedding ⟨(fun k => if k = 0 then i else j), by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

/-- Real-angle ideal phase, prior to rational elementary-gate replacement. -/
def realPhase (θ : ℝ) : Operator 1 :=
  Matrix.diagonal (fun b => if b 0 = 0 then 1 else Complex.exp (Complex.I * θ))

lemma realPhase_rat (θ : ℚ) : realPhase (θ : ℝ) = phaseMatrix θ := rfl

lemma realPhase_unitary (θ : ℝ) : OneCleanQubit.Unitary (realPhase θ) := by
  have hm : realPhase θ ∈ Matrix.unitaryGroup (Basis 1) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    change (realPhase θ).conjTranspose * realPhase θ = 1
    rw [realPhase, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext b
    by_cases hb : b 0 = 0
    · simp [hb]
    · simpa [hb] using Paper25.exp_imaginary_unitary θ
  exact ⟨hm.1, hm.2⟩

lemma physicalControl_realPhase_unitary (θ : ℝ) :
    OneCleanQubit.Unitary (physicalControl (realPhase θ)) :=
  unitary_submatrix _ _ (OneCleanQubit.controlled_unitary _ (realPhase_unitary θ))

/-- Lifting a diagonal gate leaves every unselected physical qubit alone. -/
lemma lift_diagonal {ell k : ℕ} (p : Placement ell k) (d : Basis k → ℂ) :
    p.lift (Matrix.diagonal d) = Matrix.diagonal (fun x => d (p.split x).1) := by
  unfold Placement.lift
  rw [← Matrix.diagonal_one]
  change ((Matrix.diagonal d ⊗ₖ Matrix.diagonal (fun _ => (1 : ℂ))).submatrix p.split p.split) = _
  rw [Matrix.diagonal_kronecker_diagonal,
    Matrix.submatrix_diagonal_equiv]
  congr 1
  funext x
  simp

lemma controlled_diagonal {ν : Type*} [Fintype ν] [DecidableEq ν] (d : ν → ℂ) :
    OneCleanQubit.controlled (Matrix.diagonal d) =
      Matrix.diagonal (Sum.elim (fun _ : ν => (1 : ℂ)) d) := by
  ext x y
  cases x <;> cases y <;>
    simp [OneCleanQubit.controlled, Matrix.fromBlocks, Matrix.diagonal_apply, Matrix.one_apply]

/-- The exact local diagonal exposed by a controlled phase. -/
def controlledPhaseDiagonal (θ : ℝ) (x : Basis 2) : ℂ :=
  Sum.elim (fun _ : Basis 1 => 1)
    (fun b => if b 0 = 0 then 1 else Complex.exp (Complex.I * θ)) (probeBasis 1 x)

lemma physicalControl_realPhase (θ : ℝ) :
    physicalControl (realPhase θ) = Matrix.diagonal (controlledPhaseDiagonal θ) := by
  unfold physicalControl realPhase controlledPhaseDiagonal
  rw [controlled_diagonal, Matrix.submatrix_diagonal_equiv]
  rfl

lemma exp_phase_error (x y : ℝ) :
    ‖Complex.exp (Complex.I * x) - Complex.exp (Complex.I * y)‖ ≤ 2 * |x-y| := by
  have h := Complex.norm_le_abs_re_add_abs_im
    (Complex.exp (Complex.I * x) - Complex.exp (Complex.I * y))
  have hc := cos_abs_sub_le x y
  have hs := sin_abs_sub_le x y
  have he : (Complex.exp (Complex.I * x) - Complex.exp (Complex.I * y)).re =
      Real.cos x - Real.cos y := by simp [Complex.exp_re]
  have hi : (Complex.exp (Complex.I * x) - Complex.exp (Complex.I * y)).im =
      Real.sin x - Real.sin y := by simp [Complex.exp_im]
  rw [he,hi] at h
  linarith

lemma controlledPhaseDiagonal_error (x y : ℝ) (b : Basis 2) :
    ‖controlledPhaseDiagonal x b - controlledPhaseDiagonal y b‖ ≤ 2 * |x-y| := by
  unfold controlledPhaseDiagonal
  cases probeBasis 1 b with
  | inl b => simp
  | inr b =>
    by_cases hb : b 0 = 0
    · simp [hb]
    · simpa [hb] using exp_phase_error x y

/-- Gatewise operator-norm error is independent of the total register size. -/
lemma lifted_controlled_phase_error {ell : ℕ} (p : Placement ell 2) (x y : ℝ) :
    ‖p.lift (physicalControl (realPhase x)) - p.lift (physicalControl (realPhase y))‖ ≤
      2 * |x-y| := by
  rw [physicalControl_realPhase, physicalControl_realPhase, lift_diagonal, lift_diagonal,
    Matrix.diagonal_sub]
  apply Paper25.diagonal_l2_opNorm_le _ _ (by positivity)
  intro b
  exact controlledPhaseDiagonal_error x y _

/-- The three allowed operations in the standard fixed QFT network. -/
inductive Instruction (ell : ℕ) where
  | hadamard (i : Fin ell)
  | phase (i j : Fin ell) (hij : i ≠ j) (distance : ℕ)
  | swap (i j : Fin ell) (hij : i ≠ j)

/-- The later physical wire named by the inner bounded counter. -/
def laterWire {ell : ℕ} (i : Fin ell) (d : Fin (ell-(i.val+1))) : Fin ell :=
  ⟨i.val+1+d.val, by omega⟩
lemma laterWire_ne {ell : ℕ} (i : Fin ell) (d : Fin (ell-(i.val+1))) : laterWire i d ≠ i := by
  intro h
  have he := congrArg Fin.val h
  dsimp [laterWire] at he
  omega

/-- A single QFT row uses only valid later-wire counters, without a guarded gate leaf. -/
def row (ell : ℕ) (i : Fin ell) : List (Instruction ell) :=
  [.hadamard i] ++ (List.ofFn (fun d : Fin (ell-(i.val+1)) =>
    .phase (laterWire i d) i (laterWire_ne i d) (d.val+1)))

/-- The first wire in the final reversal counter. -/
def reversalWire (ell : ℕ) (i : Fin (ell/2)) : Fin ell := ⟨i.val, by omega⟩
lemma reversalWire_ne (ell : ℕ) (i : Fin (ell/2)) :
    reversalWire ell i ≠ Fin.rev (reversalWire ell i) := by
  intro h
  have he := congrArg Fin.val h
  dsimp [reversalWire, Fin.rev] at he
  omega

/-- The exact final wire reversal, using ell/2 actual three-CNOT swaps. -/
def reversal (ell : ℕ) : List (Instruction ell) :=
  List.ofFn (fun i : Fin (ell/2) => .swap (reversalWire ell i)
    (Fin.rev (reversalWire ell i)) (reversalWire_ne ell i))

/-- The fixed network from Section 4, Figure 5, including output reversal. -/
def network (ell : ℕ) : List (Instruction ell) :=
  (List.ofFn (fun i : Fin ell => row ell i)).flatten ++ reversal ell

/-- Rational approximation of the required π/2^distance angle. -/
def rationalAngle (E : ElementaryAnalyticInputs) (precision distance : ℕ) : ℚ :=
  rationalPi E precision / (2 : ℚ) ^ distance

lemma rationalAngle_error (E : ElementaryAnalyticInputs) (precision distance : ℕ) :
    |(rationalAngle E precision distance : ℝ) - Real.pi / (2 : ℝ) ^ distance| ≤
      2 * bitError precision := by
  have h := rationalPi_error E precision
  have hd : (1 : ℝ) ≤ 2 ^ distance := one_le_pow₀ (by norm_num)
  have hp : (0 : ℝ) < 2 ^ distance := by positivity
  rw [rationalAngle, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, ← sub_div, abs_div,
    abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  nlinarith [bitError_pos precision]

/-- A binary power of two as an unreduced positive-denominator fraction.
This constructor never normalizes an input-dependent rational. -/
def powerTwoRep (distance : ℕ) : RationalRep := ⟨(2:ℤ)^distance, 1, by decide⟩

@[simp] lemma powerTwoRep_value (distance : ℕ) : (powerTwoRep distance).value = (2:ℚ)^distance := by
  simp [powerTwoRep, RationalRep.value]

/-- The actual printed angle is raw pi divided by the raw binary power of two. -/
def angleRep (E : ElementaryAnalyticInputs) (precision distance : ℕ) : RationalRep :=
  (representedPi E precision).div (powerTwoRep distance)

@[simp] lemma angleRep_value (E : ElementaryAnalyticInputs) (precision distance : ℕ) :
    (angleRep E precision distance).value = rationalAngle E precision distance := by
  simp only [angleRep, RationalRep.value_div, representedPi_value, powerTwoRep_value, rationalAngle]

/-- Exact raw-byte numerical composition; its two components are unary precision
and the explicitly printed binary power of two. -/
lemma angleRep_computes (E : ElementaryAnalyticInputs) (C : ClassicalDescriptionClosure)
    {α : Type} (encode : α → Input) (precision distance : α → ℕ)
    (hprecision : LogspaceComputes encode (fun a => encodeNat (precision a)))
    (hpower : LogspaceComputes encode (fun a => (powerTwoRep (distance a)).encode)) :
    LogspaceComputes encode (fun a => (angleRep E (precision a) (distance a)).encode) :=
  computes_represented_binary C encode (fun a => representedPi E (precision a))
    (fun a => powerTwoRep (distance a)) RationalRep.div
    (representedPi_computes E C encode precision hprecision) hpower C.rationalDiv

/-- Native CNOT on an ordered pair of existing physical wires. -/
def cnotAt {G : EffectiveGateSet} (conv : GateConvention G) {ell : ℕ}
    (i j : Fin ell) (hij : i ≠ j) : EffectiveCircuit G ell :=
  embedCircuit (twoWires i j hij) conv.CNOT

/-- SWAP is the literal three-CNOT chronological list, with no new qubit. -/
def swapAt {G : EffectiveGateSet} (conv : GateConvention G) {ell : ℕ}
    (i j : Fin ell) (hij : i ≠ j) : EffectiveCircuit G ell :=
  cnotAt conv i j hij ++ cnotAt conv j i hij.symm ++ cnotAt conv i j hij

/-- Actual rational-angle native instruction list. -/
def compileInstruction {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (precision : ℕ) {ell : ℕ} :
    Instruction ell → EffectiveCircuit G ell
  | .hadamard i => embedCircuit (oneWire i) (conv.hadamardAt 0)
  | .phase i j hij d => embedCircuit (twoWires i j hij)
      (controlledCircuit conv (conv.phaseRep (angleRep E precision d)))
  | .swap i j hij => swapAt conv i j hij

/-- Ideal fixed-network semantics; only phase angles remain real. -/
def idealInstruction {ell : ℕ} : Instruction ell → Operator ell
  | .hadamard i => (oneWire i).lift (physicalHadamard 0)
  | .phase i j hij d => (twoWires i j hij).lift
      (physicalControl (realPhase (Real.pi / (2 : ℝ) ^ d)))
  | .swap i j hij =>
      (twoWires i j hij).lift (physicalControl LocalCompilation.pauliX) *
      (twoWires j i hij.symm).lift (physicalControl LocalCompilation.pauliX) *
      (twoWires i j hij).lift (physicalControl LocalCompilation.pauliX)

/-- Chronological matrix product, the same convention as native circuits. -/
def product {ell : ℕ} : List (Operator ell) → Operator ell
  | [] => 1
  | U :: L => product L * U

/-- Precisely the published standard QFT network correctness theorem.
It only refers to the fully specified H/controlled-R/SWAP network above. -/
structure StandardQFTCorrectness : Prop where
  network_correct : ∀ ell, product ((network ell).map idealInstruction) =
    (Paper25.inverseFourierMatrix (2 ^ ell)).conjTranspose.submatrix
      (Paper25.SelectedFilter.bitsBinaryIndex ell) (Paper25.SelectedFilter.bitsBinaryIndex ell)

/-- The native rational-angle QFT, with exactly ell physical wires. -/
def circuit {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (precision ell : ℕ) : EffectiveCircuit G ell :=
  ((network ell).map (compileInstruction conv E precision)).flatten

lemma cnotAt_matrix {G : EffectiveGateSet} (conv : GateConvention G) {ell : ℕ}
    (i j : Fin ell) (hij : i ≠ j) :
    (cnotAt conv i j hij).matrix =
      (twoWires i j hij).lift (physicalControl LocalCompilation.pauliX) := by
  rw [cnotAt, embedCircuit_matrix, conv.CNOT_matrix]

lemma compileInstruction_unitary {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (precision : ℕ) {ell : ℕ} (a : Instruction ell) :
    OneCleanQubit.Unitary (compileInstruction conv E precision a).matrix :=
  EffectiveCircuit.unitary _

lemma compileInstruction_hadamard {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (precision : ℕ) {ell : ℕ} (i : Fin ell) :
    (compileInstruction conv E precision (.hadamard i)).matrix = idealInstruction (.hadamard i) := by
  simp only [compileInstruction, embedCircuit_matrix, conv.hadamard_matrix, idealInstruction]

lemma compileInstruction_swap {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (precision : ℕ) {ell : ℕ}
    (i j : Fin ell) (hij : i ≠ j) :
    (compileInstruction conv E precision (.swap i j hij)).matrix =
      idealInstruction (.swap i j hij) := by
  simp only [compileInstruction, swapAt, EffectiveCircuit.matrix_append, cnotAt_matrix,
    idealInstruction, Matrix.mul_assoc]

lemma compileInstruction_phase {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (precision : ℕ) {ell : ℕ}
    (i j : Fin ell) (hij : i ≠ j) (d : ℕ) :
    (compileInstruction conv E precision (.phase i j hij d)).matrix =
      (twoWires i j hij).lift (physicalControl (realPhase (rationalAngle E precision d))) := by
  rw [compileInstruction, embedCircuit_matrix, controlledCircuit_matrix, conv.phaseRep_matrix, angleRep_value,
    realPhase_rat]

lemma idealInstruction_unitary {G : EffectiveGateSet} (conv : GateConvention G)
    {ell : ℕ} (a : Instruction ell) : OneCleanQubit.Unitary (idealInstruction a) := by
  cases a with
  | hadamard i =>
    apply Placement.lift_unitary
    rw [← conv.hadamard_matrix 0]
    exact EffectiveCircuit.unitary _
  | phase i j hij d =>
    exact Placement.lift_unitary _ _ (physicalControl_realPhase_unitary _)
  | swap i j hij =>
    have hu : OneCleanQubit.Unitary (physicalControl LocalCompilation.pauliX) := by
      rw [← conv.CNOT_matrix]
      exact EffectiveCircuit.unitary _
    exact OneCleanQubit.unitary_mul
      (OneCleanQubit.unitary_mul (Placement.lift_unitary _ _ hu) (Placement.lift_unitary _ _ hu))
      (Placement.lift_unitary _ _ hu)

/-- Each rational phase contributes at most four precision units; H and SWAP are exact. -/
lemma instruction_error {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (precision : ℕ) {ell : ℕ} (a : Instruction ell) :
    ‖(compileInstruction conv E precision a).matrix - idealInstruction a‖ ≤
      4 * bitError precision := by
  cases a with
  | hadamard i => rw [compileInstruction_hadamard, sub_self, norm_zero]; exact le_of_lt (mul_pos (by norm_num) (bitError_pos _))
  | swap i j hij => rw [compileInstruction_swap, sub_self, norm_zero]; exact le_of_lt (mul_pos (by norm_num) (bitError_pos _))
  | phase i j hij d =>
    rw [compileInstruction_phase]
    exact (lifted_controlled_phase_error _ _ _).trans (by
      have h := rationalAngle_error E precision d
      nlinarith)

lemma product_unitary {ell : ℕ} (L : List (Operator ell))
    (hL : ∀ U ∈ L, OneCleanQubit.Unitary U) : OneCleanQubit.Unitary (product L) := by
  induction L with
  | nil => simp [product, OneCleanQubit.Unitary]
  | cons U L ih =>
    exact OneCleanQubit.unitary_mul (ih (fun V hV => hL V (by simp [hV]))) (hL U (by simp))

lemma product_error {α : Type*} {ell : ℕ} (F H : α → Operator ell)
    (L : List α) (η : ℝ) (hF : ∀ a ∈ L, OneCleanQubit.Unitary (F a))
    (hH : ∀ a ∈ L, OneCleanQubit.Unitary (H a))
    (herr : ∀ a ∈ L, ‖F a-H a‖ ≤ η) :
    ‖product (L.map F)-product (L.map H)‖ ≤ (L.length : ℝ)*η := by
  induction L with
  | nil => simp [product]
  | cons a L ih =>
    have hp := ih (fun b hb => hF b (by simp [hb])) (fun b hb => hH b (by simp [hb])) (fun b hb => herr b (by simp [hb]))
    have hL : ‖product (L.map F)‖ ≤ 1 := Paper25.Synthesis.unitary_opNorm_le
      (product_unitary _ (fun U hU => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hU; exact hF b (by simp [hb])))
    have ha : ‖H a‖ ≤ 1 := Paper25.Synthesis.unitary_opNorm_le (hH a (by simp))
    have hd : product ((a::L).map F)-product ((a::L).map H) =
        product (L.map F)*(F a-H a)+(product (L.map F)-product (L.map H))*H a := by
      simp only [List.map_cons, product]
      noncomm_ring
    rw [hd]
    calc
      _ ≤ ‖product (L.map F)*(F a-H a)‖ + ‖(product (L.map F)-product (L.map H))*H a‖ := norm_add_le _ _
      _ ≤ ‖F a-H a‖ + ‖product (L.map F)-product (L.map H)‖ := by
        apply add_le_add
        · exact (norm_mul_le _ _).trans (by simpa using mul_le_mul_of_nonneg_right hL (norm_nonneg (F a-H a)))
        · exact (norm_mul_le _ _).trans (by simpa using mul_le_mul_of_nonneg_left ha (norm_nonneg _))
      _ ≤ η+(L.length:ℝ)*η := add_le_add (herr a (by simp)) hp
      _ = _ := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

lemma flatten_matrix {G : EffectiveGateSet} {ell : ℕ} (L : List (EffectiveCircuit G ell)) :
    EffectiveCircuit.matrix L.flatten = product (L.map EffectiveCircuit.matrix) := by
  induction L with
  | nil => simp [product, EffectiveCircuit.matrix]
  | cons C L ih => simp [product, EffectiveCircuit.matrix_append, ih]

lemma circuit_matrix {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (precision ell : ℕ) :
    (circuit conv E precision ell).matrix = product ((network ell).map
      (fun a => (compileInstruction conv E precision a).matrix)) := by
  rw [circuit, flatten_matrix, List.map_map]
  rfl

/-- The positive-sign normalized Fourier matrix in the explicit binary wire order. -/
def qftMatrix (ell : ℕ) : Operator ell :=
  (Paper25.inverseFourierMatrix (2 ^ ell)).conjTranspose.submatrix
    (Paper25.SelectedFilter.bitsBinaryIndex ell) (Paper25.SelectedFilter.bitsBinaryIndex ell)

/-- Native approximation proved from individual phase replacement and unitary telescoping. -/
theorem circuit_error {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (standard : StandardQFTCorrectness) (precision ell : ℕ) :
    ‖(circuit conv E precision ell).matrix - qftMatrix ell‖ ≤
      ((network ell).length : ℝ) * (4 * bitError precision) := by
  rw [circuit_matrix, qftMatrix, ← standard.network_correct ell]
  exact product_error _ _ _ _
    (fun a _ => compileInstruction_unitary conv E precision a)
    (fun a _ => idealInstruction_unitary conv a)
    (fun a _ => instruction_error conv E precision a)

/-- A bounded-size body in a finite counter loop has the expected literal length. -/
lemma flatten_length_le {α : Type*} (L : List (List α)) (B : ℕ)
    (hL : ∀ C ∈ L, C.length ≤ B) : L.flatten.length ≤ L.length * B := by
  induction L with
  | nil => simp
  | cons C L ih =>
    have hc := hL C (by simp)
    have ht := ih (fun D hD => hL D (by simp [hD]))
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    nlinarith

lemma row_length_le (ell : ℕ) (i : Fin ell) : (row ell i).length ≤ ell+1 := by
  simp only [row, List.length_append, List.length_cons, List.length_nil, List.length_ofFn]
  omega

lemma reversal_length_le (ell : ℕ) : (reversal ell).length ≤ ell := by
  simp only [reversal, List.length_ofFn]
  omega

/-- At most ell(ell+2) fixed-network instructions, including all wire swaps. -/
theorem network_length_le (ell : ℕ) : (network ell).length ≤ ell*(ell+2) := by
  have h := flatten_length_le (List.ofFn (fun i : Fin ell => row ell i)) (ell+1) (by
    intro C hC
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hC
    exact row_length_le ell i)
  have hr := reversal_length_le ell
  simp only [List.length_ofFn] at h
  simp only [network, List.length_append]
  nlinarith

/-- A dimension-free error bound with an explicit polynomial in the Fourier-register size. -/
theorem circuit_error_polynomial {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (standard : StandardQFTCorrectness) (precision ell : ℕ) :
    ‖(circuit conv E precision ell).matrix - qftMatrix ell‖ ≤
      4 * (ell*(ell+2) : ℕ) * bitError precision := by
  have h := circuit_error conv E standard precision ell
  have hc : ((network ell).length : ℝ) ≤ (ell*(ell+2) : ℕ) := by
    exact_mod_cast network_length_le ell
  have hp := mul_le_mul_of_nonneg_right hc (show 0 ≤ 4 * bitError precision by
    exact le_of_lt (mul_pos (by norm_num) (bitError_pos _)))
  nlinarith

lemma network_distance_le (ell : ℕ) (i j : Fin ell) (hij : i ≠ j) (d : ℕ)
    (h : Instruction.phase i j hij d ∈ network ell) : d ≤ ell := by
  simp only [network, List.mem_append, List.mem_flatten, List.mem_ofFn] at h
  rcases h with ⟨C,⟨k,rfl⟩,h⟩ | h
  · simp only [row, List.mem_append, List.mem_singleton, List.mem_ofFn] at h
    rcases h with h | ⟨k',h⟩
    · cases h
    · cases h
      omega
  · simp only [reversal, List.mem_ofFn] at h
    obtain ⟨k,h⟩ := h
    cases h

/-- A local primitive phase budget gives an explicit literal native-list count. -/
theorem native_gate_count {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (precision ell P : ℕ)
    (hphase : ∀ d ≤ ell, (conv.phaseRep (angleRep E precision d)).length ≤ P) :
    (circuit conv E precision ell).length ≤
      ell*(ell+2)*(conv.bound + conv.bound*P + 3*conv.CNOT.length) := by
  have hi (a : Instruction ell) (ha : a ∈ network ell) :
      (compileInstruction conv E precision a).length ≤
        conv.bound + conv.bound*P + 3*conv.CNOT.length := by
    cases a with
    | hadamard i =>
      simp only [compileInstruction, embedCircuit_length]
      have h := conv.hadamard_length 0
      omega
    | phase i j hij d =>
      simp only [compileInstruction, embedCircuit_length]
      have h := controlledCircuit_length conv (conv.phaseRep (angleRep E precision d))
      have hd := hphase d (network_distance_le ell i j hij d ha)
      nlinarith
    | swap i j hij =>
      simp only [compileInstruction, swapAt, cnotAt, List.length_append, embedCircuit_length]
      omega
  have h := flatten_length_le ((network ell).map (compileInstruction conv E precision))
    (conv.bound + conv.bound*P + 3*conv.CNOT.length) (by
      intro C hC
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hC
      exact hi a ha)
  simp only [List.length_map] at h
  exact h.trans (Nat.mul_le_mul_right _ (network_length_le ell))

/-- The inverse QFT is the literal native adjoint list. -/
def inverseCircuit {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (precision ell : ℕ) : EffectiveCircuit G ell :=
  adjointCircuit conv (circuit conv E precision ell)

theorem inverseCircuit_error {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (standard : StandardQFTCorrectness) (precision ell : ℕ) :
    ‖(inverseCircuit conv E precision ell).matrix - (qftMatrix ell).conjTranspose‖ ≤
      4 * (ell*(ell+2) : ℕ) * bitError precision := by
  rw [inverseCircuit, adjointCircuit_matrix, Paper25.MatrixCompilationNorm.adjoint_sub_opNorm]
  exact circuit_error_polynomial conv E standard precision ell

/-- Appending an untouched data register uses precisely the existing Fourier wires. -/
def circuitOnData {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (precision ell q : ℕ) : EffectiveCircuit G (ell+q) :=
  tensorCircuit (circuit conv E precision ell) ([] : EffectiveCircuit G q)

def qftOnData (ell q : ℕ) : Operator (ell+q) :=
  (Matrix.kronecker (qftMatrix ell) (1 : Operator q)).submatrix
    (tensorBits ell q) (tensorBits ell q)

/-- Identity data registers introduce no multiplicative dimension factor. -/
theorem circuitOnData_error {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (standard : StandardQFTCorrectness) (precision ell q : ℕ) :
    ‖(circuitOnData conv E precision ell q).matrix - qftOnData ell q‖ ≤
      4 * (ell*(ell+2) : ℕ) * bitError precision := by
  rw [circuitOnData, tensorCircuit_matrix, qftOnData]
  change ‖(Matrix.kronecker (circuit conv E precision ell).matrix (1 : Operator q)).submatrix
      (tensorBits ell q) (tensorBits ell q) -
    (Matrix.kronecker (qftMatrix ell) (1 : Operator q)).submatrix
      (tensorBits ell q) (tensorBits ell q)‖ ≤ _
  rw [Paper25.MatrixCompilationNorm.submatrix_equiv_error]
  exact (Paper25.MatrixCompilationNorm.tensor_identity_error _ _).trans
    (circuit_error_polynomial conv E standard precision ell)

@[simp] lemma circuitOnData_length {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (precision ell q : ℕ) :
    (circuitOnData conv E precision ell q).length = (circuit conv E precision ell).length := by
  simp [circuitOnData]

lemma flatten_compile_flatten {α β : Type*} (f : α → List β) (L : List (List α)) :
    (L.flatten.map f).flatten = (L.map (fun C => (C.map f).flatten)).flatten := by
  induction L with
  | nil => simp
  | cons C L ih =>
    simp only [List.flatten_cons, List.map_append, List.flatten_append, List.map_cons]
    rw [ih]

/-- The row's actual lists are generated by two valid bounded counters. -/
lemma compiled_row {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (precision ell : ℕ) (i : Fin ell) :
    ((row ell i).map (compileInstruction conv E precision)).flatten =
      compileInstruction conv E precision (.hadamard i) ++
        (List.ofFn (fun d : Fin (ell-(i.val+1)) =>
          compileInstruction conv E precision (.phase (laterWire i d) i (laterWire_ne i d)
            (d.val+1)))).flatten := by
  simp [row, List.map_ofFn, Function.comp_def]

lemma compiled_reversal {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (precision ell : ℕ) :
    ((reversal ell).map (compileInstruction conv E precision)).flatten =
      (List.ofFn (fun i : Fin (ell/2) => swapAt conv (reversalWire ell i)
        (Fin.rev (reversalWire ell i)) (reversalWire_ne ell i))).flatten := by
  simp [reversal, List.map_ofFn, Function.comp_def, compileInstruction]

/-- A fixed template: a row counter, a later-wire counter, and a reversal counter.
Every gate leaf has a valid placement and contains only one local instruction. -/
def recipe {G : EffectiveGateSet} (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    {α : Type} (ell precision : α → ℕ) : CircuitRecipe G α ell :=
  .append
    (.loop ell (.append
      (.leaf (fun p => compileInstruction conv E (precision p.1) (.hadamard p.2)))
      (.loop (fun p => ell p.1-(p.2.val+1)) (.leaf (fun p =>
        compileInstruction conv E (precision p.1.1)
          (.phase (laterWire p.1.2 p.2) p.1.2 (laterWire_ne p.1.2 p.2) (p.2.val+1)))))))
    (.loop (fun a => ell a/2) (.leaf (fun p =>
      swapAt conv (reversalWire (ell p.1) p.2) (Fin.rev (reversalWire (ell p.1) p.2))
        (reversalWire_ne (ell p.1) p.2))))

/-- Interpreting the counter template gives exactly the actual native gate list. -/
theorem recipe_gates {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) {α : Type} (ell precision : α → ℕ) (a : α) :
    (recipe conv E ell precision).gates a = circuit conv E (precision a) (ell a) := by
  simp only [recipe, CircuitRecipe.gates, circuit, network, List.map_append, List.flatten_append,
    flatten_compile_flatten, List.map_ofFn, compiled_reversal]
  congr 1
  congr 2
  funext i
  exact (compiled_row conv E (precision a) (ell a) i).symm

/-- Exact inverse-Fourier target in the same binary coordinate order. -/
lemma inverse_qftMatrix (ell : ℕ) : (qftMatrix ell).conjTranspose =
    (Paper25.inverseFourierMatrix (2^ell)).submatrix
      (Paper25.SelectedFilter.bitsBinaryIndex ell) (Paper25.SelectedFilter.bitsBinaryIndex ell) := by
  simp only [qftMatrix, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_conjTranspose]

/-- The actual inverse-Fourier list on its register with untouched data. -/
def inverseCircuitOnData {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (precision ell q : ℕ) : EffectiveCircuit G (ell+q) :=
  tensorCircuit (inverseCircuit conv E precision ell) ([] : EffectiveCircuit G q)

def inverseQftOnData (ell q : ℕ) : Operator (ell+q) :=
  (Matrix.kronecker (qftMatrix ell).conjTranspose (1 : Operator q)).submatrix
    (tensorBits ell q) (tensorBits ell q)

theorem inverseCircuitOnData_error {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (standard : StandardQFTCorrectness) (precision ell q : ℕ) :
    ‖(inverseCircuitOnData conv E precision ell q).matrix - inverseQftOnData ell q‖ ≤
      4 * (ell*(ell+2) : ℕ) * bitError precision := by
  rw [inverseCircuitOnData, tensorCircuit_matrix, inverseQftOnData]
  change ‖(Matrix.kronecker (inverseCircuit conv E precision ell).matrix (1 : Operator q)).submatrix
      (tensorBits ell q) (tensorBits ell q) -
    (Matrix.kronecker (qftMatrix ell).conjTranspose (1 : Operator q)).submatrix
      (tensorBits ell q) (tensorBits ell q)‖ ≤ _
  rw [Paper25.MatrixCompilationNorm.submatrix_equiv_error]
  exact (Paper25.MatrixCompilationNorm.tensor_identity_error _ _).trans
    (inverseCircuit_error conv E standard precision ell)

/-- The exact targets are unitary because every specified network instruction is unitary. -/
lemma qftMatrix_unitary {G : EffectiveGateSet} (conv : GateConvention G)
    (standard : StandardQFTCorrectness) (ell : ℕ) : OneCleanQubit.Unitary (qftMatrix ell) := by
  rw [qftMatrix, ← standard.network_correct]
  apply product_unitary
  intro U hU
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hU
  exact idealInstruction_unitary conv a

/-- Exact descriptions of three local instruction families and bounded counter
headers. No field asks for a QFT-family generator. The phase count is precisely
the number of later wires, so a guarded whole-circuit leaf is unnecessary. -/
structure CounterDescriptions {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) {α : Type} (ell precision : α → ℕ)
    (encode : α → Input) (header : α → ℕ) : Prop where
  header_computes : LogspaceComputes encode (fun a => encodeNat (header a))
  count_computes : LogspaceComputes encode (fun a => encodeNat (ell a))
  count_polynomial : PolynomialBoundOn encode ell
  inner_header_computes : LogspaceComputes (indexedInput encode ell)
    (fun p => encodeNat (header p.1))
  inner_count_computes : LogspaceComputes (indexedInput encode ell)
    (fun p => encodeNat (ell p.1-(p.2.val+1)))
  inner_count_polynomial : PolynomialBoundOn (indexedInput encode ell) (fun p => ell p.1-(p.2.val+1))
  reversal_count_computes : LogspaceComputes encode (fun a => encodeNat (ell a/2))
  reversal_count_polynomial : PolynomialBoundOn encode (fun a => ell a/2)
  hadamard_computes : LogspaceComputes (indexedInput encode ell)
    (fun p => encodeGateList (header p.1)
      (compileInstruction conv E (precision p.1) (.hadamard p.2)))
  phase_computes : LogspaceComputes
    (indexedInput (indexedInput encode ell) (fun p => ell p.1-(p.2.val+1)))
    (fun p => encodeGateList (header p.1.1)
      (compileInstruction conv E (precision p.1.1)
        (.phase (laterWire p.1.2 p.2) p.1.2 (laterWire_ne p.1.2 p.2) (p.2.val+1))))
  reversal_computes : LogspaceComputes (indexedInput encode (fun a => ell a/2))
    (fun p => encodeGateList (header p.1)
      (swapAt conv (reversalWire (ell p.1) p.2) (Fin.rev (reversalWire (ell p.1) p.2))
        (reversalWire_ne (ell p.1) p.2)))

/-- The concrete double-counter recipe is uniform under only its local
primitive descriptions and ordinary bounded-loop string closure. -/
theorem recipe_uniform {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) {α : Type} (ell precision : α → ℕ)
    (encode : α → Input) (header : α → ℕ)
    (D : CounterDescriptions conv E ell precision encode header) :
    UniformRecipe encode header (recipe conv E ell precision) := by
  unfold recipe
  apply UniformRecipe.append
  · apply UniformRecipe.loop D.header_computes D.count_computes D.count_polynomial
    apply UniformRecipe.append
    · exact UniformRecipe.leaf D.hadamard_computes
    · exact UniformRecipe.loop D.inner_header_computes D.inner_count_computes
        D.inner_count_polynomial (UniformRecipe.leaf D.phase_computes)
  · exact UniformRecipe.loop D.header_computes D.reversal_count_computes D.reversal_count_polynomial
      (UniformRecipe.leaf D.reversal_computes)

/-- Generated output is the concrete gate list, via three local leaves and
fixed nested counters, rather than a supplied whole-Fourier generator. -/
theorem circuit_computes {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (closure : RecipeDescriptionClosure)
    {α : Type} (ell precision : α → ℕ) (encode : α → Input) (header : α → ℕ)
    (D : CounterDescriptions conv E ell precision encode header) :
    LogspaceComputes encode (fun a => encodeGateList (header a)
      (circuit conv E (precision a) (ell a))) := by
  have h := (recipe_uniform conv E ell precision encode header D).generates closure
  simpa only [recipe_gates] using h

/-- Only logarithmically many extra angle-precision bits are needed for all Fourier gates. -/
def precisionFor (ell outputBits : ℕ) : ℕ :=
  outputBits + 2*(Nat.log2 (ell+2)+1)+2

lemma precisionFor_sufficient (ell outputBits : ℕ) :
    4*(ell*(ell+2) : ℕ)*bitError (precisionFor ell outputBits) ≤ bitError outputBits := by
  let k := Nat.log2 (ell+2)+1
  have hbN : ell+2 ≤ 2^k := Nat.le_of_lt ((Nat.log2_lt (by omega : ell+2 ≠ 0)).mp
    (by dsimp [k]; omega))
  have hb : (ell:ℝ)+2 ≤ (2:ℝ)^k := by exact_mod_cast hbN
  have hc : (ell*(ell+2) : ℕ) ≤ ((2:ℝ)^k)^2 := by
    push_cast
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k]
  have he : (2:ℝ)^(precisionFor ell outputBits) =
      (2:ℝ)^outputBits * ((2:ℝ)^k)^2 * 4 := by
    change (2:ℝ)^(outputBits+2*k+2) = _
    rw [pow_add, pow_add, Nat.mul_comm 2 k, pow_mul]
    norm_num
  have hp : (0:ℝ) < 2^outputBits := by positivity
  have hn : (0:ℝ) < 2^(precisionFor ell outputBits) := by positivity
  unfold bitError
  rw [mul_one_div]
  apply (div_le_div_iff₀ hn hp).mpr
  rw [he]
  have hmul := mul_le_mul_of_nonneg_right hc (le_of_lt hp)
  nlinarith

/-- An explicit native QFT approximation to accuracy 2^-outputBits. -/
theorem circuit_error_bits {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (standard : StandardQFTCorrectness) (ell outputBits : ℕ) :
    ‖(circuit conv E (precisionFor ell outputBits) ell).matrix-qftMatrix ell‖ ≤ bitError outputBits :=
  (circuit_error_polynomial conv E standard _ _).trans (precisionFor_sufficient ell outputBits)

/-- The finite maximum of the actual primitive phase-list costs used by this network. -/
def phaseBudget {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (precision ell : ℕ) : ℕ :=
  Finset.univ.sup (fun d : Fin (ell+1) => (conv.phaseRep (angleRep E precision d.val)).length)

lemma phase_length_le_budget {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (precision ell d : ℕ) (hd : d ≤ ell) :
    (conv.phaseRep (angleRep E precision d)).length ≤ phaseBudget conv E precision ell := by
  exact Finset.le_sup (f := fun k : Fin (ell+1) =>
    (conv.phaseRep (angleRep E precision k.val)).length) (Finset.mem_univ ⟨d,by omega⟩)

/-- An unconditional count of the literal lists, in terms of their finite
primitive phase budget, retaining the individual native CNOT cost. -/
theorem native_gate_count_computed {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (precision ell : ℕ) :
    (circuit conv E precision ell).length ≤
      ell*(ell+2)*(conv.bound + conv.bound*(phaseBudget conv E precision ell) +
        3*conv.CNOT.length) :=
  native_gate_count conv E precision ell _ (fun d hd => phase_length_le_budget conv E precision ell d hd)

/-- Literal inversion changes neither the register nor the polynomial instruction
count; its only extra cost is the generic primitive adjoint bound. -/
theorem inverse_native_gate_count {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (precision ell P : ℕ)
    (hphase : ∀ d ≤ ell, (conv.phaseRep (angleRep E precision d)).length ≤ P) :
    (inverseCircuit conv E precision ell).length ≤
      conv.bound*(ell*(ell+2)*(conv.bound+conv.bound*P+3*conv.CNOT.length)) :=
  (adjointCircuit_length conv _).trans
    (Nat.mul_le_mul_left _ (native_gate_count conv E precision ell P hphase))

/-- The same literal gate count applies with an untouched data register. -/
theorem circuitOnData_native_gate_count {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (precision ell q P : ℕ)
    (hphase : ∀ d ≤ ell, (conv.phaseRep (angleRep E precision d)).length ≤ P) :
    (circuitOnData conv E precision ell q).length ≤
      ell*(ell+2)*(conv.bound+conv.bound*P+3*conv.CNOT.length) := by
  rw [circuitOnData_length]
  exact native_gate_count conv E precision ell P hphase

lemma oneWire_encode {ell : ℕ} (i : Fin ell) :
    (oneWire i).encode = encodeNat ell ++ encodeNat 1 ++ encodeNat i.val := by
  have h (k : Fin 1) : (oneWire i).wires (Sum.inl k) = i := by
    change active (oneWire i) k = i
    simp [oneWire]
  simp [Placement.encode, h, List.ofFn_succ]

lemma twoWires_encode {ell : ℕ} (i j : Fin ell) (hij : i ≠ j) :
    (twoWires i j hij).encode = encodeNat ell ++ encodeNat 2 ++ encodeNat i.val ++ encodeNat j.val := by
  have h (k : Fin 2) : (twoWires i j hij).wires (Sum.inl k) = if k=0 then i else j := by
    change active (twoWires i j hij) k = _
    simp [twoWires]
  simp [Placement.encode, h, List.ofFn_succ, List.append_assoc]

open UniformCompilation

/-- Placement descriptions print only an ambient size and the one selected counter. -/
lemma oneWire_computes (classical : FLListClosure) {α : Type} (encode : α → Input)
    (ell : α → ℕ) (i : ∀ a, Fin (ell a))
    (hwidth : LogspaceComputes encode (fun a => encodeNat (ell a)))
    (hi : LogspaceComputes encode (fun a => encodeNat (i a).val)) :
    LogspaceComputes encode (fun a => (oneWire (i a)).encode) := by
  simpa only [oneWire_encode] using classical.strings.concat encode _ _
    (classical.strings.concat encode _ _ hwidth (classical.strings.constant encode (encodeNat 1))) hi

/-- Ordered two-wire placement is only concatenation of explicit unary counters. -/
lemma twoWires_computes (classical : FLListClosure) {α : Type} (encode : α → Input)
    (ell : α → ℕ) (i j : ∀ a, Fin (ell a)) (hij : ∀ a, i a ≠ j a)
    (hwidth : LogspaceComputes encode (fun a => encodeNat (ell a)))
    (hi : LogspaceComputes encode (fun a => encodeNat (i a).val))
    (hj : LogspaceComputes encode (fun a => encodeNat (j a).val)) :
    LogspaceComputes encode (fun a => (twoWires (i a) (j a) (hij a)).encode) := by
  simpa only [twoWires_encode] using classical.strings.concat encode _ _
    (classical.strings.concat encode _ _
      (classical.strings.concat encode _ _ hwidth (classical.strings.constant encode (encodeNat 2))) hi) hj

lemma hadamardInstruction_generated {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    {α : Type} (encode : α → Input) (ell precision : α → ℕ) (i : ∀ a, Fin (ell a))
    (hp : LogspaceComputes encode (fun a => (oneWire (i a)).encode)) :
    GeneratedCircuit encode (fun a => compileInstruction conv E (precision a) (.hadamard (i a))) :=
  embedCircuit_generated classical grammar encode _ _ hp
    (constant_generated classical encode (conv.hadamardAt 0))

/-- This local leaf is derived from raw pi arithmetic, single-phase primitive
printing, generic native controls, and classical wire substitution. -/
lemma phaseInstruction_generated {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (classical : FLListClosure) (numeric : ClassicalDescriptionClosure)
    (grammar : InstructionDescriptionClosure) (primitive : PrimitiveDescriptionConvention conv)
    {α : Type} (encode : α → Input) (ell precision distance : α → ℕ)
    (i j : ∀ a, Fin (ell a)) (hij : ∀ a, i a ≠ j a)
    (hp : LogspaceComputes encode (fun a => (twoWires (i a) (j a) (hij a)).encode))
    (hn : LogspaceComputes encode (fun a => encodeNat (precision a)))
    (hpower : LogspaceComputes encode (fun a => (powerTwoRep (distance a)).encode)) :
    GeneratedCircuit encode (fun a => compileInstruction conv E (precision a)
      (.phase (i a) (j a) (hij a) (distance a))) := by
  apply embedCircuit_generated classical grammar encode _ _ hp
  apply controlledCircuit_generated classical primitive
  exact phaseRep_generated classical primitive encode _
    (angleRep_computes E numeric encode precision distance hn hpower)

lemma cnotAt_generated {G : EffectiveGateSet} (conv : GateConvention G)
    (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    {α : Type} (encode : α → Input) (ell : α → ℕ)
    (i j : ∀ a, Fin (ell a)) (hij : ∀ a, i a ≠ j a)
    (hp : LogspaceComputes encode (fun a => (twoWires (i a) (j a) (hij a)).encode)) :
    GeneratedCircuit encode (fun a => cnotAt conv (i a) (j a) (hij a)) :=
  embedCircuit_generated classical grammar encode _ _ hp (constant_generated classical encode conv.CNOT)

lemma swapAt_generated {G : EffectiveGateSet} (conv : GateConvention G)
    (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    {α : Type} (encode : α → Input) (ell : α → ℕ)
    (i j : ∀ a, Fin (ell a)) (hij : ∀ a, i a ≠ j a)
    (hp : LogspaceComputes encode (fun a => (twoWires (i a) (j a) (hij a)).encode))
    (hr : LogspaceComputes encode (fun a => (twoWires (j a) (i a) (hij a).symm).encode)) :
    GeneratedCircuit encode (fun a => swapAt conv (i a) (j a) (hij a)) := by
  have hC := cnotAt_generated conv classical grammar encode ell i j hij hp
  have hR := cnotAt_generated conv classical grammar encode ell j i (fun a => (hij a).symm) hr
  simpa only [swapAt, List.append_assoc] using append_generated classical encode _ _ hC
    (append_generated classical encode _ _ hR hC)

/-- Only pure counter/string requests remain: unary headers, sizes and indices,
and the binary fraction 2^(d+1)/1. No circuit, matrix or Fourier semantics occurs
in these query-machine premises. The indexed contexts are fixed by the recipe. -/
structure CounterQueries {α : Type} (ell precision : α → ℕ)
    (encode : α → Input) (header : α → ℕ) : Prop where
  header_query : LogspaceComputes encode (fun a => encodeNat (header a))
  count : LogspaceComputes encode (fun a => encodeNat (ell a))
  count_poly : PolynomialBoundOn encode ell
  row_header : LogspaceComputes (indexedInput encode ell) (fun p => encodeNat (header p.1))
  row_width : LogspaceComputes (indexedInput encode ell) (fun p => encodeNat (ell p.1))
  row_index : LogspaceComputes (indexedInput encode ell) (fun p => encodeNat p.2.val)
  inner_count : LogspaceComputes (indexedInput encode ell) (fun p => encodeNat (ell p.1-(p.2.val+1)))
  inner_poly : PolynomialBoundOn (indexedInput encode ell) (fun p => ell p.1-(p.2.val+1))
  phase_header : LogspaceComputes
    (indexedInput (indexedInput encode ell) (fun p => ell p.1-(p.2.val+1)))
    (fun p => encodeNat (header p.1.1))
  phase_width : LogspaceComputes
    (indexedInput (indexedInput encode ell) (fun p => ell p.1-(p.2.val+1)))
    (fun p => encodeNat (ell p.1.1))
  phase_later : LogspaceComputes
    (indexedInput (indexedInput encode ell) (fun p => ell p.1-(p.2.val+1)))
    (fun p => encodeNat (laterWire p.1.2 p.2).val)
  phase_earlier : LogspaceComputes
    (indexedInput (indexedInput encode ell) (fun p => ell p.1-(p.2.val+1)))
    (fun p => encodeNat p.1.2.val)
  phase_precision : LogspaceComputes
    (indexedInput (indexedInput encode ell) (fun p => ell p.1-(p.2.val+1)))
    (fun p => encodeNat (precision p.1.1))
  phase_distance : LogspaceComputes
    (indexedInput (indexedInput encode ell) (fun p => ell p.1-(p.2.val+1)))
    (fun p => encodeNat (p.2.val+1))
  reversal_count : LogspaceComputes encode (fun a => encodeNat (ell a/2))
  reversal_poly : PolynomialBoundOn encode (fun a => ell a/2)
  reversal_header : LogspaceComputes (indexedInput encode (fun a => ell a/2))
    (fun p => encodeNat (header p.1))
  reversal_width : LogspaceComputes (indexedInput encode (fun a => ell a/2))
    (fun p => encodeNat (ell p.1))
  reversal_first : LogspaceComputes (indexedInput encode (fun a => ell a/2))
    (fun p => encodeNat (reversalWire (ell p.1) p.2).val)
  reversal_last : LogspaceComputes (indexedInput encode (fun a => ell a/2))
    (fun p => encodeNat (Fin.rev (reversalWire (ell p.1) p.2)).val)

lemma powerTwoRep_computes (numeric : ClassicalDescriptionClosure) (shift : BinaryShiftDescription)
    {α : Type} (encode : α → Input) (distance : α → ℕ)
    (hd : LogspaceComputes encode (fun a => encodeNat (distance a))) :
    LogspaceComputes encode (fun a => (powerTwoRep (distance a)).encode) := by
  have hs : LogspaceComputes encodeNat (fun d => (powerTwoRep d).encode) := shift.powerTwo
  exact numeric.compose encode encodeNat distance (fun d => (powerTwoRep d).encode) hd hs

/-- All three local quantum leaf descriptions follow from raw elementary
primitives and pure counter queries; none remains an independent QFT premise. -/
theorem counterDescriptions_of_queries {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (classical : FLListClosure) (numeric : ClassicalDescriptionClosure)
    (grammar : InstructionDescriptionClosure) (primitive : PrimitiveDescriptionConvention conv)
    (shift : BinaryShiftDescription) {α : Type} (ell precision : α → ℕ) (encode : α → Input) (header : α → ℕ)
    (Q : CounterQueries ell precision encode header) :
    CounterDescriptions conv E ell precision encode header where
  header_computes := Q.header_query
  count_computes := Q.count
  count_polynomial := Q.count_poly
  inner_header_computes := Q.row_header
  inner_count_computes := Q.inner_count
  inner_count_polynomial := Q.inner_poly
  reversal_count_computes := Q.reversal_count
  reversal_count_polynomial := Q.reversal_poly
  hadamard_computes := generated_logspace grammar _ _ _ Q.row_header
    (hadamardInstruction_generated conv E classical grammar _ _ _ _
      (oneWire_computes classical _ _ _ Q.row_width Q.row_index))
  phase_computes := generated_logspace grammar _ _ _ Q.phase_header
    (phaseInstruction_generated conv E classical numeric grammar primitive _ _ _ _ _ _ _
      (twoWires_computes classical _ _ _ _ _ Q.phase_width Q.phase_later Q.phase_earlier)
      Q.phase_precision (powerTwoRep_computes numeric shift _ _ Q.phase_distance))
  reversal_computes := generated_logspace grammar _ _ _ Q.reversal_header
    (swapAt_generated conv classical grammar _ _ _ _ _
      (twoWires_computes classical _ _ _ _ _ Q.reversal_width Q.reversal_first Q.reversal_last)
      (twoWires_computes classical _ _ _ _ _ Q.reversal_width Q.reversal_last Q.reversal_first))

/-- Native QFT-family description generation uses the published elementary
numeric primitive interface and fixed pure-counter requests only. -/
theorem circuit_computes_from_primitives {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (classical : FLListClosure) (numeric : ClassicalDescriptionClosure)
    (grammar : InstructionDescriptionClosure) (primitive : PrimitiveDescriptionConvention conv)
    (shift : BinaryShiftDescription) (closure : RecipeDescriptionClosure) {α : Type} (ell precision : α → ℕ)
    (encode : α → Input) (header : α → ℕ) (Q : CounterQueries ell precision encode header) :
    LogspaceComputes encode (fun a => encodeGateList (header a)
      (circuit conv E (precision a) (ell a))) :=
  circuit_computes conv E closure ell precision encode header
    (counterDescriptions_of_queries conv E classical numeric grammar primitive shift ell precision encode header Q)

/-- With the elementary parameter-gate convention, native gate count is
polynomial in ell uniformly over all numerical precisions. Phase payload bytes
are accounted for separately by the genuine primitive description machines. -/
theorem native_gate_count_polynomial {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (precision ell : ℕ) :
    (circuit conv E precision ell).length ≤
      ell*(ell+2)*(conv.bound+conv.bound^2+3*conv.CNOT.length) := by
  simpa only [pow_two] using native_gate_count conv E precision ell conv.bound
    (fun d _ => conv.phaseRep_length _)

theorem circuitOnData_gate_count_polynomial {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (precision ell q : ℕ) :
    (circuitOnData conv E precision ell q).length ≤
      ell*(ell+2)*(conv.bound+conv.bound^2+3*conv.CNOT.length) := by
  rw [circuitOnData_length]
  exact native_gate_count_polynomial conv E precision ell

/-- An actual native QFT on exactly the existing ell wires: legal unitary,
explicit dyadic accuracy, and a quadratic gate bound. -/
theorem native_qft {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (standard : StandardQFTCorrectness) (ell outputBits : ℕ) :
    OneCleanQubit.Unitary (circuit conv E (precisionFor ell outputBits) ell).matrix ∧
    ‖(circuit conv E (precisionFor ell outputBits) ell).matrix-qftMatrix ell‖ ≤ bitError outputBits ∧
    (circuit conv E (precisionFor ell outputBits) ell).length ≤
      ell*(ell+2)*(conv.bound+conv.bound^2+3*conv.CNOT.length) :=
  ⟨EffectiveCircuit.unitary _, circuit_error_bits conv E standard ell outputBits,
    native_gate_count_polynomial conv E _ ell⟩

/-- A fixed unary pair grammar for ordinary counter arithmetic. -/
def unaryPairInput (p : ℕ × ℕ) : Input :=
  encodeNat (encodeNat p.1).length ++ encodeNat p.1 ++ encodeNat p.2

/-- Standard classical counter machines only: unary addition, truncated
subtraction, and division by two. These inputs contain no gate or matrix. -/
structure UnaryCounterArithmetic : Prop where
  add : LogspaceComputes unaryPairInput (fun p => encodeNat (p.1+p.2))
  sub : LogspaceComputes unaryPairInput (fun p => encodeNat (p.1-p.2))
  half : LogspaceComputes encodeNat (fun n => encodeNat (n/2))

lemma unary_binary_computes (numeric : ClassicalDescriptionClosure) {α : Type}
    (encode : α → Input) (f g : α → ℕ) (op : ℕ → ℕ → ℕ)
    (hf : LogspaceComputes encode (fun a => encodeNat (f a)))
    (hg : LogspaceComputes encode (fun a => encodeNat (g a)))
    (hop : LogspaceComputes unaryPairInput (fun p => encodeNat (op p.1 p.2))) :
    LogspaceComputes encode (fun a => encodeNat (op (f a) (g a))) :=
  numeric.compose encode unaryPairInput (fun a => (f a,g a)) _
    (numeric.pair encode _ _ hf hg) hop

lemma unary_succ_computes (numeric : ClassicalDescriptionClosure) (arithmetic : UnaryCounterArithmetic)
    {α : Type} (encode : α → Input) (f : α → ℕ)
    (hf : LogspaceComputes encode (fun a => encodeNat (f a))) :
    LogspaceComputes encode (fun a => encodeNat (f a+1)) :=
  unary_binary_computes numeric encode f (fun _ => 1) (·+·) hf
    (numeric.constant encode (encodeNat 1)) arithmetic.add

lemma indexed_pullback_computes (classical : FLListClosure) {α : Type}
    (encode : α → Input) (count : α → ℕ) (output : α → Input)
    (h : LogspaceComputes encode output) :
    LogspaceComputes (indexedInput encode count) (fun p => output p.1) :=
  classical.strings.compose (indexedInput encode count) encode Sigma.fst output
    (indexed_input_generated classical encode count) h

lemma polynomial_indexed_pullback {α : Type} (encode : α → Input) (count f : α → ℕ)
    (hf : PolynomialBoundOn encode f) :
    PolynomialBoundOn (indexedInput encode count) (fun p => f p.1) := by
  obtain ⟨C,d,hf⟩ := hf
  refine ⟨C,d,fun p => (hf p.1).trans ?_⟩
  have hl : (encode p.1).length+1 ≤ (indexedInput encode count p).length+1 := by
    simp only [indexedInput, List.length_append]
    omega
  gcongr

lemma polynomial_counter_mono {α : Type} (encode : α → Input) (f g : α → ℕ)
    (hfg : ∀ a, f a ≤ g a) (hg : PolynomialBoundOn encode g) : PolynomialBoundOn encode f := by
  obtain ⟨C,d,hg⟩ := hg
  exact ⟨C,d,fun a => (hfg a).trans (hg a)⟩

/-- Every query in the fixed template is obtained from ordinary unary
counter machines and generic indexed-input parsing. Only the caller's register
size, requested numerical precision, and output header need base generators. -/
theorem counterQueries_of_arithmetic (classical : FLListClosure) (numeric : ClassicalDescriptionClosure)
    (arithmetic : UnaryCounterArithmetic) {α : Type} (ell precision : α → ℕ)
    (encode : α → Input) (header : α → ℕ)
    (hell : LogspaceComputes encode (fun a => encodeNat (ell a)))
    (hprecision : LogspaceComputes encode (fun a => encodeNat (precision a)))
    (hheader : LogspaceComputes encode (fun a => encodeNat (header a)))
    (hpoly : PolynomialBoundOn encode ell) : CounterQueries ell precision encode header := by
  let R := Σ a : α, Fin (ell a)
  let rowCode : R → Input := indexedInput encode ell
  let inner : R → ℕ := fun p => ell p.1-(p.2.val+1)
  let P := Σ p : R, Fin (inner p)
  let phaseCode : P → Input := indexedInput rowCode inner
  let V := Σ a : α, Fin (ell a/2)
  let reversalCode : V → Input := indexedInput encode (fun a => ell a/2)
  have hrowWidth := indexed_pullback_computes classical encode ell _ hell
  have hrowHeader := indexed_pullback_computes classical encode ell _ hheader
  have hrowPrecision := indexed_pullback_computes classical encode ell _ hprecision
  have hrowIndex := indexed_counter_generated classical encode ell
  have hrowSucc := unary_succ_computes numeric arithmetic rowCode (fun p => p.2.val) hrowIndex
  have hinner : LogspaceComputes rowCode (fun p => encodeNat (inner p)) :=
    unary_binary_computes numeric rowCode _ _ (·-·) hrowWidth hrowSucc arithmetic.sub
  have hinnerPoly : PolynomialBoundOn rowCode inner :=
    polynomial_counter_mono rowCode inner (fun p => ell p.1) (fun p => Nat.sub_le _ _)
      (polynomial_indexed_pullback encode ell ell hpoly)
  have hphaseWidth := indexed_pullback_computes classical rowCode inner _ hrowWidth
  have hphaseHeader := indexed_pullback_computes classical rowCode inner _ hrowHeader
  have hphasePrecision := indexed_pullback_computes classical rowCode inner _ hrowPrecision
  have hphaseEarlier := indexed_pullback_computes classical rowCode inner _ hrowIndex
  have hphaseSucc := indexed_pullback_computes classical rowCode inner _ hrowSucc
  have hphaseIndex := indexed_counter_generated classical rowCode inner
  have hphaseDistance := unary_succ_computes numeric arithmetic phaseCode (fun p => p.2.val) hphaseIndex
  have hphaseLater := unary_binary_computes numeric phaseCode _ _ (·+·) hphaseSucc hphaseIndex arithmetic.add
  have hrevCount : LogspaceComputes encode (fun a => encodeNat (ell a/2)) :=
    numeric.compose encode encodeNat ell (fun n => encodeNat (n/2)) hell arithmetic.half
  have hrevPoly : PolynomialBoundOn encode (fun a => ell a/2) :=
    polynomial_counter_mono encode _ ell (fun a => Nat.div_le_self _ _) hpoly
  have hrevWidth := indexed_pullback_computes classical encode (fun a => ell a/2) _ hell
  have hrevHeader := indexed_pullback_computes classical encode (fun a => ell a/2) _ hheader
  have hrevIndex := indexed_counter_generated classical encode (fun a => ell a/2)
  have hrevSucc := unary_succ_computes numeric arithmetic reversalCode (fun p => p.2.val) hrevIndex
  have hrevLast := unary_binary_computes numeric reversalCode _ _ (·-·) hrevWidth hrevSucc arithmetic.sub
  exact {
    header_query := hheader
    count := hell
    count_poly := hpoly
    row_header := hrowHeader
    row_width := hrowWidth
    row_index := hrowIndex
    inner_count := hinner
    inner_poly := hinnerPoly
    phase_header := hphaseHeader
    phase_width := hphaseWidth
    phase_later := hphaseLater
    phase_earlier := hphaseEarlier
    phase_precision := hphasePrecision
    phase_distance := hphaseDistance
    reversal_count := hrevCount
    reversal_poly := hrevPoly
    reversal_header := hrevHeader
    reversal_width := hrevWidth
    reversal_first := hrevIndex
    reversal_last := hrevLast }

/-- Complete description generation from single elementary-gate emitters,
standard classical string/counter operations, and the caller's three basic
parameter machines. No whole Fourier-family generator is an input. -/
theorem circuit_computes_standard {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (classical : FLListClosure) (numeric : ClassicalDescriptionClosure)
    (grammar : InstructionDescriptionClosure) (primitive : PrimitiveDescriptionConvention conv)
    (shift : BinaryShiftDescription) (arithmetic : UnaryCounterArithmetic)
    (closure : RecipeDescriptionClosure) {α : Type} (ell precision : α → ℕ)
    (encode : α → Input) (header : α → ℕ)
    (hell : LogspaceComputes encode (fun a => encodeNat (ell a)))
    (hprecision : LogspaceComputes encode (fun a => encodeNat (precision a)))
    (hheader : LogspaceComputes encode (fun a => encodeNat (header a)))
    (hpoly : PolynomialBoundOn encode ell) :
    LogspaceComputes encode (fun a => encodeGateList (header a)
      (circuit conv E (precision a) (ell a))) :=
  circuit_computes_from_primitives conv E classical numeric grammar primitive shift closure
    ell precision encode header
    (counterQueries_of_arithmetic classical numeric arithmetic ell precision encode header
      hell hprecision hheader hpoly)

end Paper25.OperationalModel.FourierCompilation

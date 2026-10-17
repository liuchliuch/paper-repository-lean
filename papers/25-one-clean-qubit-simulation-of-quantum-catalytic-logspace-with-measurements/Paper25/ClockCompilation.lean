import Paper25.LocalCompilation
import Paper25.SelectedPreparation
import Paper25.SourceControl
import Mathlib.Logic.Equiv.Fin.Rotate

/-! An ancilla-free ripple increment on the actual binary clock register.
The only elementary operations are the X list and pattern-controlled elementary
lists supplied by the paper's effective gate convention. -/
noncomputable section
open Matrix
namespace Paper25.OperationalModel.ClockCompilation
open LocalCompilation StatePreparation SelectedFilter
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000

/-- The suffix on which a carry reaches the next more significant bit. -/
def ones (ell : ℕ) : Basis ell := fun _ => 1

/-- Binary increment as a permutation of the physical register. -/
def incrementEquiv (ell : ℕ) : Equiv.Perm (Basis ell) :=
  (bitsBinaryIndex ell).trans ((finRotate (2^ell)).trans (bitsBinaryIndex ell).symm)

@[simp] lemma incrementEquiv_index (ell : ℕ) (x : Basis ell) :
    bitsBinaryIndex ell (incrementEquiv ell x) = finRotate (2^ell) (bitsBinaryIndex ell x) := by
  simp [incrementEquiv]

lemma index_succ_val (ell : ℕ) (x : Basis (ell+1)) :
    (bitsBinaryIndex (ell+1) x).val =
      (bitsBinaryIndex ell (fun i => x i.succ)).val + 2^ell * (x 0).val := rfl

lemma index_ones (ell : ℕ) : (bitsBinaryIndex ell (ones ell)).val = 2^ell-1 := by
  induction ell with
  | zero => rfl
  | succ ell ih =>
    rw [index_succ_val]
    change (bitsBinaryIndex ell (ones ell)).val + 2^ell * 1 = 2^(ell+1)-1
    rw [ih, Nat.pow_succ]
    have hp : 0 < 2^ell := by positivity
    omega

lemma tail_eq_ones_iff (ell : ℕ) (x : Basis ell) :
    x = ones ell ↔ (bitsBinaryIndex ell x).val = 2^ell-1 := by
  rw [← index_ones ell]
  exact ⟨fun h => congrArg (fun y => (bitsBinaryIndex ell y).val) h,
    fun h => (bitsBinaryIndex ell).injective (Fin.ext h)⟩

lemma rotate_val {n : ℕ} (hn : 0<n) (i : Fin n) :
    (finRotate n i).val = if i.val = n-1 then 0 else i.val+1 := by
  cases n with
  | zero => omega
  | succ n =>
    rw [coe_finRotate]
    have he : i = Fin.last n ↔ i.val = n := by
      constructor
      · intro h; simp [h]
      · intro h; exact Fin.ext h
    simp only [Nat.add_sub_cancel, he]

/-- Flip the leading bit exactly when all of the old suffix bits are one. -/
def carryPair (ell : ℕ) : Equiv.Perm (Bit × Basis ell) where
  toFun p := (if p.2 = ones ell then p.1 + 1 else p.1, p.2)
  invFun p := (if p.2 = ones ell then p.1 + 1 else p.1, p.2)
  left_inv p := by
    rcases p with ⟨b,t⟩
    by_cases h : t = ones ell <;> simp only [h, if_true, if_false]
    · apply Prod.ext
      · fin_cases b <;> rfl
      · rfl
  right_inv p := by
    rcases p with ⟨b,t⟩
    by_cases h : t = ones ell <;> simp only [h, if_true, if_false]
    · apply Prod.ext
      · fin_cases b <;> rfl
      · rfl

def carryEquiv (ell : ℕ) : Equiv.Perm (Basis (ell+1)) :=
  (splitBits ell).trans ((carryPair ell).trans (splitBits ell).symm)

def tailEquiv (ell : ℕ) : Equiv.Perm (Basis (ell+1)) :=
  (splitBits ell).trans
    (((Equiv.refl Bit).prodCongr (incrementEquiv ell)).trans (splitBits ell).symm)

@[simp] lemma carryEquiv_head (ell : ℕ) (x : Basis (ell+1)) :
    carryEquiv ell x 0 = if (fun i : Fin ell => x i.succ) = ones ell then x 0+1 else x 0 := by
  rfl

@[simp] lemma carryEquiv_tail (ell : ℕ) (x : Basis (ell+1)) (i : Fin ell) :
    carryEquiv ell x i.succ = x i.succ := rfl

@[simp] lemma tailEquiv_head (ell : ℕ) (x : Basis (ell+1)) :
    tailEquiv ell x 0 = x 0 := rfl

@[simp] lemma tailEquiv_tail (ell : ℕ) (x : Basis (ell+1)) (i : Fin ell) :
    tailEquiv ell x i.succ = incrementEquiv ell (fun j => x j.succ) i := rfl

/-- The high-bit carry is performed before incrementing the suffix, so every
control tests an old input bit. -/
lemma ripple_equiv (ell : ℕ) :
    (carryEquiv ell).trans (tailEquiv ell) = incrementEquiv (ell+1) := by
  apply Equiv.ext
  intro x
  apply (bitsBinaryIndex (ell+1)).injective
  rw [incrementEquiv_index]
  apply Fin.ext
  rw [index_succ_val, rotate_val (by positivity), index_succ_val]
  change (bitsBinaryIndex ell (incrementEquiv ell (fun i => x i.succ))).val +
      2^ell * (if (fun i : Fin ell => x i.succ) = ones ell then x 0+1 else x 0).val = _
  rw [incrementEquiv_index, rotate_val (by positivity)]
  have ht := (bitsBinaryIndex ell (fun i => x i.succ)).isLt
  have hp : 0 < 2^ell := by positivity
  have ho := tail_eq_ones_iff ell (fun i => x i.succ)
  have hb := (x 0).isLt
  rw [Nat.pow_succ]
  have hbits : ∀ b : Bit, b = 0 ∨ b = 1 := by intro b; fin_cases b <;> simp
  have h01 : (0+1 : Bit) = 1 := rfl
  have h11 : (1+1 : Bit) = 0 := rfl
  by_cases hc : (fun i : Fin ell => x i.succ) = ones ell
  · have hv := ho.mp hc
    rw [if_pos hc, if_pos hv]
    have hx := hbits (x 0)
    rcases hx with hx | hx <;>
      simp only [hx, h01, h11, Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.mul_one, Nat.zero_add]
    all_goals split_ifs <;> omega
  · have hv : (bitsBinaryIndex ell (fun i => x i.succ)).val ≠ 2^ell-1 := by
      intro hv; exact hc (ho.mpr hv)
    rw [if_neg hc, if_neg hv]
    have hx := hbits (x 0)
    rcases hx with hx | hx <;>
      simp only [hx, Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.mul_one]
    all_goals split_ifs <;> omega

lemma permutation_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Equiv.Perm ι) (x y : ι) :
    KrausChannel.reversibleGate e x y = if x = e y then 1 else 0 := by
  simp [KrausChannel.reversibleGate, Matrix.one_apply, Equiv.symm_apply_eq]

lemma permutation_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e f : Equiv.Perm ι) :
    KrausChannel.reversibleGate f * KrausChannel.reversibleGate e =
      KrausChannel.reversibleGate (e.trans f) := by
  ext x y
  simp [Matrix.mul_apply, permutation_entry, mul_ite, Finset.sum_ite_eq', Equiv.trans_apply]


/-- Virtual controls occupy the low suffix, and the virtual target is the
physical most significant bit. This is a permutation of wire positions. -/
def carryWires (ell : ℕ) : Fin (ell+1) ↪ Fin (ell+1) :=
  (finRotate (ell+1)).toEmbedding

lemma carryWires_control (ell : ℕ) (i : Fin ell) :
    carryWires ell (Fin.castAdd 1 i) = i.succ := by
  apply Fin.ext
  change (finRotate (ell+1) (Fin.castAdd 1 i)).val = i.val+1
  rw [rotate_val (by omega)]
  have hi := i.isLt
  simp only [Fin.coe_castAdd, Nat.add_sub_cancel]
  rw [if_neg (by omega)]

lemma carryWires_target (ell : ℕ) (i : Fin 1) :
    carryWires ell (Fin.natAdd ell i) = 0 := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  apply Fin.ext
  change (finRotate (ell+1) (Fin.natAdd ell (0 : Fin 1))).val = 0
  rw [rotate_val (by omega)]
  simp

lemma carry_register (ell : ℕ) (x : Basis (ell+1)) :
    registerBasis ell 1 (fun i => x (carryWires ell i)) =
      ((fun i : Fin ell => x i.succ), (fun _ : Fin 1 => x 0)) := by
  apply Prod.ext
  · funext i
    change x (carryWires ell (finSumFinEquiv (Sum.inl i))) = x i.succ
    simp [carryWires_control]
  · funext i
    change x (carryWires ell (finSumFinEquiv (Sum.inr i))) = x 0
    simp [carryWires_target]

lemma carry_inactive (ell : ℕ) (x y : Basis (ell+1)) :
    Inactive (carryWires ell) x y := by
  intro j hj
  exact False.elim (hj ⟨(finRotate (ell+1)).symm j,
    (finRotate (ell+1)).apply_symm_apply j⟩)

/-- One physical carry update, compiled from pattern-controlled X gates. -/
def carryCircuit {G : EffectiveGateSet} (conv : GateConvention G) (ell : ℕ) :
    EffectiveCircuit G (ell+1) :=
  embedCircuit (placementOfEmbedding (carryWires ell))
    (patternCircuit conv ell (ones ell) conv.X)

lemma carryCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) (ell : ℕ) :
    (carryCircuit conv ell).matrix = KrausChannel.reversibleGate (carryEquiv ell) := by
  rw [carryCircuit, embedCircuit_matrix, patternCircuit_matrix, conv.X_matrix]
  ext x y
  rw [lift_apply]
  simp only [active_placementOfEmbedding_eq, if_pos (carry_inactive ell x y), mul_one,
    physicalPattern, Matrix.submatrix_apply, carry_register, patternBlock,
    Paper25.selectMatrix, permutation_entry, bits_eq_iff, carryEquiv_head,
    carryEquiv_tail]
  have hsingle : (fun _ : Fin 1 => x 0) = (fun _ : Fin 1 => y 0) ↔ x 0 = y 0 := by
    constructor
    · intro h; exact congrFun h 0
    · intro h; simp only [h]
  by_cases ht : (fun i : Fin ell => x i.succ) = (fun i => y i.succ)
  · simp only [ht, if_true, and_true]
    by_cases hc : (fun i : Fin ell => y i.succ) = ones ell
    · simp only [hc, if_true]
      have hbits : ∀ b : Bit, b = 0 ∨ b = 1 := by intro b; fin_cases b <;> simp
      rcases hbits (x 0) with hx | hx <;> rcases hbits (y 0) with hy | hy <;>
        simp [LocalCompilation.pauliX, hx, hy, show (0+1 : Bit) = 1 from rfl,
          show (1+1 : Bit) = 0 from rfl]
    · simp only [hc, if_false, Matrix.one_apply, hsingle]
  · simp [ht]

/-- The recursive suffix uses exactly the remaining physical wires. -/
def tailWires (ell : ℕ) : Fin ell ↪ Fin (ell+1) where
  toFun := Fin.succ
  inj' := Fin.succ_injective _

lemma tail_inactive (ell : ℕ) (x y : Basis (ell+1)) :
    Inactive (tailWires ell) x y ↔ x 0 = y 0 := by
  constructor
  · intro h
    apply h 0
    rintro ⟨i,hi⟩
    exact Fin.succ_ne_zero i hi
  · intro h j hj
    rcases Fin.eq_zero_or_eq_succ j with hj0 | ⟨i,hi⟩
    · simpa only [hj0] using h
    · exact False.elim (hj ⟨i,hi.symm⟩)

lemma tail_lift (ell : ℕ) :
    (placementOfEmbedding (tailWires ell)).lift
        (KrausChannel.reversibleGate (incrementEquiv ell)) =
      KrausChannel.reversibleGate (tailEquiv ell) := by
  ext x y
  rw [lift_apply]
  simp only [active_placementOfEmbedding_eq]
  rw [tail_inactive]
  simp only [permutation_entry, bits_eq_iff, tailEquiv_head, tailEquiv_tail, tailWires]
  by_cases hh : x 0 = y 0 <;>
    by_cases ht : (fun i : Fin ell => x i.succ) = incrementEquiv ell (fun i => y i.succ) <;>
    simp [hh,ht]

/-- Increment modulo 2^ell with no ancilla: update the highest carry bit first,
then run the same circuit on the suffix. -/
def increment {G : EffectiveGateSet} (conv : GateConvention G) :
    (ell : ℕ) → EffectiveCircuit G ell
  | 0 => []
  | ell+1 => carryCircuit conv ell ++
      embedCircuit (placementOfEmbedding (tailWires ell)) (increment conv ell)

lemma increment_permutation {G : EffectiveGateSet} (conv : GateConvention G) (ell : ℕ) :
    (increment conv ell).matrix = KrausChannel.reversibleGate (incrementEquiv ell) := by
  induction ell with
  | zero =>
    ext x y
    have hxy : x = y := Subsingleton.elim _ _
    have hinc : incrementEquiv 0 y = y := Subsingleton.elim _ _
    simp [increment, EffectiveCircuit.matrix, permutation_entry, hinc, hxy]
  | succ ell ih =>
    rw [increment, EffectiveCircuit.matrix_append, embedCircuit_matrix, ih,
      tail_lift, carryCircuit_matrix, permutation_mul, ripple_equiv]

/-- Exact clock matrix in the paper's binary computational basis. -/
theorem increment_matrix {G : EffectiveGateSet} (conv : GateConvention G) (ell : ℕ) :
    (increment conv ell).matrix =
      (KrausChannel.reversibleGate (finRotate (2^ell))).submatrix
        (bitsBinaryIndex ell) (bitsBinaryIndex ell) := by
  rw [increment_permutation]
  ext x y
  simp only [Matrix.submatrix_apply, permutation_entry]
  have he : bitsBinaryIndex ell x = finRotate (2^ell) (bitsBinaryIndex ell y) ↔
      x = incrementEquiv ell y := by
    rw [← incrementEquiv_index]
    exact (bitsBinaryIndex ell).injective.eq_iff
  simp only [he]

lemma carryCircuit_length {G : EffectiveGateSet} (conv : GateConvention G) (ell : ℕ) :
    (carryCircuit conv ell).length ≤ conv.bound^(ell+1) * conv.X.length := by
  rw [carryCircuit, embedCircuit_length]
  exact patternCircuit_length conv ell (ones ell) conv.X

/-- A fixed gate convention gives an exponential-in-clock-width bound, hence a
polynomial bound in the number of clock states. -/
theorem increment_length {G : EffectiveGateSet} (conv : GateConvention G) (ell : ℕ) :
    (increment conv ell).length ≤ ell * conv.bound^ell * conv.X.length := by
  induction ell with
  | zero => simp [increment]
  | succ ell ih =>
    rw [increment, List.length_append, embedCircuit_length]
    have hpow : conv.bound^ell ≤ conv.bound^(ell+1) :=
      Nat.pow_le_pow_right conv.bound_pos (by omega)
    calc
      (carryCircuit conv ell).length + (increment conv ell).length ≤
          conv.bound^(ell+1)*conv.X.length + ell*conv.bound^ell*conv.X.length :=
        Nat.add_le_add (carryCircuit_length conv ell) ih
      _ ≤ conv.bound^(ell+1)*conv.X.length + ell*conv.bound^(ell+1)*conv.X.length :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left ell hpow)) _
      _ = (ell+1)*conv.bound^(ell+1)*conv.X.length := by ring


lemma rotate_finCongr {m n : ℕ} (h : m = n) (i : Fin m) :
    finCongr h (finRotate m i) = finRotate n (finCongr h i) := by
  subst n
  rfl

/-- The same result in the zero-preserving coordinates used by history readout. -/
theorem increment_clockIndex_matrix {G : EffectiveGateSet}
    (conv : GateConvention G) (ell : ℕ) :
    (increment conv ell).matrix =
      (KrausChannel.reversibleGate (finRotate (Fintype.card (Bits ell)))).submatrix
        (clockIndex ell) (clockIndex ell) := by
  rw [increment_matrix]
  ext x y
  simp only [Matrix.submatrix_apply, permutation_entry]
  have h : 2^ell = Fintype.card (Bits ell) := by simp [Bits]
  have he (z : Bits ell) : clockIndex ell z = finCongr h (bitsBinaryIndex ell z) := rfl
  rw [he x, he y, ← rotate_finCongr h]
  simp only [(finCongr h).injective.eq_iff]

lemma self_le_binary_power (n : ℕ) : n ≤ 2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.pow_succ]
    have hp : 1 ≤ 2^n := Nat.one_le_two_pow
    omega

/-- The number of gates is polynomial in the number 2^ell of clock states;
the coefficient and exponent depend only on the fixed elementary convention. -/
theorem increment_length_states {G : EffectiveGateSet}
    (conv : GateConvention G) (ell : ℕ) :
    (increment conv ell).length ≤ (2^ell)^(conv.bound+1) * conv.X.length := by
  apply (increment_length conv ell).trans
  have hb : conv.bound^ell ≤ (2^ell)^conv.bound := by
    calc
      conv.bound^ell ≤ (2^conv.bound)^ell :=
        Nat.pow_le_pow_left (self_le_binary_power conv.bound) ell
      _ = (2^ell)^conv.bound := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  calc
    ell * conv.bound^ell * conv.X.length ≤
        (2^ell) * (2^ell)^conv.bound * conv.X.length :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (self_le_binary_power ell) hb)
    _ = (2^ell)^(conv.bound+1) * conv.X.length := by rw [pow_succ, mul_comm (2^ell)]

end Paper25.OperationalModel.ClockCompilation

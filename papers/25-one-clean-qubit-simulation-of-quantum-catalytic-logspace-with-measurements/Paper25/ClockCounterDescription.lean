import Paper25.ClassicalDataCompilation
import Paper25.ClockUniformCompilation

/-!
# Deriving the ripple-clock counter queries from generic byte arithmetic

The input is exactly unary ell, unary 2^ell padding, and unary position j.
The padding is read from the input; only the smaller control-word power is
computed, with its polynomial output bound proved from that padding. All
placements print their actual finite active-position arrays.
-/
noncomputable section
namespace Paper25.OperationalModel.UniformCompilation
open LocalCompilation
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

lemma clockPosition_width_generated (classical : FLListClosure) (parsing : UnaryPrefixParsing) :
    LogspaceComputes clockPositionInput (fun p => encodeNat p.1) := by
  let recode (p : ClockPositionRequest) : ℕ × Input :=
    (p.1,encodeNat (2^p.1) ++ encodeNat p.2.val)
  have he : (fun p => unaryPrefixInput (recode p)) = clockPositionInput := by
    funext p
    simp only [recode,unaryPrefixInput,clockPositionInput,List.append_assoc]
  have h : LogspaceComputes clockPositionInput (fun p => unaryPrefixInput (recode p)) := by
    rw [he]
    exact classical.strings.identity clockPositionInput
  exact classical.strings.compose clockPositionInput unaryPrefixInput recode _ h parsing.first

lemma clockPosition_tail_generated (classical : FLListClosure) (parsing : UnaryPrefixParsing) :
    LogspaceComputes clockPositionInput (fun p => encodeNat (2^p.1) ++ encodeNat p.2.val) := by
  let recode (p : ClockPositionRequest) : ℕ × Input :=
    (p.1,encodeNat (2^p.1) ++ encodeNat p.2.val)
  have he : (fun p => unaryPrefixInput (recode p)) = clockPositionInput := by
    funext p
    simp only [recode,unaryPrefixInput,clockPositionInput,List.append_assoc]
  have h : LogspaceComputes clockPositionInput (fun p => unaryPrefixInput (recode p)) := by
    rw [he]
    exact classical.strings.identity clockPositionInput
  exact classical.strings.compose clockPositionInput unaryPrefixInput recode _ h parsing.rest

lemma clockPosition_padding_generated (classical : FLListClosure) (parsing : UnaryPrefixParsing) :
    LogspaceComputes clockPositionInput (fun p => encodeNat (2^p.1)) := by
  let recode (p : ClockPositionRequest) : ℕ × Input := (2^p.1,encodeNat p.2.val)
  exact classical.strings.compose clockPositionInput unaryPrefixInput recode _
    (clockPosition_tail_generated classical parsing) parsing.first

lemma clockPosition_index_generated (classical : FLListClosure) (parsing : UnaryPrefixParsing) :
    LogspaceComputes clockPositionInput (fun p => encodeNat p.2.val) := by
  let recode (p : ClockPositionRequest) : ℕ × Input := (2^p.1,encodeNat p.2.val)
  exact classical.strings.compose clockPositionInput unaryPrefixInput recode _
    (clockPosition_tail_generated classical parsing) parsing.rest

lemma clockPosition_low_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    (parsing : UnaryPrefixParsing) :
    LogspaceComputes clockPositionInput (fun p => encodeNat (lowWidth p.1 p.2)) := by
  have hj1 := nat_add classical arithmetic clockPositionInput _ _
    (clockPosition_index_generated classical parsing) (nat_const classical clockPositionInput 1)
  simpa only [lowWidth_eq] using nat_sub classical arithmetic clockPositionInput _ _
    (clockPosition_width_generated classical parsing) hj1

private lemma clockPosition_padding_bound (p : ClockPositionRequest) :
    2^p.1 ≤ (clockPositionInput p).length+1 := by
  simp only [clockPositionInput,encodeNat,List.length_append,List.length_replicate,List.length_singleton]
  omega

lemma clockPosition_controlStates_polynomial :
    PolynomialBoundOn clockPositionInput (fun p => 2^lowWidth p.1 p.2) := by
  refine ⟨1,1,?_⟩
  intro p
  simp only [pow_one,one_mul]
  exact (Nat.pow_le_pow_right (by decide) (by rw [lowWidth_eq]; omega)).trans
    (clockPosition_padding_bound p)

lemma clockPosition_controls_polynomial :
    PolynomialBoundOn clockPositionInput (fun p => lowWidth p.1 p.2) := by
  obtain ⟨C,d,h⟩ := clockPosition_controlStates_polynomial
  exact ⟨C,d,fun p => (Nat.le_of_lt (Nat.lt_two_pow_self (n := lowWidth p.1 p.2))).trans (h p)⟩

lemma clockPosition_suffixWidth_polynomial :
    PolynomialBoundOn clockPositionInput (fun p => lowWidth p.1 p.2+1) := by
  refine ⟨1,1,?_⟩
  intro p
  have hj := p.2.isLt
  have hlow := lowWidth_eq p.1 p.2
  have hle : lowWidth p.1 p.2+1 ≤ p.1 := by omega
  have hpow : p.1 ≤ 2^p.1 := Nat.le_of_lt (Nat.lt_two_pow_self (n := p.1))
  simpa only [pow_one,one_mul] using hle.trans (hpow.trans (clockPosition_padding_bound p))

lemma clock_controls_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    (parsing : UnaryPrefixParsing) :
    LogspaceComputes clockPositionInput (fun p =>
      controlPrefix (lowWidth p.1 p.2) (ClockCompilation.ones (lowWidth p.1 p.2))) := by
  have hlow := clockPosition_low_generated classical arithmetic parsing
  have hstates := nat_two_pow arithmetic clockPositionInput _ hlow clockPosition_controlStates_polynomial
  have hbits := arithmetic.bitArray clockPositionInput (fun p => lowWidth p.1 p.2)
    (fun _ _ => (1 : Bit)) hlow clockPosition_controls_polynomial
    (classical.strings.constant (indexedInput clockPositionInput (fun p => lowWidth p.1 p.2)) [1])
  exact classical.strings.concat clockPositionInput _ _
    (classical.strings.concat clockPositionInput _ _ hlow hstates) hbits

private lemma clock_query_pullback (classical : FLListClosure) (count : ClockPositionRequest → ℕ)
    (f : ClockPositionRequest → Input) (hf : LogspaceComputes clockPositionInput f) :
    LogspaceComputes (indexedInput clockPositionInput count) (fun p => f p.1) :=
  classical.strings.compose (indexedInput clockPositionInput count) clockPositionInput Sigma.fst _
    (indexed_input_generated classical clockPositionInput count) hf

lemma clock_carryWires_value (ell : ℕ) (i : Fin (ell+1)) :
    (ClockCompilation.carryWires ell i).val = if i.val=ell then 0 else i.val+1 := by
  change (finRotate (ell+1) i).val = _
  rw [ClockCompilation.rotate_val (by omega)]
  simp only [Nat.add_sub_cancel]

lemma clock_carryWires_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    (parsing : UnaryPrefixParsing) :
    LogspaceComputes clockPositionInput (fun p =>
      (placementOfEmbedding (ClockCompilation.carryWires (lowWidth p.1 p.2))).encode) := by
  let count (p : ClockPositionRequest) := lowWidth p.1 p.2+1
  have hlow := clockPosition_low_generated classical arithmetic parsing
  have hcount := nat_add classical arithmetic clockPositionInput _ _ hlow
    (nat_const classical clockPositionInput 1)
  apply placement_generated classical arithmetic clockPositionInput _ hcount hcount
    clockPosition_suffixWidth_polynomial
  let ctx := indexedInput clockPositionInput count
  have hlo := clock_query_pullback classical count _ hlow
  have hi := indexed_counter_generated classical clockPositionInput count
  have heq := nat_eq classical arithmetic ctx _ _ hi hlo
  have hisucc := nat_add classical arithmetic ctx _ _ hi (nat_const classical ctx 1)
  have hif := nat_if classical ctx (fun p => decide (p.2.val=lowWidth p.1.1 p.1.2))
    (fun _ => 0) (fun p => p.2.val+1) heq (nat_const classical ctx 0) hisucc
  simpa only [active_placementOfEmbedding_eq,clock_carryWires_value,decide_eq_true_eq] using hif

lemma clock_suffixWires_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    (parsing : UnaryPrefixParsing) :
    LogspaceComputes clockPositionInput (fun p => (placementOfEmbedding (suffixWires p.1 p.2)).encode) := by
  let count (p : ClockPositionRequest) := lowWidth p.1 p.2+1
  have hlow := clockPosition_low_generated classical arithmetic parsing
  have hcount := nat_add classical arithmetic clockPositionInput _ _ hlow
    (nat_const classical clockPositionInput 1)
  apply placement_generated classical arithmetic clockPositionInput _
    (clockPosition_width_generated classical parsing) hcount clockPosition_suffixWidth_polynomial
  have hj := clock_query_pullback classical count _ (clockPosition_index_generated classical parsing)
  have hi := indexed_counter_generated classical clockPositionInput count
  simpa only [active_placementOfEmbedding_eq,suffixWires] using
    nat_add classical arithmetic (indexedInput clockPositionInput count) _ _ hj hi

/-- The clock-specific description record is a proved consequence of only
fixed generic string parsing and natural arithmetic programs. -/
def clockIndex_of_arithmetic (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    (parsing : UnaryPrefixParsing) : ClockIndexDescription where
  controls := clock_controls_generated classical arithmetic parsing
  carryWires := clock_carryWires_generated classical arithmetic parsing
  suffixWires := clock_suffixWires_generated classical arithmetic parsing

end Paper25.OperationalModel.UniformCompilation

import Paper25.PreparationRowExpansion
import Paper25.ClassicalCounterCompilation

/-!
# Description generation of the actual native preparation list

The Bell rows, clock rows, and fixed X/Z/X sign operation use only the already
constructed constant elementary implementations. Every variable placement byte
is derived from unary arithmetic and indexed input projections. The row loops
are the exact chronological lists proved in `PreparationRowExpansion`.
-/
noncomputable section
namespace Paper25.OperationalModel.UniformCompilation
open LocalCompilation
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000
variable {G : EffectiveGateSet}

private lemma preparation_poly_constant {α : Type} (encode : α → Input) (k : ℕ) :
    PolynomialBoundOn encode (fun _ => k) := ⟨k,0,by simp⟩

private lemma preparation_poly_succ {α : Type} (encode : α → Input) (f : α → ℕ)
    (hf : PolynomialBoundOn encode f) : PolynomialBoundOn encode (fun a => f a+1) := by
  obtain ⟨C,d,h⟩ := hf
  refine ⟨C+1,d,?_⟩
  intro a
  have hp : 0 < ((encode a).length+1)^d := by positivity
  have ha := h a
  nlinarith

private lemma preparation_pullback (classical : FLListClosure) {α : Type}
    (encode : α → Input) (count : α → ℕ) (f : α → Input)
    (hf : LogspaceComputes encode f) :
    LogspaceComputes (indexedInput encode count) (fun p => f p.1) :=
  classical.strings.compose (indexedInput encode count) encode Sigma.fst f
    (indexed_input_generated classical encode count) hf

/-- All placement bytes of a contiguous fixed-width row come from offset+i. -/
lemma intervalPlacement_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    {α : Type} (encode : α → Input) (q offset : α → ℕ) (k : ℕ)
    (h : ∀ a, offset a+k≤q a)
    (hq : LogspaceComputes encode (fun a => encodeNat (q a)))
    (ho : LogspaceComputes encode (fun a => encodeNat (offset a))) :
    LogspaceComputes encode (fun a =>
      (placementOfEmbedding (intervalWires (q a) k (offset a) (h a))).encode) := by
  apply placement_generated classical arithmetic encode _ hq (nat_const classical encode k)
    (preparation_poly_constant encode k)
  have hoff := preparation_pullback classical encode (fun _ => k) _ ho
  have hi := indexed_counter_generated classical encode (fun _ => k)
  simpa only [active_placementOfEmbedding_eq, intervalWires] using
    nat_add classical arithmetic (indexedInput encode (fun _ => k)) _ _ hoff hi

lemma bellSize_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    {α : Type} (encode : α → Input) (s : α → ℕ)
    (hs : LogspaceComputes encode (fun a => encodeNat (s a))) :
    LogspaceComputes encode (fun a => encodeNat (StatePreparationLocal.bellSize (s a))) := by
  simpa only [StatePreparationLocal.bellSize_eq] using
    nat_mul classical arithmetic encode (fun _ => 2) s (nat_const classical encode 2) hs

lemma bellRow_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    (arithmetic : NatArithmeticDescription) (conv : GateConvention G)
    {α : Type} (encode : α → Input) (s : α → ℕ)
    (hs : LogspaceComputes encode (fun a => encodeNat (s a))) :
    GeneratedCircuit (indexedInput encode s) (fun p => bellRow conv (s p.1) p.2) := by
  let ctx := indexedInput encode s
  have hsctx := preparation_pullback classical encode s _ hs
  have hq := bellSize_generated classical arithmetic ctx (fun p => s p.1) hsctx
  have hj := indexed_counter_generated classical encode s
  have ho := nat_mul classical arithmetic ctx (fun _ => 2) (fun p => p.2.val)
    (nat_const classical ctx 2) hj
  exact embedCircuit_generated classical grammar ctx _ _
    (intervalPlacement_generated classical arithmetic ctx _ _ 2 _ hq ho)
    (constant_generated classical ctx (compileElementary conv StatePreparationLocal.bellLocalPair))

lemma bell_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    (arithmetic : NatArithmeticDescription) (conv : GateConvention G)
    {α : Type} (encode : α → Input) (s : α → ℕ)
    (hs : LogspaceComputes encode (fun a => encodeNat (s a)))
    (hpoly : PolynomialBoundOn encode s) :
    GeneratedCircuit encode (fun a => compileElementary conv (StatePreparationLocal.bellLocal (s a))) := by
  simpa only [bell_eq_rows] using loop_generated classical (q := fun a => StatePreparationLocal.bellSize (s a)) encode s
    (fun p => bellRow conv (s p.1) p.2) hs hpoly
    (bellRow_generated classical grammar arithmetic conv encode s hs)

private lemma encode_oneBit_bool (b : Bit) : encodeBool (decide (b=1)) = [b] := by
  fin_cases b <;> rfl

lemma preparationClockRow_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    (arithmetic : NatArithmeticDescription) (conv : GateConvention G)
    {α : Type} (encode : α → Input) (ell : α → ℕ) (t : ∀ a, StatePreparation.Bits (ell a))
    (hell : LogspaceComputes encode (fun a => encodeNat (ell a)))
    (ht : LogspaceComputes encode (fun a => List.ofFn (t a))) :
    GeneratedCircuit (indexedInput encode ell) (fun p => preparationClockRow conv (ell p.1) (t p.1) p.2) := by
  let ctx := indexedInput encode ell
  have hellctx := preparation_pullback classical encode ell _ hell
  have htctx := preparation_pullback classical encode ell _ ht
  have hj := indexed_counter_generated classical encode ell
  have hbit := word_bit_generated classical arithmetic ctx (fun p => t p.1) (fun p => p.2)
    hellctx htctx hj
  have hbool : LogspaceComputes ctx (fun p => encodeBool (decide (t p.1 p.2=1))) := by
    simpa only [encode_oneBit_bool] using hbit
  have hq : LogspaceComputes ctx (fun p => encodeNat (StatePreparationLocal.clockSize (ell p.1))) := by
    simpa only [StatePreparationLocal.clockSize_eq] using hellctx
  let pClock (p : Σ a, Fin (ell a)) : Placement (StatePreparationLocal.clockSize (ell p.1)) 1 :=
    placementOfEmbedding (intervalWires _ 1 p.2.val
      (by have := p.2.isLt; rw [StatePreparationLocal.clockSize_eq]; omega))
  have hpClock : LogspaceComputes ctx (fun p => (pClock p).encode) :=
    intervalPlacement_generated classical arithmetic ctx _ _ 1
      (by intro p; have := p.2.isLt; rw [StatePreparationLocal.clockSize_eq]; omega) hq hj
  have hX : GeneratedCircuit ctx (fun p => embedCircuit (pClock p)
      (compileElementary conv StatePreparationLocal.xCircuit)) :=
    embedCircuit_generated classical grammar ctx pClock _ hpClock
      (constant_generated classical ctx (compileElementary conv StatePreparationLocal.xCircuit))
  have h := conditional_generated classical ctx (fun p => decide (t p.1 p.2=1)) _ _ hbool hX
    (nil_generated classical ctx (fun p => StatePreparationLocal.clockSize (ell p.1)))
  have heq : (fun p : Σ a, Fin (ell a) => preparationClockRow conv (ell p.1) (t p.1) p.2) =
      (fun p : Σ a, Fin (ell a) => if decide (t p.1 p.2=1) then
        embedCircuit (pClock p) (compileElementary conv StatePreparationLocal.xCircuit) else []) := by
    funext p
    unfold preparationClockRow pClock
    rcases SourceTermCompilation.bit_cases (t p.1 p.2) with hb | hb <;> simp [hb]
  rw [heq]
  exact h

lemma clock_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    (arithmetic : NatArithmeticDescription) (conv : GateConvention G)
    {α : Type} (encode : α → Input) (ell : α → ℕ) (t : ∀ a, StatePreparation.Bits (ell a))
    (hell : LogspaceComputes encode (fun a => encodeNat (ell a)))
    (ht : LogspaceComputes encode (fun a => List.ofFn (t a)))
    (hpoly : PolynomialBoundOn encode ell) :
    GeneratedCircuit encode (fun a => compileElementary conv (StatePreparationLocal.clockLocal (ell a) (t a))) := by
  simpa only [clock_eq_rows] using loop_generated classical (q := fun a => StatePreparationLocal.clockSize (ell a)) encode ell
    (fun p => preparationClockRow conv (ell p.1) (t p.1) p.2) hell hpoly
    (preparationClockRow_generated classical grammar arithmetic conv encode ell t hell ht)

lemma sign_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    (arithmetic : NatArithmeticDescription) (conv : GateConvention G)
    {α : Type} (encode : α → Input) (s : α → ℕ)
    (hs : LogspaceComputes encode (fun a => encodeNat (s a))) :
    GeneratedCircuit encode (fun a => compileElementary conv (StatePreparationLocal.signLocal (s a))) := by
  have hs1 := nat_add classical arithmetic encode s (fun _ => 1) hs (nat_const classical encode 1)
  have hq := bellSize_generated classical arithmetic encode (fun a => s a+1) hs1
  have hp : LogspaceComputes encode (fun a =>
      (placementOfEmbedding (StatePreparationLocal.firstWire (s a))).encode) := by
    apply placement_generated classical arithmetic encode _ hq (nat_const classical encode 1)
      (preparation_poly_constant encode 1)
    simpa only [active_placementOfEmbedding_eq, StatePreparationLocal.firstWire] using
      nat_const classical (indexedInput encode (fun _ => 1)) 0
  have hX := embedCircuit_generated classical grammar encode _ _ hp
    (constant_generated classical encode (elementaryImplementation conv (1 : Fin 4)))
  have hZ := embedCircuit_generated classical grammar encode _ _ hp
    (constant_generated classical encode (elementaryImplementation conv (2 : Fin 4)))
  simpa only [compileElementary,StatePreparationLocal.signLocal,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,compileElementaryGate,StatePreparationLocal.firstX,StatePreparationLocal.firstZ] using
    append_generated classical encode _ _ hX (append_generated classical encode _ _ hZ hX)

lemma signed_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    (arithmetic : NatArithmeticDescription) (conv : GateConvention G)
    {α : Type} (encode : α → Input) (s : α → ℕ)
    (hs : LogspaceComputes encode (fun a => encodeNat (s a)))
    (hpoly : PolynomialBoundOn encode s) :
    GeneratedCircuit encode (fun a => compileElementary conv (StatePreparationLocal.signedLocal (s a))) := by
  have hs1 := nat_add classical arithmetic encode s (fun _ => 1) hs (nat_const classical encode 1)
  simpa only [StatePreparationLocal.signedLocal,compileElementary,List.flatMap_append] using
    append_generated classical encode _ _
      (bell_generated classical grammar arithmetic conv encode (fun a => s a+1) hs1
        (preparation_poly_succ encode s hpoly))
      (sign_generated classical grammar arithmetic conv encode s hs)

/-- All actual preparation bytes are derived from widths, the target clock word,
and generic classical operations. No preparation compiler is an external input. -/
theorem nativeF_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    (arithmetic : NatArithmeticDescription) (conv : GateConvention G)
    {α : Type} (encode : α → Input) (ell s r : α → ℕ) (t : ∀ a, StatePreparation.Bits (ell a))
    (hell : LogspaceComputes encode (fun a => encodeNat (ell a)))
    (hs : LogspaceComputes encode (fun a => encodeNat (s a)))
    (hr : LogspaceComputes encode (fun a => encodeNat (r a)))
    (ht : LogspaceComputes encode (fun a => List.ofFn (t a)))
    (hpolyEll : PolynomialBoundOn encode ell) (hpolyS : PolynomialBoundOn encode s) :
    GeneratedCircuit encode (fun a => nativeF conv (ell a) (s a) (r a) (t a)) := by
  have hbell := signed_generated classical grammar arithmetic conv encode s hs hpolyS
  have hnil : GeneratedCircuit encode
      (fun a => compileElementary conv ([] : Circuit StatePreparationLocal.elementary (r a))) :=
    nil_generated classical encode r
  have hs1 := nat_add classical arithmetic encode s (fun _ => 1) hs (nat_const classical encode 1)
  have hbellWidth := bellSize_generated classical arithmetic encode (fun a => s a+1) hs1
  have hbellr := tensorCircuit_generated classical grammar encode _ _ hbell hnil hbellWidth hr
  have hbellrWidth := nat_add classical arithmetic encode _ _ hbellWidth hr
  have hclock := clock_generated classical grammar arithmetic conv encode ell t hell ht hpolyEll
  have hclockWidth : LogspaceComputes encode
      (fun a => encodeNat (StatePreparationLocal.clockSize (ell a))) := by
    simpa only [StatePreparationLocal.clockSize_eq] using hell
  have hmid := tensorCircuit_generated classical grammar encode _ _ hclock hbellr hclockWidth hbellrWidth
  have hmidWidth := nat_add classical arithmetic encode _ _ hclockWidth hbellrWidth
  have hX := constant_generated classical encode (compileElementary conv StatePreparationLocal.xCircuit)
  simpa only [nativeF,StatePreparationLocal.physicalF,compileElementary_tensor] using
    tensorCircuit_generated classical grammar encode _ _ hX hmid (nat_const classical encode 1) hmidWidth

end Paper25.OperationalModel.UniformCompilation

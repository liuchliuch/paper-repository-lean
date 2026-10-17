import Paper25.UniformCompilation
import Paper25.ClockCompilation
import Paper25.HistoryCompilation

/-! Description generation for the actual ripple-clock and scalar-minus lists.
The exposed external queries only print unary widths, bit words and arrays of
natural wire positions. No query accepts or returns a quantum circuit. -/
noncomputable section
namespace Paper25.OperationalModel.UniformCompilation
open LocalCompilation
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000

lemma embedCircuit_embedding_comp {G : EffectiveGateSet} {a b c : ℕ}
    (f : Fin b ↪ Fin a) (g : Fin c ↪ Fin b) (C : EffectiveCircuit G c) :
    embedCircuit (placementOfEmbedding f) (embedCircuit (placementOfEmbedding g) C) =
      embedCircuit (placementOfEmbedding (g.trans f)) C := by
  simp only [embedCircuit, List.map_map, Function.comp_def]
  congr 1

/-- Number of less significant bits, computed by the physical bit scan. -/
def lowWidth : (ell : ℕ) → Fin ell → ℕ
  | 0, j => Fin.elim0 j
  | ell+1, j => Fin.cases ell (lowWidth ell) j

lemma lowWidth_eq (ell : ℕ) (j : Fin ell) : lowWidth ell j = ell-(j.val+1) := by
  induction ell with
  | zero => exact Fin.elim0 j
  | succ ell ih =>
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [lowWidth]
    · simpa [lowWidth, Fin.val_succ, Nat.add_sub_add_right] using ih i

/-- The suffix beginning at the currently scanned physical bit. -/
def suffixWires (ell : ℕ) (j : Fin ell) : Fin (lowWidth ell j+1) ↪ Fin ell where
  toFun i := ⟨j.val+i.val, by have hj := j.isLt; have hi := i.isLt; have hl := lowWidth_eq ell j; omega⟩
  inj' := by intro i k h; apply Fin.ext; have hv := congrArg Fin.val h; dsimp at hv; omega

def clockRow {G : EffectiveGateSet} (conv : GateConvention G) (ell : ℕ) (j : Fin ell) :
    EffectiveCircuit G ell :=
  embedCircuit (placementOfEmbedding (suffixWires ell j))
    (ClockCompilation.carryCircuit conv (lowWidth ell j))

lemma clockRow_zero {G : EffectiveGateSet} (conv : GateConvention G) (ell : ℕ) :
    clockRow conv (ell+1) 0 = ClockCompilation.carryCircuit conv ell := by
  unfold clockRow
  change embedCircuit (placementOfEmbedding (suffixWires (ell+1) 0))
    (ClockCompilation.carryCircuit conv ell) = ClockCompilation.carryCircuit conv ell
  unfold ClockCompilation.carryCircuit
  rw [embedCircuit_embedding_comp]
  have he : (ClockCompilation.carryWires ell).trans (suffixWires (ell+1) 0) =
      ClockCompilation.carryWires ell := by
    ext i
    simp [suffixWires]
  rw [he]

lemma clockRow_succ {G : EffectiveGateSet} (conv : GateConvention G) (ell : ℕ) (j : Fin ell) :
    clockRow conv (ell+1) j.succ =
      embedCircuit (placementOfEmbedding (ClockCompilation.tailWires ell)) (clockRow conv ell j) := by
  unfold clockRow
  rw [embedCircuit_embedding_comp]
  have he : (suffixWires ell j).trans (ClockCompilation.tailWires ell) =
      suffixWires (ell+1) j.succ := by
    ext i
    dsimp [suffixWires, ClockCompilation.tailWires]
    omega
  change embedCircuit (placementOfEmbedding (suffixWires (ell+1) j.succ))
    (ClockCompilation.carryCircuit conv (lowWidth ell j)) = _
  rw [he]

lemma increment_eq_rows {G : EffectiveGateSet} (conv : GateConvention G) (ell : ℕ) :
    ClockCompilation.increment conv ell = (List.ofFn (clockRow conv ell)).flatten := by
  induction ell with
  | zero => simp [ClockCompilation.increment]
  | succ ell ih =>
    rw [ClockCompilation.increment, ih, List.ofFn_succ, List.flatten_cons, clockRow_zero]
    simp only [clockRow_succ, embedCircuit, List.map_ofFn, List.map_flatten, Function.comp_def]

abbrev ClockPositionRequest := Σ ell : ℕ, Fin ell

def clockPositionInput (p : ClockPositionRequest) : Input :=
  encodeNat p.1 ++ encodeNat (2^p.1) ++ encodeNat p.2.val

/-- Fixed classical counter programs. Padding is explicit and ensures the
control-word output has polynomial size. Only bitstrings/natural arrays occur. -/
structure ClockIndexDescription : Prop where
  controls : LogspaceComputes clockPositionInput (fun p =>
    controlPrefix (lowWidth p.1 p.2) (ClockCompilation.ones (lowWidth p.1 p.2)))
  carryWires : LogspaceComputes clockPositionInput (fun p =>
    (placementOfEmbedding (ClockCompilation.carryWires (lowWidth p.1 p.2))).encode)
  suffixWires : LogspaceComputes clockPositionInput (fun p =>
    (placementOfEmbedding (suffixWires p.1 p.2)).encode)

lemma increment_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv)
    (indices : ClockIndexDescription) {α : Type} (encode : α → Input) (ell : α → ℕ)
    (hell : LogspaceComputes encode (fun a => encodeNat (ell a)))
    (hstates : LogspaceComputes encode (fun a => encodeNat (2^(ell a))))
    (hpoly : PolynomialBoundOn encode ell) :
    GeneratedCircuit encode (fun a => ClockCompilation.increment conv (ell a)) := by
  let ctx := indexedInput encode ell
  let request (p : Σ a, Fin (ell a)) : ClockPositionRequest := ⟨ell p.1,p.2⟩
  have hwidth := classical.strings.compose ctx encode Sigma.fst _
    (indexed_input_generated classical encode ell) hell
  have hstates' := classical.strings.compose ctx encode Sigma.fst _
    (indexed_input_generated classical encode ell) hstates
  have hcounter := indexed_counter_generated classical encode ell
  have hrequest : LogspaceComputes ctx (fun p => clockPositionInput (request p)) :=
    classical.strings.concat ctx _ _ (classical.strings.concat ctx _ _ hwidth hstates') hcounter
  have hc := classical.strings.compose ctx clockPositionInput request _ hrequest indices.controls
  have hp := classical.strings.compose ctx clockPositionInput request _ hrequest indices.carryWires
  have hs := classical.strings.compose ctx clockPositionInput request _ hrequest indices.suffixWires
  have hx := constant_generated classical (G := G) ctx conv.X
  have hpattern := patternCircuit_generated classical primitive ctx
    (fun p => ClockCompilation.ones (lowWidth (ell p.1) p.2)) (fun _ => conv.X) hc hx
  have hcarry := embedCircuit_generated classical grammar ctx
    (fun p => placementOfEmbedding (ClockCompilation.carryWires (lowWidth (ell p.1) p.2))) _ hp hpattern
  have hrow := embedCircuit_generated classical grammar ctx
    (fun p => placementOfEmbedding (suffixWires (ell p.1) p.2)) _ hs hcarry
  have h := loop_generated classical encode ell
    (fun p => clockRow conv (ell p.1) p.2) hell hpoly hrow
  simpa only [increment_eq_rows] using h

abbrev PositiveWidth := {q : ℕ // 0<q}

def positiveWidthInput (p : PositiveWidth) : Input := encodeNat p.1

/-- Again these are only fixed natural-number/position printers. -/
structure NegativeIndexDescription : Prop where
  firstWire : LogspaceComputes encodeNat (fun q =>
    (placementOfEmbedding (LocalCompilation.firstWire q)).encode)
  predecessor : LogspaceComputes positiveWidthInput (fun q => encodeNat (q.1-1))
  castWires : LogspaceComputes positiveWidthInput (fun q =>
    (placementOfEmbedding (finCongr (show q.1-1+1=q.1 by have := q.2; omega)).toEmbedding).encode)

lemma flipCircuit_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    {G : EffectiveGateSet} {conv : GateConvention G} (indices : NegativeIndexDescription)
    {α : Type} (encode : α → Input) (q : α → ℕ)
    (hq : LogspaceComputes encode (fun a => encodeNat (q a))) :
    GeneratedCircuit encode (fun a => flipCircuit conv (q a)) := by
  have hp := classical.strings.compose encode encodeNat q _ hq indices.firstWire
  exact embedCircuit_generated classical grammar encode _ _ hp (constant_generated classical encode conv.X)

lemma negativeCircuit_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv)
    (indices : NegativeIndexDescription) {α : Type} (encode : α → Input) (q : α → ℕ)
    (hq : LogspaceComputes encode (fun a => encodeNat (q a))) :
    GeneratedCircuit encode (fun a => negativeCircuit conv (q a)) := by
  have hx := flipCircuit_generated classical grammar (conv := conv) indices encode q hq
  have hh := hadamard_generated classical primitive encode q hq
  have hxH := append_generated classical encode _ _ hx hh
  have htwo := append_generated classical encode _ _ hxH hxH
  have hfour := append_generated classical encode _ _ htwo htwo
  simpa only [negativeCircuit, List.append_assoc] using hfour

lemma negativeOn_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv)
    (indices : NegativeIndexDescription) {α : Type} (encode : α → Input) (q : α → ℕ)
    (hpositive : ∀ a, 0<q a)
    (hq : LogspaceComputes encode (fun a => encodeNat (q a))) :
    GeneratedCircuit encode (fun a => negativeOn conv (q a) (hpositive a)) := by
  let width (a : α) : PositiveWidth := ⟨q a,hpositive a⟩
  have hp := classical.strings.compose encode positiveWidthInput width _ hq indices.predecessor
  have hc := classical.strings.compose encode positiveWidthInput width _ hq indices.castWires
  have hn := negativeCircuit_generated classical grammar primitive indices encode (fun a => q a-1) hp
  exact rewire_generated classical grammar encode
    (fun a => finCongr (show q a-1+1=q a by have := hpositive a; omega)) _ hc hn

end Paper25.OperationalModel.UniformCompilation

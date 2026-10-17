import Paper25.SourceUniformCompilation
import Paper25.ClassicalCounterCompilation
import Paper25.NatVectorParsing

/-! Generated descriptions of the actual seven source-view term templates.
Only fixed classical unary-vector parsing is added as external data machinery;
all doubled placements and all gate-list combinations are constructed here. -/
noncomputable section
namespace Paper25.OperationalModel.UniformCompilation
open LocalCompilation SourceTermCompilation
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 512

lemma placement_natVector {q k : ℕ} (p : Placement q k) :
    p.encode = natVectorInput (q,List.ofFn (fun i => (active p i).val)) := by
  simp [Placement.encode, natVectorInput, active, List.map_ofFn, Function.comp_def]

lemma double_active_value {q k : ℕ} (hk : 0 < k) (p : Placement q k) (i : Fin (k+k)) :
    (active (doublePlacement p) i).val =
      if i.val < k then ((List.ofFn (fun j => (active p j).val))[i.val%k]?).getD 0
      else q + ((List.ofFn (fun j => (active p j).val))[i.val%k]?).getD 0 := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [doublePlacement, active_placementOfEmbedding_eq, doubleEmbedding_left,
      Nat.mod_eq_of_lt j.isLt, j.isLt]
  · change ((doubleEmbedding p) (Fin.natAdd k j)).val = _
    rw [doubleEmbedding_right]
    have hn : ¬ k+j.val < k := by omega
    simp [Fin.natAdd, Nat.add_mod, Nat.mod_eq_of_lt j.isLt, hn, j.isLt]

lemma doublePlacement_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    (vectors : NatVectorParsing) {α : Type} {q : α → ℕ} (encode : α → Input)
    (k : ℕ) (hk : 0 < k) (p : ∀ a, Placement (q a) k)
    (hq : LogspaceComputes encode (fun a => encodeNat (q a)))
    (hp : LogspaceComputes encode (fun a => (p a).encode)) :
    LogspaceComputes encode (fun a => (doublePlacement (p a)).encode) := by
  apply placement_generated classical arithmetic encode (fun a => doublePlacement (p a))
  · exact nat_add classical arithmetic encode q q hq hq
  · exact nat_const classical encode (k+k)
  · exact ⟨k+k,0,by intro a; simp⟩
  · let ctx := indexedInput encode (fun _ => k+k)
    have hi := indexed_counter_generated classical encode (fun _ => k+k)
    have hiMod := nat_mod classical arithmetic ctx (fun r => r.2.val) (fun _ => k) hi (nat_const classical ctx k)
    have hpCtx := classical.strings.compose ctx encode Sigma.fst _
      (indexed_input_generated classical encode (fun _ => k+k)) hp
    have hqCtx := classical.strings.compose ctx encode Sigma.fst _
      (indexed_input_generated classical encode (fun _ => k+k)) hq
    let req (r : Σ a, Fin (k+k)) : ℕ × (ℕ × List ℕ) :=
      (r.2.val%k,(q r.1,List.ofFn (fun j => (active (p r.1) j).val)))
    have hr : LogspaceComputes ctx (fun r => natVectorEntryInput (req r)) := by
      simpa only [req,natVectorEntryInput,←placement_natVector] using
        classical.strings.concat ctx _ _ hiMod hpCtx
    have he := classical.strings.compose ctx natVectorEntryInput req _ hr vectors.entry
    have ho := nat_add classical arithmetic ctx (fun r => q r.1)
      (fun r => ((List.ofFn (fun j => (active (p r.1) j).val))[r.2.val%k]?).getD 0) hqCtx he
    have hc := nat_lt classical arithmetic ctx (fun r => r.2.val) (fun _ => k) hi (nat_const classical ctx k)
    have h := classical.strings.conditional ctx (fun r => decide (r.2.val < k))
      (fun r => encodeNat (((List.ofFn (fun j => (active (p r.1) j).val))[r.2.val%k]?).getD 0))
      (fun r => encodeNat (q r.1 + ((List.ofFn (fun j => (active (p r.1) j).val))[r.2.val%k]?).getD 0)) hc he ho
    simpa only [ctx, double_active_value hk, decide_eq_true_eq, apply_ite] using h

lemma source_unitaryTerm_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    (arithmetic : NatArithmeticDescription) {G : EffectiveGateSet} {conv : GateConvention G}
    (primitive : PrimitiveDescriptionConvention conv) {α : Type} {q : α → ℕ}
    (encode : α → Input) (hqPos : ∀ a, 0 < q a) (C : ∀ a, EffectiveCircuit G (q a))
    (j : α → Fin 8) (hC : GeneratedCircuit encode C)
    (hq : LogspaceComputes encode (fun a => encodeNat (q a)))
    (hj : LogspaceComputes encode (fun a => encodeNat (j a).val)) :
    GeneratedCircuit encode (fun a => unitaryTermCircuit conv (hqPos a) (C a) (j a)) := by
  have hL := tensorCircuit_generated classical grammar encode C (fun a => conjugateCircuit conv (C a))
    hC (conjugateCircuit_generated classical primitive encode C hC) hq hq
  let negP (a : α) : Placement (q a+q a) 1 := placementOfEmbedding {
    toFun := fun _ => ⟨0,by have h := hqPos a; omega⟩
    inj' := fun _ _ _ => Subsingleton.elim _ _ }
  have hp : LogspaceComputes encode (fun a => (negP a).encode) := by
    apply placement_generated classical arithmetic encode negP
    · exact nat_add classical arithmetic encode q q hq hq
    · exact nat_const classical encode 1
    · exact ⟨1,0,by intro a; simp⟩
    · simpa only [negP,active_placementOfEmbedding_eq] using
        nat_const classical (indexedInput encode (fun _ => 1)) 0
  have hN := embedCircuit_generated classical grammar encode negP
    (fun _ => negativeCircuit conv 0) hp (constant_generated classical encode (negativeCircuit conv 0))
  have hmod := nat_mod classical arithmetic encode (fun a => (j a).val) (fun _ => 2) hj (nat_const classical encode 2)
  have heven := nat_eq classical arithmetic encode (fun a => (j a).val%2) (fun _ => 0) hmod (nat_const classical encode 0)
  have hrest := conditional_generated classical encode (fun a => decide ((j a).val%2=0))
    (fun a => ([] : EffectiveCircuit G (q a+q a))) _ heven (nil_generated classical encode _) hN
  have hlt := nat_lt classical arithmetic encode (fun a => (j a).val) (fun _ => 4) hj (nat_const classical encode 4)
  have h := conditional_generated classical encode (fun a => decide ((j a).val<4)) _ _ hlt hL hrest
  simpa only [unitaryTermCircuit,unitaryLiouvilleCircuit,decide_eq_true_eq,negP] using h

lemma source_placedTerm_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    (arithmetic : NatArithmeticDescription) (vectors : NatVectorParsing)
    (queries : FLDataQueryDescription) {G : EffectiveGateSet} {α : Type} {q : α → ℕ}
    (encode : α → Input) (k : ℕ) (hk : 0 < k) (p : ∀ a, Placement (q a) k)
    (j : α → Fin 8) (K : Fin 8 → EffectiveCircuit G (k+k))
    (hq : LogspaceComputes encode (fun a => encodeNat (q a)))
    (hp : LogspaceComputes encode (fun a => (p a).encode))
    (hj : LogspaceComputes encode (fun a => encodeNat (j a).val)) :
    GeneratedCircuit encode (fun a => embedCircuit (doublePlacement (p a)) (K (j a))) :=
  embedCircuit_generated classical grammar encode _ _
    (doublePlacement_generated classical arithmetic vectors encode k hk p hq hp)
    (finiteFamily_generated classical queries encode j K hj)


structure ViewInputQueries (G : EffectiveGateSet) : Prop where
  width : LogspaceComputes (viewTermInput (G := G)) (fun r => encodeNat r.1.val)
  term : LogspaceComputes (viewTermInput (G := G)) (fun r => encodeNat r.2.2.val)
  tag : LogspaceComputes (viewTermInput (G := G)) (fun r => encodeNat r.2.1.tag.val)
  payload : LogspaceComputes (viewTermInput (G := G)) (fun r => r.2.1.payload)

lemma viewInputQueries (classical : FLListClosure) (prefixParsing : UnaryPrefixParsing)
    (G : EffectiveGateSet) : ViewInputQueries G := by
  let enc := viewTermInput (G := G)
  let a (r : ViewTermRequest G) : ℕ × Input := (r.1.val, encodeNat r.2.2.val ++ r.2.1.encode)
  have ha : LogspaceComputes enc (fun r => unaryPrefixInput (a r)) := by
    have he : (fun r => unaryPrefixInput (a r)) = enc := by
      funext r
      simp only [enc,a,unaryPrefixInput,viewTermInput,List.append_assoc]
    rw [he]
    exact classical.strings.identity enc
  have hq := classical.strings.compose enc unaryPrefixInput a _ ha prefixParsing.first
  have hrest := classical.strings.compose enc unaryPrefixInput a _ ha prefixParsing.rest
  let b (r : ViewTermRequest G) : ℕ × Input := (r.2.2.val,r.2.1.encode)
  have hb : LogspaceComputes enc (fun r => unaryPrefixInput (b r)) := hrest
  have hj := classical.strings.compose enc unaryPrefixInput b _ hb prefixParsing.first
  have hv := classical.strings.compose enc unaryPrefixInput b _ hb prefixParsing.rest
  let c (r : ViewTermRequest G) : ℕ × Input := (r.2.1.tag.val,r.2.1.payload)
  have hc : LogspaceComputes enc (fun r => unaryPrefixInput (c r)) := by
    simpa only [c,b,unaryPrefixInput,SourceView.encode_eq] using hv
  exact ⟨hq,hj,classical.strings.compose enc unaryPrefixInput c _ hc prefixParsing.first,
    classical.strings.compose enc unaryPrefixInput c _ hc prefixParsing.rest⟩

lemma restrict_query (classical : FLListClosure) {α : Type} (encode : α → Input)
    (p : α → Prop) (out : α → Input) (h : LogspaceComputes encode out) :
    LogspaceComputes (fun a : {a // p a} => encode a.val) (fun a => out a.val) :=
  classical.strings.compose _ encode Subtype.val out (classical.strings.identity _) h

def viewGateData {G : EffectiveGateSet}
    (r : {r : ViewTermRequest G // r.2.1.tag = 0}) : EffectiveLocalGate G r.val.1.val := by
  rcases r with ⟨⟨q,v,j⟩,h⟩
  cases v <;> simp [SourceView.tag] at h
  assumption

lemma viewGateData_payload {G : EffectiveGateSet}
    (r : {r : ViewTermRequest G // r.2.1.tag = 0}) :
    r.val.2.1.payload = (viewGateData r).encode := by
  rcases r with ⟨⟨q,v,j⟩,h⟩
  cases v <;> simp [SourceView.tag] at h
  rfl

def viewDephaseData {G : EffectiveGateSet}
    (r : {r : ViewTermRequest G // r.2.1.tag = 1}) : Placement r.val.1.val 1 := by
  rcases r with ⟨⟨q,v,j⟩,h⟩
  cases v <;> simp [SourceView.tag] at h
  assumption

lemma viewDephaseData_payload {G : EffectiveGateSet}
    (r : {r : ViewTermRequest G // r.2.1.tag = 1}) :
    r.val.2.1.payload = (viewDephaseData r).encode := by
  rcases r with ⟨⟨q,v,j⟩,h⟩
  cases v <;> simp [SourceView.tag] at h
  rfl

def viewResetData {G : EffectiveGateSet}
    (r : {r : ViewTermRequest G // r.2.1.tag = 2}) : Placement r.val.1.val 1 := by
  rcases r with ⟨⟨q,v,j⟩,h⟩
  cases v <;> simp [SourceView.tag] at h
  assumption

lemma viewResetData_payload {G : EffectiveGateSet}
    (r : {r : ViewTermRequest G // r.2.1.tag = 2}) :
    r.val.2.1.payload = (viewResetData r).encode := by
  rcases r with ⟨⟨q,v,j⟩,h⟩
  cases v <;> simp [SourceView.tag] at h
  rfl

def viewOutcomeResetData {G : EffectiveGateSet}
    (r : {r : ViewTermRequest G // r.2.1.tag = 3}) : Placement r.val.1.val 2 := by
  rcases r with ⟨⟨q,v,j⟩,h⟩
  cases v <;> simp [SourceView.tag] at h
  assumption

lemma viewOutcomeResetData_payload {G : EffectiveGateSet}
    (r : {r : ViewTermRequest G // r.2.1.tag = 3}) :
    r.val.2.1.payload = (viewOutcomeResetData r).encode := by
  rcases r with ⟨⟨q,v,j⟩,h⟩
  cases v <;> simp [SourceView.tag] at h
  rfl

def viewCopyData {G : EffectiveGateSet}
    (r : {r : ViewTermRequest G // r.2.1.tag = 4}) : Placement r.val.1.val 2 := by
  rcases r with ⟨⟨q,v,j⟩,h⟩
  cases v <;> simp [SourceView.tag] at h
  assumption

lemma viewCopyData_payload {G : EffectiveGateSet}
    (r : {r : ViewTermRequest G // r.2.1.tag = 4}) :
    r.val.2.1.payload = (viewCopyData r).encode := by
  rcases r with ⟨⟨q,v,j⟩,h⟩
  cases v <;> simp [SourceView.tag] at h
  rfl

def viewOutcomeDephaseData {G : EffectiveGateSet}
    (r : {r : ViewTermRequest G // r.2.1.tag = 5}) : Placement r.val.1.val 2 := by
  rcases r with ⟨⟨q,v,j⟩,h⟩
  cases v <;> simp [SourceView.tag] at h
  assumption

lemma viewOutcomeDephaseData_payload {G : EffectiveGateSet}
    (r : {r : ViewTermRequest G // r.2.1.tag = 5}) :
    r.val.2.1.payload = (viewOutcomeDephaseData r).encode := by
  rcases r with ⟨⟨q,v,j⟩,h⟩
  cases v <;> simp [SourceView.tag] at h
  rfl

lemma viewGateData_term {G : EffectiveGateSet} (conv : GateConvention G)
    (r : {r : ViewTermRequest G // r.2.1.tag = 0}) :
    viewTerm conv r.val.1.property r.val.2.1 r.val.2.2 = unitaryTermCircuit conv r.val.1.property [viewGateData r] r.val.2.2 := by
  rcases r with ⟨⟨q,v,j⟩,h⟩
  cases v <;> simp [SourceView.tag] at h
  rfl

lemma viewDephaseData_term {G : EffectiveGateSet} (conv : GateConvention G)
    (r : {r : ViewTermRequest G // r.2.1.tag = 1}) :
    viewTerm conv r.val.1.property r.val.2.1 r.val.2.2 = dephasePlacedCircuit conv (viewDephaseData r) r.val.2.2 := by
  rcases r with ⟨⟨q,v,j⟩,h⟩
  cases v <;> simp [SourceView.tag] at h
  rfl

lemma viewResetData_term {G : EffectiveGateSet} (conv : GateConvention G)
    (r : {r : ViewTermRequest G // r.2.1.tag = 2}) :
    viewTerm conv r.val.1.property r.val.2.1 r.val.2.2 = resetPlacedCircuit conv (viewResetData r) r.val.2.2 := by
  rcases r with ⟨⟨q,v,j⟩,h⟩
  cases v <;> simp [SourceView.tag] at h
  rfl

lemma viewOutcomeResetData_term {G : EffectiveGateSet} (conv : GateConvention G)
    (r : {r : ViewTermRequest G // r.2.1.tag = 3}) :
    viewTerm conv r.val.1.property r.val.2.1 r.val.2.2 = outcomeResetCircuit conv (viewOutcomeResetData r) r.val.2.2 := by
  rcases r with ⟨⟨q,v,j⟩,h⟩
  cases v <;> simp [SourceView.tag] at h
  rfl

lemma viewCopyData_term {G : EffectiveGateSet} (conv : GateConvention G)
    (r : {r : ViewTermRequest G // r.2.1.tag = 4}) :
    viewTerm conv r.val.1.property r.val.2.1 r.val.2.2 = copyPlacedCircuit conv (viewCopyData r) r.val.2.2 := by
  rcases r with ⟨⟨q,v,j⟩,h⟩
  cases v <;> simp [SourceView.tag] at h
  rfl

lemma viewOutcomeDephaseData_term {G : EffectiveGateSet} (conv : GateConvention G)
    (r : {r : ViewTermRequest G // r.2.1.tag = 5}) :
    viewTerm conv r.val.1.property r.val.2.1 r.val.2.2 = outcomeDephaseCircuit conv (viewOutcomeDephaseData r) r.val.2.2 := by
  rcases r with ⟨⟨q,v,j⟩,h⟩
  cases v <;> simp [SourceView.tag] at h
  rfl

lemma viewPadding_term {G : EffectiveGateSet} (conv : GateConvention G)
    (r : {r : ViewTermRequest G // r.2.1.tag = 6}) :
    viewTerm conv r.val.1.property r.val.2.1 r.val.2.2 =
      unitaryTermCircuit conv r.val.1.property [] r.val.2.2 := by
  rcases r with ⟨⟨q,v,j⟩,h⟩
  cases v <;> simp [SourceView.tag] at h
  rfl

/-- Actual native terms for every source-view branch, generated from literal
source bytes and fixed primitive programs. No native-term compiler is assumed. -/
theorem viewTerm_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    (arithmetic : NatArithmeticDescription) (queries : FLDataQueryDescription)
    (prefixParsing : UnaryPrefixParsing) (vectors : NatVectorParsing)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv) :
    GeneratedCircuit (viewTermInput (G := G))
      (fun r => viewTerm conv r.1.property r.2.1 r.2.2) := by
  have Q := viewInputQueries classical prefixParsing G
  apply queries.finiteCases viewTermInput (fun r => r.2.1.tag) _ Q.tag
  intro i
  fin_cases i
  · let enc := fun r : {r : ViewTermRequest G // r.2.1.tag = 0} => viewTermInput r.val
    have hq := restrict_query classical viewTermInput (fun r : ViewTermRequest G => r.2.1.tag = 0) _ Q.width
    have hj := restrict_query classical viewTermInput (fun r : ViewTermRequest G => r.2.1.tag = 0) _ Q.term
    have hp : LogspaceComputes enc (fun r => (viewGateData r).encode) := by
      simpa only [viewGateData_payload] using
        restrict_query classical viewTermInput (fun r : ViewTermRequest G => r.2.1.tag = 0) _ Q.payload
    have hg := classical.singleton enc (fun r => @EffectiveLocalGate.encode G r.val.1.val) viewGateData hp
    have h := source_unitaryTerm_generated classical grammar arithmetic primitive enc
      (fun r => r.val.1.property) (fun r => [viewGateData r]) (fun r => r.val.2.2) hg hq hj
    simpa only [viewGateData_term] using h
  · let enc := fun r : {r : ViewTermRequest G // r.2.1.tag = 1} => viewTermInput r.val
    have hq := restrict_query classical viewTermInput (fun r : ViewTermRequest G => r.2.1.tag = 1) _ Q.width
    have hj := restrict_query classical viewTermInput (fun r : ViewTermRequest G => r.2.1.tag = 1) _ Q.term
    have hp : LogspaceComputes enc (fun r => (viewDephaseData r).encode) := by
      simpa only [viewDephaseData_payload] using
        restrict_query classical viewTermInput (fun r : ViewTermRequest G => r.2.1.tag = 1) _ Q.payload
    have h := source_placedTerm_generated classical grammar arithmetic vectors queries enc 1 (by decide)
      viewDephaseData (fun r => r.val.2.2) (dephaseLocalCircuit conv) hq hp hj
    simpa only [viewDephaseData_term,dephasePlacedCircuit] using h
  · let enc := fun r : {r : ViewTermRequest G // r.2.1.tag = 2} => viewTermInput r.val
    have hq := restrict_query classical viewTermInput (fun r : ViewTermRequest G => r.2.1.tag = 2) _ Q.width
    have hj := restrict_query classical viewTermInput (fun r : ViewTermRequest G => r.2.1.tag = 2) _ Q.term
    have hp : LogspaceComputes enc (fun r => (viewResetData r).encode) := by
      simpa only [viewResetData_payload] using
        restrict_query classical viewTermInput (fun r : ViewTermRequest G => r.2.1.tag = 2) _ Q.payload
    have h := source_placedTerm_generated classical grammar arithmetic vectors queries enc 1 (by decide)
      viewResetData (fun r => r.val.2.2) (resetLocalCircuit conv) hq hp hj
    simpa only [viewResetData_term,resetPlacedCircuit] using h
  · let enc := fun r : {r : ViewTermRequest G // r.2.1.tag = 3} => viewTermInput r.val
    have hq := restrict_query classical viewTermInput (fun r : ViewTermRequest G => r.2.1.tag = 3) _ Q.width
    have hj := restrict_query classical viewTermInput (fun r : ViewTermRequest G => r.2.1.tag = 3) _ Q.term
    have hp : LogspaceComputes enc (fun r => (viewOutcomeResetData r).encode) := by
      simpa only [viewOutcomeResetData_payload] using
        restrict_query classical viewTermInput (fun r : ViewTermRequest G => r.2.1.tag = 3) _ Q.payload
    have h := source_placedTerm_generated classical grammar arithmetic vectors queries enc 2 (by decide)
      viewOutcomeResetData (fun r => r.val.2.2) (resetPlacedCircuit conv secondPlacement) hq hp hj
    simpa only [viewOutcomeResetData_term,outcomeResetCircuit] using h
  · let enc := fun r : {r : ViewTermRequest G // r.2.1.tag = 4} => viewTermInput r.val
    have hq := restrict_query classical viewTermInput (fun r : ViewTermRequest G => r.2.1.tag = 4) _ Q.width
    have hj := restrict_query classical viewTermInput (fun r : ViewTermRequest G => r.2.1.tag = 4) _ Q.term
    have hp : LogspaceComputes enc (fun r => (viewCopyData r).encode) := by
      simpa only [viewCopyData_payload] using
        restrict_query classical viewTermInput (fun r : ViewTermRequest G => r.2.1.tag = 4) _ Q.payload
    have h := source_placedTerm_generated classical grammar arithmetic vectors queries enc 2 (by decide)
      viewCopyData (fun r => r.val.2.2) (unitaryTermCircuit conv (by decide : 0 < 2) conv.CNOT) hq hp hj
    simpa only [viewCopyData_term,copyPlacedCircuit] using h
  · let enc := fun r : {r : ViewTermRequest G // r.2.1.tag = 5} => viewTermInput r.val
    have hq := restrict_query classical viewTermInput (fun r : ViewTermRequest G => r.2.1.tag = 5) _ Q.width
    have hj := restrict_query classical viewTermInput (fun r : ViewTermRequest G => r.2.1.tag = 5) _ Q.term
    have hp : LogspaceComputes enc (fun r => (viewOutcomeDephaseData r).encode) := by
      simpa only [viewOutcomeDephaseData_payload] using
        restrict_query classical viewTermInput (fun r : ViewTermRequest G => r.2.1.tag = 5) _ Q.payload
    have h := source_placedTerm_generated classical grammar arithmetic vectors queries enc 2 (by decide)
      viewOutcomeDephaseData (fun r => r.val.2.2) (dephasePlacedCircuit conv secondPlacement) hq hp hj
    simpa only [viewOutcomeDephaseData_term,outcomeDephaseCircuit] using h
  · let enc := fun r : {r : ViewTermRequest G // r.2.1.tag = 6} => viewTermInput r.val
    have hq := restrict_query classical viewTermInput (fun r : ViewTermRequest G => r.2.1.tag = 6) _ Q.width
    have hj := restrict_query classical viewTermInput (fun r : ViewTermRequest G => r.2.1.tag = 6) _ Q.term
    have h := source_unitaryTerm_generated classical grammar arithmetic primitive enc
      (fun r => r.val.1.property) (fun r => []) (fun r => r.val.2.2) (nil_generated classical enc _) hq hj
    simpa only [viewPadding_term] using h

/-- Full native source-term generation from the original literal source
format, including the owned measurement expansion and out-of-range padding. -/
theorem canonicalNativeTerm_generated (classical : FLListClosure) (numeric : ClassicalDescriptionClosure)
    (grammar : InstructionDescriptionClosure) (arithmetic : NatArithmeticDescription)
    (queries : FLDataQueryDescription) (prefixParsing : UnaryPrefixParsing) (vectors : NatVectorParsing)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv)
    (parsing : SourceDescriptionParsing G) (opParsing : SourceOperationParsing G) :
    GeneratedCircuit (sourceTermInput (G := G))
      (fun r => canonicalNativeTerm conv r.1 r.2.1 r.2.2) := by
  have h := (viewTerm_generated classical grammar arithmetic queries prefixParsing vectors primitive).pullback
    classical sourceTermInput viewTermInput termViewRequest _
    (termViewRequest_generated classical numeric arithmetic queries prefixParsing parsing opParsing)
  simpa only [canonicalNativeTerm_eq_viewRequest] using h

end Paper25.OperationalModel.UniformCompilation

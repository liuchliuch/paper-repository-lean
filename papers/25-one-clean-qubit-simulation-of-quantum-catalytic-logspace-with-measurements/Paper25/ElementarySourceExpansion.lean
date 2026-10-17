import Paper25.ElementaryEncoding
import Paper25.SourceHistory

/-! # Three-step measurement expansion into encoded source primitives

All constructed steps are actual constant-local source channels. The measurement
macro contributes reset-outcome, CNOT, dephase-outcome in that temporal order.
The complete expanded list has the original Liouville action and length at
most three times the source list length.
-/
noncomputable section
namespace Paper25.ElementaryEncoding
open OperationalModel

/-- Liouville action of a fixed physical wire placement. -/
def liftLiouville {q k : ℕ} (p : Placement q k)
    (S : Matrix (Basis k × Basis k) (Basis k × Basis k) ℂ) :
    Matrix (Basis q × Basis q) (Basis q × Basis q) ℂ :=
  ((Matrix.kronecker S (1 : Matrix (Basis (q-k) × Basis (q-k))
    (Basis (q-k) × Basis (q-k)) ℂ)).submatrix
      (reshuffleEquiv (α := Basis k) (β := Basis (q-k))
        (γ := Basis k) (δ := Basis (q-k)))
      (reshuffleEquiv (α := Basis k) (β := Basis (q-k))
        (γ := Basis k) (δ := Basis (q-k)))).submatrix
      (p.split.prodCongr p.split) (p.split.prodCongr p.split)

lemma placement_liouville {q k : ℕ} (p : Placement q k)
    (C : KrausChannel (Basis k)) :
    (p.liftChannel C).liouville = liftLiouville p C.liouville := by
  rw [Placement.liftChannel, relabel_liouville, extendRight_liouville]
  rfl

lemma liftLiouville_mul {q k : ℕ} (p : Placement q k)
    (S T : Matrix (Basis k × Basis k) (Basis k × Basis k) ℂ) :
    liftLiouville p (S * T) = liftLiouville p S * liftLiouville p T := by
  simp only [liftLiouville, Matrix.submatrix_mul_equiv]
  simp only [Matrix.kronecker, ← Matrix.mul_kronecker_mul, one_mul]

/-- Lift the explicit two-bit local channel without an arbitrary basis change. -/
def liftTwoChannel {q : ℕ} (p : Placement q 2)
    (C : KrausChannel (Bit × Bit)) : KrausChannel (Basis q) :=
  p.liftChannel (relabelChannel (finTwoArrowEquiv Bit) C)

def liftTwoTerms {q : ℕ} (p : Placement q 2)
    {C : KrausChannel (Bit × Bit)} (A : EightChannelTerms C) :
    EightChannelTerms (liftTwoChannel p C) :=
  (A.relabel (finTwoArrowEquiv Bit)).placement p

/-- A real local source primitive. The last three constructors are the exact
constant-local implementation of a retained measurement. -/
inductive SourcePrimitive (q : ℕ) where
  | unitary {k : ℕ} (p : Placement q k) (U : Operator k)
      (hU : U ∈ Matrix.unitaryGroup (Basis k) ℂ)
  | dephase (p : Placement q 1)
  | reset (p : Placement q 1)
  | outcomeReset (p : Placement q 2)
  | copyBasis (p : Placement q 2)
  | outcomeDephase (p : Placement q 2)

namespace SourcePrimitive

def channel {q : ℕ} : SourcePrimitive q → KrausChannel (Basis q)
  | .unitary p U hU =>
    KrausChannel.unitary (p.lift U) (p.lift_unitary U ⟨hU.1, hU.2⟩).1
  | .dephase p => p.liftChannel (relabelChannel oneBit KrausChannel.dephase)
  | .reset p => p.liftChannel (relabelChannel oneBit KrausChannel.reset)
  | .outcomeReset p => liftTwoChannel p (KrausChannel.reset.extendLeft Bit)
  | .copyBasis p => liftTwoChannel p
      (KrausChannel.unitary KrausChannel.copyGate KrausChannel.copyGate_unitary)
  | .outcomeDephase p => liftTwoChannel p (KrausChannel.dephase.extendLeft Bit)

def arity {q : ℕ} : SourcePrimitive q → ℕ
  | .unitary (k := k) _ _ _ => k
  | .dephase _ => 1
  | .reset _ => 1
  | .outcomeReset _ => 2
  | .copyBasis _ => 2
  | .outcomeDephase _ => 2

/-- The eight unitary terms are constructed from the primitive's actual matrix,
Pauli dephasing/reset terms, wire identity extensions, and wire permutations. -/
def encoding {q : ℕ} : (g : SourcePrimitive q) → EightChannelTerms g.channel
  | .unitary p U hU =>
    unitaryTerms (p.lift U) (Matrix.mem_unitaryGroup_iff'.mpr
      (p.lift_unitary U ⟨hU.1, hU.2⟩).1)
  | .dephase p => (dephaseTerms.relabel oneBit).placement p
  | .reset p => (resetTermsWitness.relabel oneBit).placement p
  | .outcomeReset p => liftTwoTerms p (resetTermsWitness.extendLeft (ρ := Bit))
  | .copyBasis p => liftTwoTerms p (unitaryTerms KrausChannel.copyGate
      (Matrix.mem_unitaryGroup_iff'.mpr KrausChannel.copyGate_unitary))
  | .outcomeDephase p => liftTwoTerms p (dephaseTerms.extendLeft (ρ := Bit))

/-- Temporal product; the first primitive acts first. -/
def product {q : ℕ} : List (SourcePrimitive q) →
    Matrix (Basis q × Basis q) (Basis q × Basis q) ℂ
  | [] => 1
  | g :: gs => product gs * g.channel.liouville

lemma product_append {q : ℕ} (xs ys : List (SourcePrimitive q)) :
    product (xs ++ ys) = product ys * product xs := by
  induction xs with
  | nil => simp [product]
  | cons x xs ih => simp [product, ih, mul_assoc]

end SourcePrimitive

/-- Replace the measurement macro by its three actual source operations. -/
def expandSourceOp {G : GateSet} {q : ℕ} : SourceOp G q → List (SourcePrimitive q)
  | .gate g => [.unitary g.placement (G.matrix g.symbol)
      (Matrix.mem_unitaryGroup_iff'.mpr (G.unitary g.symbol).1)]
  | .dephase p => [.dephase p]
  | .reset p => [.reset p]
  | .measurement p => [.outcomeReset p, .copyBasis p, .outcomeDephase p]

lemma expandSourceOp_length {G : GateSet} {q : ℕ} (g : SourceOp G q) :
    (expandSourceOp g).length ≤ 3 := by
  cases g <;> simp [expandSourceOp]

lemma expandSourceOp_locality {G : GateSet} {q : ℕ} (g : SourceOp G q)
    (h : SourcePrimitive q) (hh : h ∈ expandSourceOp g) :
    h.arity ≤ max G.locality 2 := by
  cases g with
  | gate g =>
    simp only [expandSourceOp, List.mem_singleton] at hh
    subst h
    exact (G.arity_le g.symbol).trans (le_max_left _ _)
  | dephase p =>
    simp only [expandSourceOp, List.mem_singleton] at hh
    subst h
    exact (by norm_num : (1 : ℕ) ≤ 2).trans (le_max_right _ _)
  | reset p =>
    simp only [expandSourceOp, List.mem_singleton] at hh
    subst h
    exact (by norm_num : (1 : ℕ) ≤ 2).trans (le_max_right _ _)
  | measurement p =>
    simp only [expandSourceOp, List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl <;> exact le_max_right _ _

lemma reindex_mul {a b : Type*} [Fintype a] [Fintype b]
    (e : a ≃ b) (S T : Matrix b b ℂ) :
    (S * T).submatrix e e = S.submatrix e e * T.submatrix e e :=
  (Matrix.submatrix_mul_equiv S T e e e).symm

/-- The three-step expansion has exactly the original macro's full operator
semantics, rather than only its action on a particular input density. -/
lemma expandSourceOp_product {G : GateSet} {q : ℕ} (g : SourceOp G q) :
    SourcePrimitive.product (expandSourceOp g) = g.channel.liouville := by
  cases g with
  | gate g =>
    simp only [expandSourceOp, SourcePrimitive.product, SourcePrimitive.channel,
      SourceOp.channel, LocalGate.matrix, one_mul]
  | dephase p => simp [expandSourceOp, SourcePrimitive.product, SourcePrimitive.channel,
      SourceOp.channel]
  | reset p => simp [expandSourceOp, SourcePrimitive.product, SourcePrimitive.channel,
      SourceOp.channel]
  | measurement p =>
    simp only [expandSourceOp, SourcePrimitive.product, SourcePrimitive.channel,
      SourceOp.channel, liftTwoChannel, one_mul, placement_liouville,
      relabel_liouville, KrausChannel.measurement, KrausChannel.liouville_comp,
      reindex_mul, liftLiouville_mul, mul_assoc]

/-- Expand a fixed chronological source schedule. -/
def expandSourceCircuit {G : GateSet} {q : ℕ} (C : SourceCircuit G q) :=
  C.flatMap expandSourceOp

lemma expandSourceCircuit_product {G : GateSet} {q : ℕ} (C : SourceCircuit G q) :
    SourcePrimitive.product (expandSourceCircuit C) = C.channel.liouville := by
  induction C with
  | nil =>
    simp only [expandSourceCircuit, List.flatMap_nil, SourcePrimitive.product,
      SourceCircuit.channel]
    symm
    exact KrausChannel.liouville_identity
  | cons g gs ih =>
    change SourcePrimitive.product (expandSourceOp g ++ expandSourceCircuit gs) = _
    rw [SourcePrimitive.product_append, ih, expandSourceOp_product,
      SourceCircuit.channel, KrausChannel.liouville_comp]

lemma expandSourceCircuit_length {G : GateSet} {q : ℕ} (C : SourceCircuit G q) :
    (expandSourceCircuit C).length ≤ 3 * C.length := by
  induction C with
  | nil => simp [expandSourceCircuit]
  | cons g gs ih =>
    change (expandSourceOp g ++ expandSourceCircuit gs).length ≤ _
    rw [List.length_append, List.length_cons]
    have hg := expandSourceOp_length g
    omega

/-- The effective-angle source model uses the same exact primitive expansion. -/
def expandEffectiveSourceOp {G : EffectiveGateSet} {q : ℕ} :
    EffectiveSourceOp G q → List (SourcePrimitive q)
  | .gate g => [.unitary g.placement (G.matrix g.kind g.payload)
      (Matrix.mem_unitaryGroup_iff'.mpr (G.unitary g.kind g.payload).1)]
  | .dephase p => [.dephase p]
  | .reset p => [.reset p]
  | .measurement p => [.outcomeReset p, .copyBasis p, .outcomeDephase p]

lemma expandEffectiveSourceOp_length {G : EffectiveGateSet} {q : ℕ}
    (g : EffectiveSourceOp G q) : (expandEffectiveSourceOp g).length ≤ 3 := by
  cases g <;> simp [expandEffectiveSourceOp]

lemma expandEffectiveSourceOp_product {G : EffectiveGateSet} {q : ℕ}
    (g : EffectiveSourceOp G q) :
    SourcePrimitive.product (expandEffectiveSourceOp g) = g.channel.liouville := by
  cases g with
  | gate g =>
    simp only [expandEffectiveSourceOp, SourcePrimitive.product, SourcePrimitive.channel,
      EffectiveSourceOp.channel, EffectiveLocalGate.matrix, one_mul]
  | dephase p => simp [expandEffectiveSourceOp, SourcePrimitive.product,
      SourcePrimitive.channel, EffectiveSourceOp.channel]
  | reset p => simp [expandEffectiveSourceOp, SourcePrimitive.product,
      SourcePrimitive.channel, EffectiveSourceOp.channel]
  | measurement p =>
    simp only [expandEffectiveSourceOp, SourcePrimitive.product, SourcePrimitive.channel,
      EffectiveSourceOp.channel, liftTwoChannel, one_mul, placement_liouville,
      relabel_liouville, KrausChannel.measurement, KrausChannel.liouville_comp,
      reindex_mul, liftLiouville_mul, mul_assoc]

def expandEffectiveSourceCircuit {G : EffectiveGateSet} {q : ℕ}
    (C : EffectiveSourceCircuit G q) := C.flatMap expandEffectiveSourceOp

lemma expandEffectiveSourceCircuit_product {G : EffectiveGateSet} {q : ℕ}
    (C : EffectiveSourceCircuit G q) :
    SourcePrimitive.product (expandEffectiveSourceCircuit C) = C.channel.liouville := by
  induction C with
  | nil =>
    simp only [expandEffectiveSourceCircuit, List.flatMap_nil, SourcePrimitive.product,
      EffectiveSourceCircuit.channel]
    symm
    exact KrausChannel.liouville_identity
  | cons g gs ih =>
    change SourcePrimitive.product (expandEffectiveSourceOp g ++ expandEffectiveSourceCircuit gs) = _
    rw [SourcePrimitive.product_append, ih, expandEffectiveSourceOp_product,
      EffectiveSourceCircuit.channel, KrausChannel.liouville_comp]

lemma expandEffectiveSourceCircuit_length {G : EffectiveGateSet} {q : ℕ}
    (C : EffectiveSourceCircuit G q) :
    (expandEffectiveSourceCircuit C).length ≤ 3 * C.length := by
  induction C with
  | nil => simp [expandEffectiveSourceCircuit]
  | cons g gs ih =>
    change (expandEffectiveSourceOp g ++ expandEffectiveSourceCircuit gs).length ≤ _
    rw [List.length_append, List.length_cons]
    have hg := expandEffectiveSourceOp_length g
    omega

/-- The actual expanded channel at a schedule position, with identity padding. -/
def primitiveChannelAt {q : ℕ} (xs : List (SourcePrimitive q)) (t : ℕ) :
    KrausChannel (Basis q) :=
  match xs[t]? with
  | some g => g.channel
  | none => KrausChannel.identity

/-- Explicit eight-term witnesses at every schedule position. -/
def primitiveEncodingAt {q : ℕ} (xs : List (SourcePrimitive q)) (t : ℕ) :
    EightChannelTerms (primitiveChannelAt xs t) := by
  unfold primitiveChannelAt
  cases h : xs[t]? with
  | some g => exact g.encoding
  | none => exact unitaryTerms 1 (Matrix.unitaryGroup (Basis q) ℂ).one_mem

/-- Adapt to any finite enumeration/reordering used by the channel history. -/
def primitiveTermsAt {q : ℕ} {a : Type*} [Fintype a] [DecidableEq a]
    (xs : List (SourcePrimitive q)) (e : a ≃ (Basis q × Basis q))
    (t : ℕ) : Fin 8 → Matrix a a ℂ :=
  ((primitiveEncodingAt xs t).reindex e).terms

lemma primitiveTermsAt_unitary {q : ℕ} {a : Type*} [Fintype a] [DecidableEq a]
    (xs : List (SourcePrimitive q)) (e : a ≃ (Basis q × Basis q)) (t : ℕ) (j : Fin 8) :
    primitiveTermsAt xs e t j ∈ Matrix.unitaryGroup a ℂ :=
  ((primitiveEncodingAt xs t).reindex e).terms_unitary j

lemma primitiveTermsAt_average {q : ℕ} {a : Type*} [Fintype a] [DecidableEq a]
    (xs : List (SourcePrimitive q)) (e : a ≃ (Basis q × Basis q)) (t : ℕ) :
    (1 / 8 : ℂ) • ∑ j, primitiveTermsAt xs e t j =
      (1 / 2 : ℂ) • (primitiveChannelAt xs t).liouville.submatrix e e :=
  ((primitiveEncodingAt xs t).reindex e).average

lemma primitiveProduct_take {q : ℕ} (xs : List (SourcePrimitive q)) (n : ℕ)
    (hn : n ≤ xs.length) :
    SourcePrimitive.product (xs.take n) =
      chainProd (fun t => (primitiveChannelAt xs t).liouville) 0 n := by
  induction n with
  | zero => simp [SourcePrimitive.product, chainProd_zero]
  | succ n ih =>
    have hlt : n < xs.length := by omega
    rw [List.take_succ_eq_append_getElem hlt, SourcePrimitive.product_append,
      ih (by omega), chainProd_succ]
    simp [SourcePrimitive.product, primitiveChannelAt, List.getElem?_eq_getElem hlt]

lemma primitiveSequence_liouville {q : ℕ} (xs : List (SourcePrimitive q)) :
    (KrausChannel.sequence (primitiveChannelAt xs) 0 xs.length).liouville =
      SourcePrimitive.product xs := by
  rw [KrausChannel.liouville_sequence]
  simpa using (primitiveProduct_take xs xs.length le_rfl).symm

/-- The actual indexed primitive sequence has the full original effective-source
channel action after the measurement macros are expanded. -/
lemma expandedEffectiveSequence_liouville {G : EffectiveGateSet} {q : ℕ}
    (C : EffectiveSourceCircuit G q) :
    (KrausChannel.sequence (primitiveChannelAt (expandEffectiveSourceCircuit C)) 0
      (expandEffectiveSourceCircuit C).length).liouville = C.channel.liouville := by
  rw [primitiveSequence_liouville, expandEffectiveSourceCircuit_product]

lemma expandedEffectiveSequence_act {G : EffectiveGateSet} {q : ℕ}
    (C : EffectiveSourceCircuit G q) (X : Operator q) :
    (KrausChannel.sequence (primitiveChannelAt (expandEffectiveSourceCircuit C)) 0
      (expandEffectiveSourceCircuit C).length).act X = C.channel.act X := by
  ext a b
  simp only [KrausChannel.liouville_action, expandedEffectiveSequence_liouville]

/-- The expansion preserves all correlations, so the original source's exact
restoration hypothesis transports to the primitive sequence without weakening. -/
lemma expandedEffectiveSequence_reference_act {G : EffectiveGateSet} {q : ℕ}
    (C : EffectiveSourceCircuit G q) (ρ : Type*) [Fintype ρ] [DecidableEq ρ]
    (X : Matrix (Basis q × ρ) (Basis q × ρ) ℂ) :
    ((KrausChannel.sequence (primitiveChannelAt (expandEffectiveSourceCircuit C)) 0
      (expandEffectiveSourceCircuit C).length).extendRight ρ).act X =
      (C.channel.extendRight ρ).act X := by
  ext a b
  simp only [KrausChannel.liouville_action, extendRight_liouville,
    expandedEffectiveSequence_liouville]

end Paper25.ElementaryEncoding

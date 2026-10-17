import ELV.QueryCircuit

/-! The operational converse of (2.10). A witness family determines one fixed
work unitary and a two-gate circuit (one oracle gate followed by that work gate).
The catalysts and costs are computed from its execution. -/
noncomputable section
namespace ELV.Query
open ELV.Stabilize

variable {H Q X I : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- The adversary constraint is a Gram identity for the actual queried vectors. -/
def Witness (O : X → Q ≃ₗᵢ[ℂ] Q) (ξ τ : X → H) (v : X → Q) : Prop :=
  ∀ x y, inner ℂ (ξ x) (ξ y) - inner ℂ (τ x) (τ y) =
    inner ℂ (v x) (v y) - inner ℂ (O x (v x)) (O y (v y))

lemma witness_equalGram {O : X → Q ≃ₗᵢ[ℂ] Q} {ξ τ : X → H} {v : X → Q}
    (h : Witness O ξ τ v) :
    Gram.EqualGram (fun x => WithLp.toLp 2 (ξ x, O x (v x)))
      (fun x => WithLp.toLp 2 (τ x, v x)) := by
  intro x y
  have hh := h x y
  change inner ℂ (ξ x) (ξ y) + inner ℂ (O x (v x)) (O y (v y)) =
    inner ℂ (τ x) (τ y) + inner ℂ (v x) (v y)
  linear_combination hh

abbrev CanonicalPrivate (I : Type*) (H Q : Type*) :=
  HilbertPair Q (Gram.StabilizingSpace I)

/-- The fixed oracle-independent work operation obtained from the full family. -/
def canonicalWork (bV : HilbertBasis I ℂ (HilbertPair H Q))
    {O : X → Q ≃ₗᵢ[ℂ] Q} {ξ τ : X → H} {v : X → Q} (h : Witness O ξ τ v) :
    HilbertPair H (CanonicalPrivate I H Q) ≃ₗᵢ[ℂ] HilbertPair H (CanonicalPrivate I H Q) :=
  (pairAssoc (𝕜 := ℂ) (E := H) (F := Q) (G := Gram.StabilizingSpace I)).symm.trans
    ((Gram.stabilizedUnitary bV (witness_equalGram h)).trans pairAssoc)

/-- One query followed by one fixed work unitary, independent of the instance. -/
def canonicalCircuit (bV : HilbertBasis I ℂ (HilbertPair H Q))
    {O : X → Q ≃ₗᵢ[ℂ] Q} {ξ τ : X → H} {v : X → Q} (h : Witness O ξ τ v) :
    Circuit (HilbertPair H (CanonicalPrivate I H Q))
      (HilbertPair H (Gram.StabilizingSpace I)) Q :=
  [.query queryLayout, .work (canonicalWork bV h)]

def canonicalCatalyst (v : X → Q) (x : X) : CanonicalPrivate I H Q :=
  WithLp.toLp 2 (v x, 0)

lemma canonical_query (O : Q ≃ₗᵢ[ℂ] Q) (ξ : H) (v : Q) :
    (Gate.query (queryLayout (𝕜 := ℂ) (E := H) (F := Q) (G := Gram.StabilizingSpace I))).unitary O
      (WithLp.toLp 2 (ξ, WithLp.toLp 2 (v, 0))) =
        WithLp.toLp 2 (ξ, WithLp.toLp 2 (O v, 0)) := rfl

/-- Equation (2.11), applied to the actual state after the query. -/
theorem canonical_exact (bV : HilbertBasis I ℂ (HilbertPair H Q))
    {O : X → Q ≃ₗᵢ[ℂ] Q} {ξ τ : X → H} {v : X → Q} (h : Witness O ξ τ v) :
    Exact (canonicalCircuit bV h) O ξ τ (canonicalCatalyst (I := I) v) := by
  intro x
  simp only [canonicalCircuit, run, canonicalCatalyst, canonical_query, Gate.unitary]
  change (pairAssoc (𝕜 := ℂ)) (Gram.stabilizedUnitary bV (witness_equalGram h)
    (WithLp.toLp 2 (WithLp.toLp 2 (ξ x, O x (v x)), 0))) = _
  rw [Gram.stabilizedUnitary_apply]
  rfl

/-- The actual cost of the executed one-query circuit is the witness norm. -/
theorem canonical_cost (bV : HilbertBasis I ℂ (HilbertPair H Q))
    {O : X → Q ≃ₗᵢ[ℂ] Q} {ξ τ : X → H} {v : X → Q} (h : Witness O ξ τ v) (x : X) :
    cost (O x) (canonicalCircuit bV h)
      (WithLp.toLp 2 (ξ x, canonicalCatalyst (I := I) v x)) = ‖v x‖ ^ 2 := by
  simp [cost, canonicalCircuit, trace, Fin.sum_univ_succ, Gate.queried,
    canonicalCatalyst, queryLayout]

/-- The catalyst is an actual vector of the same squared norm as the query witness. -/
theorem canonical_catalyst_norm (v : X → Q) (x : X) :
    ‖canonicalCatalyst (I := I) (H := H) v x‖ ^ 2 = ‖v x‖ ^ 2 := by
  simp [canonicalCatalyst, WithLp.prod_norm_sq_eq_of_L2]

/-- No finiteness or countability assumption on the instance family is needed. -/
theorem operational_converse (O : X → Q ≃ₗᵢ[ℂ] Q) (ξ τ : X → H) (v : X → Q)
    (h : Witness O ξ τ v) :
    ∃ (I : Set (HilbertPair H Q))
      (c : Circuit (HilbertPair H (CanonicalPrivate I H Q))
        (HilbertPair H (Gram.StabilizingSpace I)) Q)
      (w : X → CanonicalPrivate I H Q),
      Exact c O ξ τ w ∧ ∀ x,
        cost (O x) c (WithLp.toLp 2 (ξ x, w x)) = ‖v x‖ ^ 2 ∧
        ‖w x‖ ^ 2 = ‖v x‖ ^ 2 := by
  obtain ⟨I, bV, _⟩ := exists_hilbertBasis ℂ (HilbertPair H Q)
  exact ⟨I, canonicalCircuit bV h, canonicalCatalyst v, canonical_exact bV h,
    fun x => ⟨canonical_cost bV h x, canonical_catalyst_norm v x⟩⟩

end ELV.Query

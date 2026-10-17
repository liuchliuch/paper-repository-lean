import Paper12.Main
import Paper12.Threshold
import Paper12.Choi
import Paper12.ChoiCircuit
import Paper12.BlockFailure

/-! Source-facing specifications, with explicit elementary circuits,
clean-workspace semantics, resource bounds, and every-lift preservation. -/
noncomputable section
namespace Paper12.PaperStatements
open Paper12 Matrix Complex Classical

def definition_2_1 : Prop :=
  ∀ (X W : Type) [Fintype X] [Fintype W] (Γ : Subgroup (X ≃ X))
    (C : Circuit (X ⊕ W)) (U : Op X),
    (Nonempty (Symmetric Γ C) ↔
      ∀ γ : Γ, ∃ e : (X ⊕ W) ≃ (X ⊕ W),
        (∀ x, e (Sum.inl x) = Sum.inl (γ.val x)) ∧
        ∀ L ∈ C.layers, Layer.map e L = L) ∧
    (CleanImplements C U ↔
      ∀ ψ, applyOp C.unitary (embedZero ψ) = embedZero (applyOp U ψ)) ∧
    C.size = (C.layers.map (fun L => L.gates.card)).sum

def lemma_2_2 : Prop :=
  ∀ (X W : Type) [Fintype X] [Fintype W] (Γ : Subgroup (X ≃ X))
    (U : Op X) (C : Circuit (X ⊕ W)),
    Symmetric Γ C → CleanImplements C U → Equivariant Γ U

def lemma_2_3 : Prop :=
  ∀ (X : Type) [Fintype X] (Γ : Subgroup (X ≃ X)) (U : Op X),
    Uᴴ * U = 1 → Equivariant Γ U →
    (∀ γ ∈ Γ, ∀ w : PWord X, pauliCoeff U (actWord γ w) = pauliCoeff U w) ∧
    (∑ w : PWord X, Complex.abs (pauliCoeff U w) ^ 2 = 1)

def lemma_2_4 : Prop :=
  ∀ (d k : ℕ) (θ : ℝ) (P : Matrix (Fin d) (Fin d) ℂ)
    (S G : Matrix (Fin d) (Fin k) ℂ),
    TwoReflectionData θ P S G →
    IsIsometry (twoReflB θ S G) ∧ Gᴴ * twoReflB θ S G = 0 ∧
    P * twoReflB θ S G = 0 ∧
    (∀ j : ℕ, (RS S * RG P) ^ j * S = (-1 : ℂ) ^ j •
      ((Real.sin ((2 * j + 1) * θ) : ℂ) • G +
        (Real.cos ((2 * j + 1) * θ) : ℂ) • twoReflB θ S G))

/-- One wire for each nonzero Pauli coefficient. -/
abbrev Selector {X : Type} [Fintype X] (α : Coeffs X) :=
  {w : PWord X // w ∈ coeffSupport α}

def chi {X : Type} [Fintype X] (α : Coeffs X) : Vec (Selector α) :=
  fun b => ∑ q : Selector α,
    if b = oneHot q then (selectorAmp α q.val : ℂ) else 0

/-- The full preparation, workspace reset, gate bound and orbitwise layer symmetry. -/
def lemma_2_5 : Prop :=
  ∀ (X : Type) [Fintype X] (α : Coeffs X), 0 < coeffMass α →
    ∃ B : Circuit (Selector α ⊕ Fin 3),
      applyOp B.unitary (embedZero (eBasis (zeroBasis (Selector α)))) =
        embedZero (chi α) ∧
      B.size ≤ 40 * (coeffCard α + 1) ∧
      ∀ τ : Selector α ≃ Selector α,
        (∀ q, α (τ q).val = α q.val) →
        ∀ L ∈ B.layers, Layer.map (liftFixW τ) L = L

/-- Add two fixed wires to a lift, using the actual sum-register association. -/
def extendLift {X W : Type} (e : (X ⊕ W) ≃ (X ⊕ W)) :
    (X ⊕ (W ⊕ Fin 2)) ≃ (X ⊕ (W ⊕ Fin 2)) :=
  (Equiv.sumAssoc X W (Fin 2)).symm |>.trans
    (e.sumCongr (Equiv.refl (Fin 2))) |>.trans (Equiv.sumAssoc X W (Fin 2))

def lemma_4_1 : Prop :=
  ∀ (X W : Type) [Fintype X] [Fintype W] (Γ : Subgroup (X ≃ X))
    (A : Circuit (X ⊕ W)) (V : Op X) (p : ℝ),
    Vᴴ * V = 1 → Symmetric Γ A → 0 < p → p < 1 → BlockEncodes A.unitary p V →
    ∃ C : Circuit (X ⊕ (W ⊕ Fin 2)),
      C.size ≤ 32 * (A.size + 1) * (ampK p + 1) ∧
      Nonempty (Symmetric Γ C) ∧ CleanImplements C V ∧
      ∀ (γ : X ≃ X) (e : (X ⊕ W) ≃ (X ⊕ W)),
        (∀ x, e (Sum.inl x) = Sum.inl (γ x)) →
        (∀ L ∈ A.layers, Layer.map e L = L) →
        ∀ L ∈ C.layers, Layer.map (extendLift e) L = L

def theorem_1_1 : Prop :=
  ∀ (X : Type) [Fintype X] (Γ : Subgroup (X ≃ X)) (U : Op X), Uᴴ * U = 1 →
    ((∃ nW s, HasCleanSymmetricCircuit Γ U nW s) ↔ Equivariant Γ U) ∧
    (0 < Fintype.card X → Equivariant Γ U →
      HasCleanSymmetricCircuit Γ U (resourceM U + 5) (sizeBound U)) ∧
    (Fintype.card X = 0 → HasCleanSymmetricCircuit Γ U 1 1) ∧
    resourceM U ≤ 4 ^ Fintype.card X ∧
    (1 ≤ resourceLambda U ∧ resourceLambda U ≤ Real.sqrt (resourceM U)) ∧
    (sizeBound U : ℝ) ≤
      49152 * (Fintype.card X : ℝ) * resourceM U * resourceLambda U

def corollary_4_2 : Prop :=
  ∀ (X G : Type) [Fintype X] [Group G] (ρ : G →* (X ≃ X)) (U : Op X),
    Uᴴ * U = 1 → (∀ g : G, U * R (ρ g) = R (ρ g) * U) →
    (∃ nW s, HasCleanSymmetricCircuit (Subgroup.map ρ ⊤) U nW s) ∧
    (0 < Fintype.card X →
      HasCleanSymmetricCircuit (Subgroup.map ρ ⊤) U (resourceM U + 5) (sizeBound U))

/-- Equation (2) on the full register, for arbitrary thresholds and controls. -/
def equation_2 : Prop :=
  ∀ (J : Type) [Fintype J] (g : Threshold J),
    g.unitary * (nextThreshold g).unitary =
      (fun i j : Basis J => if equalityAct g j = i then (1 : ℂ) else 0)

/-- Equation (4), with coefficients defined by normalized Pauli traces. -/
def equation_4 : Prop :=
  ∀ (X : Type) [Fintype X] (U : Op X), pauliExpand U = U

/-- The exact one-gate empty-register subcase of Theorem 1.1. -/
def empty_case : Prop :=
  ∀ (X : Type) [Fintype X] [IsEmpty X] (Γ : Subgroup (X ≃ X)) (U : Op X),
    Uᴴ * U = 1 → HasCleanSymmetricCircuit Γ U 1 1

/-- Appendix A, equation (23), in computational-basis coordinates. -/
def equation_23 : Prop :=
  ∀ (X : Type) [Fintype X] (U : Op X) (ψ : Vec X) (b : Basis X),
    (∑ i : Basis X, ∑ a : Basis X, bellCoeff i a * ψ i * choiCoeff U a b) =
      ((2 : ℂ) ^ Fintype.card X)⁻¹ * applyOp U ψ b

/-- Equation (13), for the literal incidence-and-phase elementary circuit. -/
def equation_13 : Prop :=
  ∀ (X : Type) [Fintype X] (α : Coeffs X) (q : SelectorWire α) (ψ : Vec X),
    applyOp (fullSelection α).unitary (registerVec ψ (eBasis (oneHot q))) =
      selectorPhase α q.val • registerVec (applyOp (pop X q.val) ψ) (eBasis (oneHot q))

/-- Equation (16), for the literal B† SEL B circuit. -/
def equation_16 : Prop :=
  ∀ (X : Type) [Fintype X] (U : Op X), Uᴴ * U = 1 →
    zeroBlock (blockCircuit (pauliCoeff U)).unitary =
      ((coeffMass (pauliCoeff U) : ℂ)⁻¹) • U

/-- Equation (17), including the input-independent complementary isometry. -/
def equation_17 : Prop :=
  ∀ (X W : Type) [Fintype X] [Fintype W] (A : Circuit (X ⊕ W)) (U : Op X) (p : ℝ),
    Uᴴ * U = 1 → 0 ≤ p → p < 1 → BlockEncodes A.unitary p U →
    ∃ F : Matrix (Basis (X ⊕ W)) (Basis X) ℂ,
      IsIsometry F ∧ (zeroEmbed (X := X) (W := W))ᴴ * F = 0 ∧
      A.unitary * zeroEmbed = (Real.sqrt p : ℂ) • (zeroEmbed * U) +
        (Real.sqrt (1 - p) : ℂ) • F

/-- Equation (18), counting the actual elementary gates of A. -/
def equation_18 : Prop :=
  ∀ (X : Type) [Fintype X] (α : Coeffs X), 0 < Fintype.card X →
    (blockCircuit α).size + 1 ≤ 256 * Fintype.card X * (coeffCard α + 1)

/-- Appendix A: the literal Bell-unpreparation/three-CNOT-swap reduction,
its exact block, chosen-lift extension, clean amplification, and resources. -/
def appendix_choi : Prop :=
  ∀ (X T : Type) [Fintype X] [Fintype T] (Γ : Subgroup (X ≃ X))
    (CJ : Circuit ((X ⊕ X) ⊕ T)) (U : Op X), Uᴴ * U = 1 →
    applyOp CJ.unitary (zeroKet _) = embedZero (W := T) (choiVec U) →
    (∀ γ : Γ, ∃ e : ((X ⊕ X) ⊕ T) ≃ ((X ⊕ X) ⊕ T),
      (∀ x, e (Sum.inl x) = Sum.inl ((γ.val.sumCongr γ.val) x)) ∧ CJ.Preserved e) →
    zeroBlock (choiBlock CJ).unitary = ((2 : ℂ) ^ Fintype.card X)⁻¹ • U ∧
    Nonempty (Symmetric Γ (choiBlock CJ)) ∧
    ∃ C : Circuit (X ⊕ (((X ⊕ X) ⊕ T) ⊕ Fin 2)),
      CleanImplements C U ∧ Nonempty (Symmetric Γ C) ∧
      Fintype.card (((X ⊕ X) ⊕ T) ⊕ Fin 2) = 2 * Fintype.card X + Fintype.card T + 2 ∧
      C.size ≤ 32 * (CJ.size + 5 * Fintype.card X + 1) * (ampK (choiProbability X) + 1) ∧
      ∀ (γ : X ≃ X) (e : ((X ⊕ X) ⊕ T) ≃ ((X ⊕ X) ⊕ T)),
        (∀ x, e (Sum.inl x) = Sum.inl ((γ.sumCongr γ) x)) → CJ.Preserved e →
        C.Preserved (outerFinalLift (γ.sumCongr e))

end Paper12.PaperStatements

import PUT.CollisionAlgorithm

/-!
# The uniformity tester really yields a collision algorithm

Kutin's published lower bound is the sole external input in this module.
The function-dependent preparation, controlled calls, finite workspace,
query replacement, promise preservation, and Born-output equality are proved.
-/
noncomputable section
set_option maxRecDepth 4096
namespace PUT.CollisionTester
open PUT.QueryModel PUT.SourceTargets PUT.CollisionReduction PUT.CollisionCircuit
open PUT.CollisionQuerySimulation

section Conjugation
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

def conjugate (e : E ≃ₗᵢ[ℂ] F) (U : F ≃ₗᵢ[ℂ] F) : E ≃ₗᵢ[ℂ] E :=
  (e.trans U).trans e.symm

@[simp] theorem conjugate_trans (e : E ≃ₗᵢ[ℂ] F) (f : F ≃ₗᵢ[ℂ] G)
    (U : G ≃ₗᵢ[ℂ] G) : conjugate (e.trans f) U = conjugate e (conjugate f U) := by
  ext x
  rfl

def registerShape {I : Type*} [Fintype I] (e : E ≃ₗᵢ[ℂ] F) :
    Register I E ≃ₗᵢ[ℂ] Register I F :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ => e)

@[simp] theorem conjugate_workspace {I : Type*} [Fintype I]
    (e : E ≃ₗᵢ[ℂ] F) (U : F ≃ₗᵢ[ℂ] F) :
    conjugate (registerShape (I := I) e) (withWorkspace U) =
      withWorkspace (conjugate e U) := by
  ext x : 1
  ext i : 1
  rfl

@[simp] theorem conjugate_controlled (e : E ≃ₗᵢ[ℂ] F) (U : E ≃ₗᵢ[ℂ] E) :
    conjugate (registerShape (I := Bool) e) (controlled ((e.symm.trans U).trans e)) =
      controlled U := by
  ext x : 1
  ext c : 1
  cases c <;> simp [conjugate, registerShape, controlled]

end Conjugation

variable {D R : ℕ} [NeZero D]

abbrev FlatBasis (D R W : ℕ) := Fin W × (Bool × Basis D R)

def bodyShape : EuclideanSpace ℂ (Bool × Basis D R) ≃ₗᵢ[ℂ]
    Register Bool (PurificationSpace (D+R) ((D+R)*D)) :=
  controlCurry.trans (registerShape (lift reshape))

/-- The same finite physical/work registers as `TesterFamily`, merely regrouped. -/
def testerShape (W : ℕ) : EuclideanSpace ℂ (FlatBasis D R W) ≃ₗᵢ[ℂ]
    TestSpace (D+R) ((D+R)*D) W :=
  pairCurry.trans (registerShape bodyShape)

/-- The full unknown operator matches the proved four-query implementation,
including its arbitrary-input action and the inactive controlled block. -/
theorem testerShape_oracle (W : ℕ) (f : Fin D → Fin D) :
    conjugate (testerShape (D := D) (R := R) W)
      (withWorkspace (controlled (physicalUnitary f))) =
      workspaceUnitary (I := Fin W) (controlUnitary (unitary f)) := by
  simp only [testerShape, conjugate_trans, conjugate_workspace, bodyShape,
    conjugate_trans, physicalUnitary, conjugate_controlled]
  rfl

/-- Standard-function-query implementation of a tester's *entire* controlled
physical oracle, with its chosen finite workspace. -/
def testerImplementation (W : ℕ) : Implements (D := D)
    (fun f => conjugate (testerShape (D := D) (R := R) W)
      (withWorkspace (controlled (physicalUnitary f)))) 4 := by
  let h := (controlledPreparationImplementation (D := D) (R := R)).workspace (I := Fin W)
  refine ⟨h.program, h.count, ?_⟩
  intro f v
  rw [testerShape_oracle]
  exact h.correct f v

/-- The actual standard-query collision tester obtained from `C`. -/
def collisionAlgorithm (C : TesterFamily (D+R)) (Q : ℕ) :
    FunctionAlgorithm (FlatBasis D R (C.workspace ((D+R)*D))) D :=
  simulateCircuit (conjugateCircuit (testerShape _) (C.circuit ((D+R)*D)))
    (testerImplementation _) Q

@[simp] theorem collisionAlgorithm_queries (C : TesterFamily (D+R)) (Q : ℕ) :
    (collisionAlgorithm C Q).program.queries = 4*Q := simulateCircuit_queries _ _ _

@[simp] theorem collisionAlgorithm_probability (C : TesterFamily (D+R)) (Q : ℕ)
    (f : Fin D → Fin D) :
    (collisionAlgorithm C Q).rejectProbability f =
      (C.circuit ((D+R)*D)).rejectProbability (C.oracle (preparationOracle f)) Q := by
  rw [collisionAlgorithm, simulateCircuit_probability]
  exact conjugateCircuit_probability _ _ _ _

/-- Exact promise preservation for arbitrary tester workspace and directions. -/
theorem collisionAlgorithm_tests (C : TesterFamily (D+R)) (Q : ℕ) (ε : ℝ)
    (hC : C.Tests ε Q) (hfar : ε < (3*D : ℝ)/(4*(D+R))) :
    (∀ f : Fin D → Fin D, Function.Injective f →
      (collisionAlgorithm C Q).rejectProbability f ≤ 1/3) ∧
    (∀ f : Fin D → Fin D, FourToOne f →
      2/3 ≤ (collisionAlgorithm C Q).rejectProbability f) := by
  constructor
  · intro f hf
    rw [collisionAlgorithm_probability]
    have h := (hC ((D+R)*D) (preparationOracle f)).1 (by
      rw [preparationOracle_law, extend_law_injective f hf]
      intro i; rfl)
    linarith
  · intro f hf
    rw [collisionAlgorithm_probability]
    have h := (hC ((D+R)*D) (preparationOracle f)).2 (by
      rw [preparationOracle_law, fourToOne_tv (NeZero.pos (D+R)) f hf]
      exact hfar)
    linarith

end PUT.CollisionTester

namespace PUT.External
open PUT.CollisionReduction PUT.CollisionQuerySimulation

/-- Published external input, Kutin (2005), Theorem 1.1, specialized to
four-to-one functions with range `[D]` and bounded error at most `1/3`.
The query primitive is exactly `standard`; inverse queries cost one by
`standard_inverse`. No uniformity tester or simulation claim is in this law.
Source: https://theoryofcomputing.org/articles/v001a002/v001a002.pdf, p.30.
-/
def KutinCollisionLaw : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ (D : ℕ) [NeZero D], 4 ∣ D →
    ∀ (B : Type) [Fintype B] [DecidableEq B] (A : FunctionAlgorithm B D),
      ((∀ f : Fin D → Fin D, Function.Injective f → A.rejectProbability f ≤ 1/3) ∧
       (∀ f : Fin D → Fin D, FourToOne f → 2/3 ≤ A.rejectProbability f)) →
      κ * ((D : ℝ)/4) ^ (1/3 : ℝ) ≤ (A.program.queries : ℝ)

end PUT.External

namespace PUT.CollisionTester
open PUT.QueryModel PUT.SourceTargets PUT.CollisionReduction PUT.CollisionCircuit
open PUT.CollisionQuerySimulation
open PUT.External

/-- The paper's collision reduction, with the actual tester query count,
proved from the published standard-function collision theorem. -/
theorem query_lower_bound (hK : KutinCollisionLaw) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (D R : ℕ) [NeZero D], 4 ∣ D →
      ∀ (ε : ℝ) (C : TesterFamily (D+R)) (Q : ℕ),
        C.Tests ε Q → ε < (3*D : ℝ)/(4*(D+R)) →
        κ * ((D : ℝ)/4) ^ (1/3 : ℝ) ≤ (Q : ℝ) := by
  obtain ⟨κ,hκ,hK⟩ := hK
  refine ⟨κ/4, by positivity, ?_⟩
  intro D R _ hD ε C Q hC hfar
  have h := hK D hD (FlatBasis D R (C.workspace ((D+R)*D)))
    (collisionAlgorithm C Q) (collisionAlgorithm_tests C Q ε hC hfar)
  rw [collisionAlgorithm_queries, Nat.cast_mul, Nat.cast_ofNat] at h
  nlinarith

/-- Constant-accuracy lower bound for every dimension in the actual source
model. Rounding the collision size and the finitely many small dimensions are
proved here; neither is included in the external Kutin input. -/
theorem constant_accuracy_lower (hKutin : PUT.External.KutinCollisionLaw) :
    ∃ k : ℝ, 0 < k ∧ ∀ (d : ℕ) (ε : ℝ), 2 ≤ d → ε < 1/2 →
      ∀ (C : TesterFamily d) (Q : ℕ), C.Tests ε Q →
        k * (d : ℝ) ^ (1/3 : ℝ) ≤ (Q : ℝ) := by
  obtain ⟨κ,hκ,hbound⟩ := query_lower_bound hKutin
  let k := min (κ/8) (1/8 : ℝ)
  refine ⟨k, lt_min (by positivity) (by norm_num), ?_⟩
  intro d ε hd hε C Q hC
  have hkκ : k ≤ κ/8 := min_le_left _ _
  have hk1 : k ≤ (1/8 : ℝ) := min_le_right _ _
  have hpow0 : 0 ≤ (d : ℝ) ^ (1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  by_cases hd8 : 8 ≤ d
  · let D := collD d
    let R := d - D
    have hDle : D ≤ d := by dsimp [D, collD]; omega
    have hDpos : 0 < D := by dsimp [D, collD]; omega
    letI : NeZero D := ⟨Nat.ne_of_gt hDpos⟩
    have hdim : D + R = d := Nat.add_sub_of_le hDle
    have hdiv : 4 ∣ D := ⟨d/4,rfl⟩
    have hex : ∃ C' : TesterFamily (D+R), C'.Tests ε Q := by
      rw [hdim]
      exact ⟨C,hC⟩
    obtain ⟨C',hC'⟩ := hex
    have hfar : ε < (3*D : ℝ)/(4*(D+R)) := by
      have he : (D : ℝ) + R = d := by exact_mod_cast hdim
      have hhalf := collTV_gt_half d hd8
      unfold collTV at hhalf
      dsimp [D]
      rw [he]
      exact hε.trans hhalf
    have hq := hbound D R hdiv ε C' Q hC' hfar
    have hsize : (d : ℝ) ≤ 8*((D : ℝ)/4) := by
      have hnat : d ≤ 2*D := by dsimp [D, collD]; omega
      have hr : (d : ℝ) ≤ 2*D := by exact_mod_cast hnat
      nlinarith
    have h8pow : (8 : ℝ) ^ (1/3 : ℝ) ≤ 8 :=
      Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    have hpower : (d : ℝ) ^ (1/3 : ℝ) ≤ 8*((D : ℝ)/4) ^ (1/3 : ℝ) := by
      calc
        _ ≤ (8*((D : ℝ)/4)) ^ (1/3 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hsize (by norm_num)
        _ = (8 : ℝ) ^ (1/3 : ℝ) * ((D : ℝ)/4) ^ (1/3 : ℝ) :=
          Real.mul_rpow (by norm_num) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right h8pow (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hpower (le_of_lt hκ)
    have hk := mul_le_mul_of_nonneg_right hkκ hpow0
    nlinarith
  · have hq : (1 : ℝ) ≤ Q := by exact_mod_cast tester_needs_query hd hε C Q hC
    have hpow : (d : ℝ) ^ (1/3 : ℝ) ≤ 8 := by
      calc
        _ ≤ (d : ℝ) := Real.rpow_le_self_of_one_le (by exact_mod_cast (by omega : 1 ≤ d))
          (by norm_num)
        _ ≤ 8 := by exact_mod_cast (by omega : d ≤ 8)
    have hk := mul_le_mul_of_nonneg_right hk1 hpow0
    nlinarith

end PUT.CollisionTester

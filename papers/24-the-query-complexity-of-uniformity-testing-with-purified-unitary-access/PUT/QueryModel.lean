import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Unitary query circuits and their adversary progress

The query count below is the number of actual calls in a unitary circuit; it
is independent of the claimed lower bound. Hilbert spaces in the progress
lemmas need not be finite dimensional, allowing the latent `L²` spaces of
paper 24, §2. The circuit itself may be instantiated with any finite
`EuclideanSpace ℂ ι`, including arbitrary finite workspace.
-/
noncomputable section

namespace PUT.QueryModel

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An actual two-outcome projective measurement, with reject outcome `P`.
Idempotence and self-adjointness are the usual operator conditions. -/
structure Measurement (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  reject : H →L[ℂ] H
  idem : ∀ x, reject (reject x) = reject x
  hermitian : ∀ x y, ⟪reject x, y⟫_ℂ = ⟪x, reject y⟫_ℂ

def Measurement.accept (P : Measurement H) (x : H) : H := x - P.reject x

def Measurement.rejectionProbability (P : Measurement H) (x : H) : ℝ :=
  ‖P.reject x‖ ^ 2

theorem Measurement.orthogonal (P : Measurement H) (x y : H) :
    ⟪P.accept x, P.reject y⟫_ℂ = 0 := by
  rw [Measurement.accept, inner_sub_left, P.hermitian x (P.reject y), P.idem, sub_self]

theorem Measurement.pythagoras (P : Measurement H) (x : H) :
    ‖x‖ ^ 2 = ‖P.accept x‖ ^ 2 + ‖P.reject x‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (P.accept x) (P.reject x) (P.orthogonal x x)
  simpa [Measurement.accept, sub_add_cancel, sq] using h

theorem Measurement.probability_bounds (P : Measurement H) (x : H) (hx : ‖x‖ = 1) :
    0 ≤ P.rejectionProbability x ∧ P.rejectionProbability x ≤ 1 := by
  have hp := P.pythagoras x
  rw [hx] at hp
  constructor
  · exact sq_nonneg _
  · dsimp [Measurement.rejectionProbability]
    nlinarith [sq_nonneg ‖P.accept x‖]

theorem Measurement.reject_norm (P : Measurement H) (x : H) :
    ‖P.reject x‖ = Real.sqrt (P.rejectionProbability x) := by
  simp [Measurement.rejectionProbability, Real.sqrt_sq (norm_nonneg _)]

theorem Measurement.accept_norm (P : Measurement H) (x : H) (hx : ‖x‖ = 1) :
    ‖P.accept x‖ = Real.sqrt (1 - P.rejectionProbability x) := by
  have hp := P.pythagoras x
  rw [hx] at hp
  have hs : 1 - P.rejectionProbability x = ‖P.accept x‖ ^ 2 := by
    dsimp [Measurement.rejectionProbability]
    nlinarith
  rw [hs, Real.sqrt_sq (norm_nonneg _)]

/-- Physical input/output register for a finite purification. The extra
coordinate is the designated all-zero input, disjoint from output labels. -/
abbrev PurificationSpace (d M : ℕ) := EuclideanSpace ℂ (Unit ⊕ (Fin d × Fin M))

def zeroState (d M : ℕ) : PurificationSpace d M :=
  EuclideanSpace.single (Sum.inl ()) 1

/-- A preparation oracle includes its entire arbitrary unitary action and
actual normalized conditional garbage. The preparation equation constrains
only its action on the designated input. -/
structure PreparationOracle (d M : ℕ) where
  unitary : PurificationSpace d M ≃ₗᵢ[ℂ] PurificationSpace d M
  probability : Fin d → ℝ
  nonnegative : ∀ i, 0 ≤ probability i
  total : ∑ i, probability i = 1
  garbage : Fin d → EuclideanSpace ℂ (Fin M)
  garbage_norm : ∀ i, ‖garbage i‖ = 1
  preparation_bot : unitary (zeroState d M) (Sum.inl ()) = 0
  preparation_output : ∀ i j, unitary (zeroState d M) (Sum.inr (i,j)) =
    (Real.sqrt (probability i) : ℂ) * garbage i j

/-- Measuring the first output register really samples the declared
probability vector. This follows from the actual preparation equation and the
unit norm of each conditional garbage vector. -/
theorem PreparationOracle.output_probability {d M : ℕ} (U : PreparationOracle d M)
    (i : Fin d) :
    (∑ j, ‖U.unitary (zeroState d M) (Sum.inr (i,j))‖ ^ 2) = U.probability i := by
  simp_rw [U.preparation_output, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  rw [← Finset.mul_sum, ← EuclideanSpace.norm_sq_eq, U.garbage_norm, one_pow, mul_one]
  exact Real.sq_sqrt (U.nonnegative i)

/-- Each selected oracle operation has unit query cost. A controlled oracle
is also a genuine unitary, constructed below from its active unitary. -/
inductive Direction where
  | forward
  | inverse
  deriving DecidableEq

def queryUnitary (U : H ≃ₗᵢ[ℂ] H) : Direction → H ≃ₗᵢ[ℂ] H
  | .forward => U
  | .inverse => U.symm

/-- Oracle-independent circuit data. A run with `T` calls applies the initial
unitary `free 0`, then `T` calls, each followed by `free (t+1)`. The oracle
is an argument to `state`, never part of the fixed circuit data. -/
structure Circuit (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  initial : H
  initial_norm : ‖initial‖ = 1
  free : ℕ → H ≃ₗᵢ[ℂ] H
  direction : ℕ → Direction
  measurement : Measurement H

def Circuit.state (C : Circuit H) (U : H ≃ₗᵢ[ℂ] H) : ℕ → H
  | 0 => C.free 0 C.initial
  | t + 1 => C.free (t+1) (queryUnitary U (C.direction t) (C.state U t))

theorem Circuit.state_norm (C : Circuit H) (U : H ≃ₗᵢ[ℂ] H) (t : ℕ) :
    ‖C.state U t‖ = 1 := by
  induction t with
  | zero => simpa [Circuit.state] using C.initial_norm
  | succ t ht => simpa [Circuit.state] using ht

def Circuit.rejectProbability (C : Circuit H) (U : H ≃ₗᵢ[ℂ] H) (T : ℕ) : ℝ :=
  C.measurement.rejectionProbability (C.state U T)

theorem Circuit.rejectProbability_bounds (C : Circuit H) (U : H ≃ₗᵢ[ℂ] H) (T : ℕ) :
    0 ≤ C.rejectProbability U T ∧ C.rejectProbability U T ≤ 1 :=
  C.measurement.probability_bounds _ (C.state_norm U T)

/-- With zero calls, the output statistics are independent of the oracle. -/
theorem Circuit.zero_queries (C : Circuit H) (U V : H ≃ₗᵢ[ℂ] H) :
    C.rejectProbability U 0 = C.rejectProbability V 0 := rfl

/-- A promise tester is quantified over actual preparation unitaries, rather
than a number defined to equal the intended lower bound. -/
def Circuit.Tests {X : Type*} (C : Circuit H) (oracle : X → H ≃ₗᵢ[ℂ] H)
    (null alternative : X → Prop) (error : ℝ) (T : ℕ) : Prop :=
  (∀ x, null x → C.rejectProbability (oracle x) T ≤ error) ∧
  (∀ x, alternative x → 1 - error ≤ C.rejectProbability (oracle x) T)

/-- Distinct promised sides cannot both be tested without querying the
oracle when the error is strictly below one half. -/
theorem Circuit.no_zero_query_test {X : Type*} (C : Circuit H)
    (oracle : X → H ≃ₗᵢ[ℂ] H) (null alternative : X → Prop) {error : ℝ}
    (herror : error < 1/2) {x y : X} (hx : null x) (hy : alternative y) :
    ¬ C.Tests oracle null alternative error 0 := by
  intro h
  have h₀ := h.1 x hx
  have h₁ := h.2 y hy
  rw [C.zero_queries (oracle y) (oracle x)] at h₁
  linarith

section Progress
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The complex adversary progress used by the paper, prior to taking its
real part for the scalar telescoping argument. -/
def progress (Γ : F →L[ℂ] E) (x : E) (y : F) : ℂ := ⟪x, Γ y⟫_ℂ

/-- Oracle-independent isometries leave progress unchanged whenever they
intertwine with the adversary. This is the exact commuting condition satisfied
by `Γ ⊗ I` and arbitrary fixed computation on the physical registers. -/
theorem free_progress (Γ : F →L[ℂ] E) (V₀ : E ≃ₗᵢ[ℂ] E)
    (V₁ : F ≃ₗᵢ[ℂ] F) (hcomm : ∀ y, Γ (V₁ y) = V₀ (Γ y)) (x : E) (y : F) :
    progress Γ (V₀ x) (V₁ y) = progress Γ x y := by
  simp only [progress, hcomm, V₀.inner_map_map]

/-- Exact operator identity behind (4), expressed on vectors. No bound on
progress itself occurs among the hypotheses. -/
theorem query_difference_identity (Γ : F →L[ℂ] E) (U₀ : E ≃ₗᵢ[ℂ] E)
    (U₁ : F ≃ₗᵢ[ℂ] F) (x : E) (y : F) :
    progress Γ (U₀ x) (U₁ y) - progress Γ x y =
      ⟪U₀ x, (Γ.comp (U₁ : F →L[ℂ] F) -
        (U₀ : E →L[ℂ] E).comp Γ) y⟫_ℂ := by
  change ⟪U₀ x, Γ (U₁ y)⟫_ℂ - ⟪x, Γ y⟫_ℂ =
    ⟪U₀ x, Γ (U₁ y) - U₀ (Γ y)⟫_ℂ
  rw [inner_sub_right, U₀.inner_map_map]

/-- A query changes complex progress by at most the operator-norm bound (4),
for any normalized states, any workspace, and any latent Hilbert spaces. -/
theorem query_progress_bound (Γ : F →L[ℂ] E) (U₀ : E ≃ₗᵢ[ℂ] E)
    (U₁ : F ≃ₗᵢ[ℂ] F) (x : E) (y : F) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {B : ℝ} (hB : ‖Γ.comp (U₁ : F →L[ℂ] F) -
      (U₀ : E →L[ℂ] E).comp Γ‖ ≤ B) :
    ‖progress Γ (U₀ x) (U₁ y) - progress Γ x y‖ ≤ B := by
  rw [query_difference_identity]
  calc
    _ ≤ ‖U₀ x‖ * ‖(Γ.comp (U₁ : F →L[ℂ] F) -
        (U₀ : E →L[ℂ] E).comp Γ) y‖ := norm_inner_le_norm _ _
    _ ≤ ‖U₀ x‖ * (‖Γ.comp (U₁ : F →L[ℂ] F) -
        (U₀ : E →L[ℂ] E).comp Γ‖ * ‖y‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ B := by simpa [hx, hy] using hB

/-- The scalar progress in `PUT.Progress` is the real part of the actual
complex inner-product progress, and inherits the same query bound. -/
theorem query_real_progress_bound (Γ : F →L[ℂ] E) (U₀ : E ≃ₗᵢ[ℂ] E)
    (U₁ : F ≃ₗᵢ[ℂ] F) (x : E) (y : F) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {B : ℝ} (hB : ‖Γ.comp (U₁ : F →L[ℂ] F) -
      (U₀ : E →L[ℂ] E).comp Γ‖ ≤ B) :
    |(progress Γ (U₀ x) (U₁ y)).re - (progress Γ x y).re| ≤ B := by
  have h := query_progress_bound Γ U₀ U₁ x y hx hy hB
  exact (Complex.abs_re_le_norm _).trans (by simpa using h)

/-- Output measurement commutation kills the two cross terms in (5). -/
theorem measurement_progress_decomposition (Γ : F →L[ℂ] E)
    (P₀ : Measurement E) (P₁ : Measurement F)
    (hcomm : ∀ y, P₀.reject (Γ y) = Γ (P₁.reject y)) (x : E) (y : F) :
    progress Γ x y = progress Γ (P₀.accept x) (P₁.accept y) +
      progress Γ (P₀.reject x) (P₁.reject y) := by
  have h₀ : ⟪P₀.accept x, Γ (P₁.reject y)⟫_ℂ = 0 := by
    rw [← hcomm]
    exact P₀.orthogonal x (Γ y)
  have h₁ : ⟪P₀.reject x, Γ (P₁.accept y)⟫_ℂ = 0 := by
    rw [P₀.hermitian, hcomm]
    simp [Measurement.accept, map_sub, P₁.idem]
  have hx : x = P₀.accept x + P₀.reject x := by simp [Measurement.accept]
  have hy : y = P₁.accept y + P₁.reject y := by simp [Measurement.accept]
  conv_lhs => rw [hx, hy]
  simp only [progress, map_add, inner_add_left, inner_add_right]
  rw [h₀, h₁]
  simp

/-- Genuine operator/measurement envelope (5): it follows from Born
probabilities and Cauchy--Schwarz, not from an assumed final-progress bound. -/
theorem final_progress_envelope (Γ : F →L[ℂ] E)
    (P₀ : Measurement E) (P₁ : Measurement F)
    (hcomm : ∀ y, P₀.reject (Γ y) = Γ (P₁.reject y))
    (x : E) (y : F) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) {A : ℝ}
    (hΓ : ‖Γ‖ ≤ A) :
    ‖progress Γ x y‖ ≤ A *
      (Real.sqrt ((1 - P₀.rejectionProbability x) * (1 - P₁.rejectionProbability y)) +
        Real.sqrt (P₀.rejectionProbability x * P₁.rejectionProbability y)) := by
  have bound (u : E) (v : F) : ‖progress Γ u v‖ ≤ A * (‖u‖ * ‖v‖) := by
    calc
      _ ≤ ‖u‖ * ‖Γ v‖ := norm_inner_le_norm _ _
      _ ≤ ‖u‖ * (‖Γ‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (Γ.le_opNorm v) (norm_nonneg _)
      _ ≤ A * (‖u‖ * ‖v‖) := by
        nlinarith [mul_le_mul_of_nonneg_right hΓ (mul_nonneg (norm_nonneg u) (norm_nonneg v))]
  have hr₀ := P₀.probability_bounds x hx
  have hr₁ := P₁.probability_bounds y hy
  rw [measurement_progress_decomposition Γ P₀ P₁ hcomm]
  calc
    _ ≤ ‖progress Γ (P₀.accept x) (P₁.accept y)‖ +
      ‖progress Γ (P₀.reject x) (P₁.reject y)‖ := norm_add_le _ _
    _ ≤ A * (‖P₀.accept x‖ * ‖P₁.accept y‖) +
      A * (‖P₀.reject x‖ * ‖P₁.reject y‖) := add_le_add (bound _ _) (bound _ _)
    _ = _ := by
      rw [P₀.accept_norm x hx, P₁.accept_norm y hy, P₀.reject_norm, P₁.reject_norm,
        ← Real.sqrt_mul (sub_nonneg.mpr hr₀.2), ← Real.sqrt_mul hr₀.1]
      ring

end Progress

/-! ## Controlled calls and finite workspaces -/

/-- An arbitrary finite ancilla is represented in an orthonormal basis.
`PiLp 2` gives the Hilbert (not supremum) norm on the resulting tensor product. -/
abbrev Register (ι : Type*) (H : Type*) := PiLp 2 (fun _ : ι => H)

/-- The exact unitary `I_workspace ⊗ U`. -/
def withWorkspace {ι : Type*} [Fintype ι] (U : H ≃ₗᵢ[ℂ] H) :
    Register ι H ≃ₗᵢ[ℂ] Register ι H :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ => U)

/-- The exact block unitary `I ⊕ U`, controlled by a qubit. -/
def controlled (U : H ≃ₗᵢ[ℂ] H) : Register Bool H ≃ₗᵢ[ℂ] Register Bool H :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun b => if b then U else .refl ℂ H)

@[simp] theorem controlled_false (U : H ≃ₗᵢ[ℂ] H) (x : Register Bool H) :
    controlled U x false = x false := by simp [controlled]

@[simp] theorem controlled_true (U : H ≃ₗᵢ[ℂ] H) (x : Register Bool H) :
    controlled U x true = U (x true) := by simp [controlled]

theorem controlled_inverse (U : H ≃ₗᵢ[ℂ] H) :
    (controlled U).symm = controlled U.symm := by
  ext x b
  cases b <;> rfl

/-- For the paper's Hermitian unitaries, inverse calls are literally the same
operation, including controlled calls. -/
theorem queryUnitary_of_involutive (U : H ≃ₗᵢ[ℂ] H)
    (hU : ∀ x, U (U x) = x) (q : Direction) : queryUnitary U q = U := by
  cases q with
  | forward => rfl
  | inverse =>
    ext x
    apply U.injective
    simp [queryUnitary, hU]

theorem controlled_involutive (U : H ≃ₗᵢ[ℂ] H) (hU : ∀ x, U (U x) = x)
    (x : Register Bool H) : controlled U (controlled U x) = x := by
  ext b
  cases b <;> simp [hU]

section WorkspaceNorm
variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- A diagonal family of actual continuous operators on a finite Hilbert
sum. The following lemma is the finite-workspace norm argument, with the
correct `ℓ²` norm. -/
def blockLinear (G : ι → F →L[ℂ] E) : Register ι F →ₗ[ℂ] Register ι E where
  toFun x := WithLp.toLp 2 (fun i => G i (x i))
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

theorem blockLinear_bound (G : ι → F →L[ℂ] E) {B : ℝ}
    (hB : 0 ≤ B) (hG : ∀ i, ‖G i‖ ≤ B) (x : Register ι F) :
    ‖blockLinear G x‖ ≤ B * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  change ‖G i (x i)‖ ^ 2 ≤ B ^ 2 * ‖x i‖ ^ 2
  have h : ‖G i (x i)‖ ≤ B * ‖x i‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hG i) (norm_nonneg _))
  simpa [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2

def blockOperator (G : ι → F →L[ℂ] E) {B : ℝ} (hB : 0 ≤ B)
    (hG : ∀ i, ‖G i‖ ≤ B) : Register ι F →L[ℂ] Register ι E :=
  (blockLinear G).mkContinuous B (blockLinear_bound G hB hG)

@[simp] theorem blockOperator_apply (G : ι → F →L[ℂ] E) {B : ℝ} (hB : 0 ≤ B)
    (hG : ∀ i, ‖G i‖ ≤ B) (x : Register ι F) (i : ι) :
    blockOperator G hB hG x i = G i (x i) := rfl

theorem blockOperator_norm (G : ι → F →L[ℂ] E) {B : ℝ} (hB : 0 ≤ B)
    (hG : ∀ i, ‖G i‖ ≤ B) : ‖blockOperator G hB hG‖ ≤ B :=
  (blockOperator G hB hG).opNorm_le_bound hB (blockLinear_bound G hB hG)

/-- `Γ ⊗ I` in a finite ancillary basis. -/
def workspaceOperator (Γ : F →L[ℂ] E) : Register ι F →L[ℂ] Register ι E :=
  blockOperator (fun _ => Γ) (norm_nonneg Γ) (fun _ => le_rfl)

@[simp] theorem workspaceOperator_apply (Γ : F →L[ℂ] E) (x : Register ι F) (i : ι) :
    workspaceOperator Γ x i = Γ (x i) := rfl

theorem workspaceOperator_norm (Γ : F →L[ℂ] E) :
    ‖(workspaceOperator Γ : Register ι F →L[ℂ] Register ι E)‖ ≤ ‖Γ‖ :=
  blockOperator_norm _ _ _

/-- Tensoring the query difference with arbitrary finite workspace preserves
the bound; the equality is of actual operators on the workspace Hilbert sum. -/
theorem workspace_query_bound (Γ : F →L[ℂ] E) (U₀ : E ≃ₗᵢ[ℂ] E)
    (U₁ : F ≃ₗᵢ[ℂ] F) {B : ℝ}
    (hB : ‖Γ.comp (U₁ : F →L[ℂ] F) - (U₀ : E →L[ℂ] E).comp Γ‖ ≤ B) :
    ‖(workspaceOperator Γ : Register ι F →L[ℂ] Register ι E).comp
      (withWorkspace (ι := ι) U₁ : Register ι F →L[ℂ] Register ι F) -
      (withWorkspace (ι := ι) U₀ : Register ι E →L[ℂ] Register ι E).comp
        (workspaceOperator Γ)‖ ≤ B := by
  let D := Γ.comp (U₁ : F →L[ℂ] F) - (U₀ : E →L[ℂ] E).comp Γ
  have heq : (workspaceOperator Γ : Register ι F →L[ℂ] Register ι E).comp
      (withWorkspace (ι := ι) U₁ : Register ι F →L[ℂ] Register ι F) -
      (withWorkspace (ι := ι) U₀ : Register ι E →L[ℂ] Register ι E).comp
        (workspaceOperator Γ) = workspaceOperator D := by
    ext x i
    rfl
  rw [heq]
  exact (workspaceOperator_norm D).trans hB

/-- For a controlled call the inactive block has zero query difference and
the active block is the original query difference, precisely as in §2. -/
theorem controlled_query_bound (Γ : F →L[ℂ] E) (U₀ : E ≃ₗᵢ[ℂ] E)
    (U₁ : F ≃ₗᵢ[ℂ] F) {B : ℝ}
    (hB : ‖Γ.comp (U₁ : F →L[ℂ] F) - (U₀ : E →L[ℂ] E).comp Γ‖ ≤ B) :
    ‖(workspaceOperator Γ : Register Bool F →L[ℂ] Register Bool E).comp
      (controlled U₁ : Register Bool F →L[ℂ] Register Bool F) -
      (controlled U₀ : Register Bool E →L[ℂ] Register Bool E).comp
        (workspaceOperator Γ)‖ ≤ B := by
  let D := Γ.comp (U₁ : F →L[ℂ] F) - (U₀ : E →L[ℂ] E).comp Γ
  have hB0 : 0 ≤ B := (norm_nonneg D).trans hB
  let G : Bool → F →L[ℂ] E := fun b => if b then D else 0
  have hG : ∀ b, ‖G b‖ ≤ B := by
    intro b
    cases b
    · simpa [G] using hB0
    · simpa [G, D] using hB
  have heq : (workspaceOperator Γ : Register Bool F →L[ℂ] Register Bool E).comp
      (controlled U₁ : Register Bool F →L[ℂ] Register Bool F) -
      (controlled U₀ : Register Bool E →L[ℂ] Register Bool E).comp
        (workspaceOperator Γ) = blockOperator G hB0 hG := by
    ext x b
    cases b <;> simp [controlled, G, D, ContinuousLinearMap.comp_apply]
  rw [heq]
  exact blockOperator_norm G hB0 hG

end WorkspaceNorm

/-! ## Actual joint evolutions under two priors -/

/-- A pure-state evolution on a joint latent/physical Hilbert space. Query
and free gates are genuine unitary operators. This type imposes no progress
inequality and no numerical lower bound. -/
structure Evolution (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  initial : H
  initial_norm : ‖initial‖ = 1
  query : ℕ → H ≃ₗᵢ[ℂ] H
  free : ℕ → H ≃ₗᵢ[ℂ] H

def Evolution.state (C : Evolution H) : ℕ → H
  | 0 => C.initial
  | t + 1 => C.free t (C.query t (C.state t))

theorem Evolution.state_norm (C : Evolution H) (t : ℕ) : ‖C.state t‖ = 1 := by
  induction t with
  | zero => exact C.initial_norm
  | succ t ht => simpa [Evolution.state] using ht

/-- Every actual oracle circuit is a unitary evolution; this equality links
the generic progress lemmas to the circuit's recursive semantics. -/
def Circuit.evolution (C : Circuit H) (U : H ≃ₗᵢ[ℂ] H) : Evolution H where
  initial := C.free 0 C.initial
  initial_norm := by simpa using C.initial_norm
  query t := queryUnitary U (C.direction t)
  free t := C.free (t+1)

theorem Circuit.evolution_state (C : Circuit H) (U : H ≃ₗᵢ[ℂ] H) (t : ℕ) :
    (C.evolution U).state t = C.state U t := by
  induction t with
  | zero => rfl
  | succ t ht =>
    change C.free (t+1) (queryUnitary U (C.direction t) ((C.evolution U).state t)) =
      C.free (t+1) (queryUnitary U (C.direction t) (C.state U t))
    rw [ht]

section JointRun
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The actual scalar progress trajectory of two joint unitary runs. -/
def runProgress (Γ : F →L[ℂ] E) (C₀ : Evolution E) (C₁ : Evolution F) (t : ℕ) : ℝ :=
  (progress Γ (C₀.state t) (C₁.state t)).re

/-- Operational form of (4): the gate commutation condition and operator
query-difference bound imply a step bound for the actual recursive run. -/
theorem runProgress_step (Γ : F →L[ℂ] E) (C₀ : Evolution E) (C₁ : Evolution F)
    (hfree : ∀ t y, Γ (C₁.free t y) = C₀.free t (Γ y)) {B : ℝ}
    (hquery : ∀ t, ‖Γ.comp (C₁.query t : F →L[ℂ] F) -
      (C₀.query t : E →L[ℂ] E).comp Γ‖ ≤ B) (t : ℕ) :
    |runProgress Γ C₀ C₁ (t+1) - runProgress Γ C₀ C₁ t| ≤ B := by
  simp only [runProgress, Evolution.state]
  rw [free_progress Γ (C₀.free t) (C₁.free t) (hfree t)]
  exact query_real_progress_bound Γ (C₀.query t) (C₁.query t) _ _
    (C₀.state_norm t) (C₁.state_norm t) (hquery t)

/-- The output envelope for the actual joint run, using actual Born
probabilities of its final states. -/
theorem runProgress_final (Γ : F →L[ℂ] E) (C₀ : Evolution E) (C₁ : Evolution F)
    (P₀ : Measurement E) (P₁ : Measurement F)
    (hcomm : ∀ y, P₀.reject (Γ y) = Γ (P₁.reject y)) {A : ℝ}
    (hΓ : ‖Γ‖ ≤ A) (T : ℕ) :
    |runProgress Γ C₀ C₁ T| ≤ A *
      (Real.sqrt ((1 - P₀.rejectionProbability (C₀.state T)) *
        (1 - P₁.rejectionProbability (C₁.state T))) +
      Real.sqrt (P₀.rejectionProbability (C₀.state T) *
        P₁.rejectionProbability (C₁.state T))) := by
  exact (Complex.abs_re_le_norm _).trans
    (final_progress_envelope Γ P₀ P₁ hcomm _ _ (C₀.state_norm T) (C₁.state_norm T) hΓ)

end JointRun

end PUT.QueryModel

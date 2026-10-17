import P31.Schatten
import P31.UpperBound

/-!
# Actual adaptive Schatten gradient-query upper bound

The spectral input is pinned to genuine rectangular singular values. The
only algorithmic literature input is the norm-agnostic complementary-composite
objective theorem [6, Theorem 2; arXiv:2101.11041v2, Theorem 2.1], with
q_src=p, lambda=mu, psi=H, phi=Omega_center, eta=mu*delta^p/p.
The spectral normalization factors are absorbed into C(p,kappa). The external
constructor knows H, its center, the scales, and its exact matrix prox; it
never receives f, its gradient, or a minimizer. All outer-stage reasoning,
terminal accuracy, and actual executed query accounting are proved below.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
namespace P31.Schatten
open QueryProgram Schedule

/-- The exact matrix version of (5.7), on actual rectangular matrices. -/
def IsMatrixCompositeProx {m n : ℕ} (S : SpectralInput m n) (p : ℝ)
    (H : Mat m n → ℝ) (center : Mat m n) (prox : CompositeProx (Mat m n)) : Prop :=
  ∀ G A ξ, 0 < A → 0 < ξ → ∀ Y,
    tracePair G (prox G A ξ) + A * H (prox G A ξ) + ξ * S.atom p center (prox G A ξ) ≤
      tracePair G Y + A * H Y + ξ * S.atom p center Y

/-- Explicit objective-only specialization of the same external source used
for vectors. Its source constant is fixed before any unknown objective. -/
structure ExternalMatrixComposite {m n : ℕ} (S : SpectralInput m n) (p κ C : ℝ) where
  routine : (Mat m n → ℝ) → Mat m n → ℝ → ℝ → ℝ → ℝ →
    CompositeProx (Mat m n) → Program (Mat m n) (Mat m n) (Mat m n)
  calls_le : ∀ H c L μ D δ prox oracle,
    0 < L → 0 < μ → 0 < D → 0 < δ → δ ≤ D →
    ((routine H c L μ D δ prox).run oracle).calls ≤ compositeQueryBudget C p κ L μ D δ
  objective_gap : ∀ H c L μ D δ prox,
    0 < L → 0 < μ → 0 < D → 0 < δ → δ ≤ D →
    S.Jensen p μ H → IsMatrixCompositeProx S p H c prox →
    ∀ (f : Mat m n → ℝ) (grad : Mat m n → Mat m n) (zstar : Mat m n),
    ConvexOn ℝ Set.univ f →
    (∀ X, HasFDerivAt f (traceFunctional (grad X)) X) →
    (∀ X Y, S.snorm (dualExponent p) (grad X-grad Y) ≤ L * S.snorm p (X-Y)^(κ-1)) →
    (∀ Y, f zstar + H zstar ≤ f Y + H Y) → S.snorm p (c-zstar) ≤ D →
    let z := ((routine H c L μ D δ prox).run grad).value
    f z + H z - (f zstar + H zstar) ≤ μ / p * δ ^ p

/-- One source constant valid simultaneously for all positive rectangular
sizes and all genuine spectral realizations. -/
abbrev ExternalMatrixCompositeFamily (p κ C : ℝ) :=
  ∀ m n : ℕ, 0 < m → 0 < n → ∀ S : SpectralInput m n, ExternalMatrixComposite S p κ C

def matrixBiasCoefficient (p : ℝ) : ℝ := SpectralInput.atomScale p * (3 : ℝ)^(p-1)

lemma matrixBiasCoefficient_pos (p : ℝ) : 0 < matrixBiasCoefficient p :=
  mul_pos (SpectralInput.atomScale_pos p) (Real.rpow_pos_of_pos (by norm_num) _)

/-- The complete known matrix data; f and its gradient are absent. -/
structure MatrixAccumulationData (m n : ℕ) where
  spectral : SpectralInput m n
  p : ℝ
  κ : ℝ
  L : ℝ
  R : ℝ
  ε : ℝ
  initial : Mat m n
  hp : 2 ≤ p
  hκ : 1 < κ
  hκhi : κ ≤ 2
  hL : 0 < L
  hR : 0 < R
  hε : 0 < ε

namespace MatrixAccumulationData
variable {m n : ℕ}

def firstWeight (a : MatrixAccumulationData m n) : ℝ :=
  initialWeight (matrixBiasCoefficient a.p * a.R^(a.p-1)) (theta a.p) (ratio a.κ) a.ε

def increment (a : MatrixAccumulationData m n) (s : ℕ) : ℝ := alpha a.firstWeight (tau a.p a.κ) s
def weight (a : MatrixAccumulationData m n) (k : ℕ) : ℝ := a.increment (k+1)
def modulus (a : MatrixAccumulationData m n) (s : ℕ) : ℝ := sigma a.firstWeight (tau a.p a.κ) s

def regularizer (a : MatrixAccumulationData m n) (hist : ℕ → Mat m n) (s : ℕ) (X : Mat m n) : ℝ :=
  ∑ k ∈ Finset.range s, a.weight k * a.spectral.atom a.p (hist k) X

lemma firstWeight_pos (a : MatrixAccumulationData m n) : 0 < a.firstWeight :=
  initialWeight_pos (mul_pos (matrixBiasCoefficient_pos a.p) (Real.rpow_pos_of_pos a.hR _))
    (theta_lt_one a.hp) (ratio_lt_one a.hκ) a.hε

lemma increment_pos (a : MatrixAccumulationData m n) {s : ℕ} (hs : 0 < s) : 0 < a.increment s :=
  alpha_pos a.firstWeight_pos (tau_gt_one a.hp a.hκhi) hs

lemma weight_pos (a : MatrixAccumulationData m n) (k : ℕ) : 0 < a.weight k := a.increment_pos (by omega)

lemma modulus_pos (a : MatrixAccumulationData m n) (s : ℕ) : 0 < a.modulus (s+1) :=
  mul_pos a.firstWeight_pos (pow_pos (lt_trans zero_lt_one (tau_gt_one a.hp a.hκhi)) s)

lemma sum_weight (a : MatrixAccumulationData m n) (s : ℕ) :
    ∑ k ∈ Finset.range s, a.weight k = a.modulus s := sum_alpha _ _ _

lemma modulus_eq (a : MatrixAccumulationData m n) (s : ℕ) :
    SpectralInput.modulus a.increment s = a.modulus s := a.sum_weight s

@[simp] lemma regularizer_zero (a : MatrixAccumulationData m n) (hist : ℕ → Mat m n) (X : Mat m n) :
    a.regularizer hist 0 X = 0 := by simp [regularizer]

lemma regularizer_congr (a : MatrixAccumulationData m n) {hist hist' : ℕ → Mat m n} (s : ℕ)
    (h : ∀ k, k < s → hist k = hist' k) : a.regularizer hist s = a.regularizer hist' s := by
  funext X
  apply Finset.sum_congr rfl
  intro k hk
  rw [h k (Finset.mem_range.mp hk)]

lemma regularizer_jensen (a : MatrixAccumulationData m n) (hist : ℕ → Mat m n) (s : ℕ) :
    a.spectral.Jensen a.p (a.modulus s) (a.regularizer hist s) := by
  rw [← a.sum_weight s]
  simpa only [mul_one] using a.spectral.jensen_weighted_sum (Finset.range s) a.p
    (fun k => a.spectral.atom a.p (hist k)) (fun _ => 1) a.weight
    (fun k _ => (a.weight_pos k).le) (fun k _ => a.spectral.atom_jensen a.hp (hist k))

/-- The proved single-valued multicenter spectral map is uncharged internal work. -/
def prox (a : MatrixAccumulationData m n) (hist : ℕ → Mat m n) (s : ℕ) : CompositeProx (Mat m n) :=
  a.spectral.compositeProx a.hp (Finset.range s) a.weight hist
    (fun k _ => (a.weight_pos k).le) (hist (s-1))

lemma prox_valid (a : MatrixAccumulationData m n) (hist : ℕ → Mat m n) (s : ℕ) :
    IsMatrixCompositeProx a.spectral a.p (a.regularizer hist s) (hist (s-1)) (a.prox hist s) := by
  intro G A ξ hA hξ Y
  exact a.spectral.compositeProx_minimizes a.hp (Finset.range s) a.weight hist
    (fun k _ => (a.weight_pos k).le) (hist (s-1)) G A ξ hA.le hξ Y

def stage {C : ℝ} (a : MatrixAccumulationData m n)
    (engine : ExternalMatrixComposite a.spectral a.p a.κ C) (hist : ℕ → Mat m n) (s : ℕ) :
    Program (Mat m n) (Mat m n) (Mat m n) :=
  engine.routine (a.regularizer hist (s+1)) (hist s) a.L (a.modulus (s+1))
    (radius a.R s) (radius a.R (s+1)) (a.prox hist (s+1))

/-- Every subsequent stage sees only the history generated by prior replies. -/
def historyProgram {C : ℝ} (a : MatrixAccumulationData m n)
    (engine : ExternalMatrixComposite a.spectral a.p a.κ C) : ℕ →
      Program (Mat m n) (Mat m n) (ℕ → Mat m n)
  | 0 => .pure (fun _ => a.initial)
  | s+1 => (a.historyProgram engine s).bind (fun hist =>
      (a.stage engine hist s).map (fun Z => Function.update hist (s+1) Z))

def realizedHistory {C : ℝ} (a : MatrixAccumulationData m n)
    (engine : ExternalMatrixComposite a.spectral a.p a.κ C) (oracle : Mat m n → Mat m n)
    (s : ℕ) : ℕ → Mat m n := ((a.historyProgram engine s).run oracle).value

def iterates {C : ℝ} (a : MatrixAccumulationData m n)
    (engine : ExternalMatrixComposite a.spectral a.p a.κ C) (oracle : Mat m n → Mat m n)
    (s : ℕ) : Mat m n := a.realizedHistory engine oracle s s

lemma realizedHistory_succ {C : ℝ} (a : MatrixAccumulationData m n)
    (engine : ExternalMatrixComposite a.spectral a.p a.κ C) (oracle : Mat m n → Mat m n) (s : ℕ) :
    a.realizedHistory engine oracle (s+1) = Function.update (a.realizedHistory engine oracle s)
      (s+1) (((a.stage engine (a.realizedHistory engine oracle s) s).run oracle).value) := by
  simp [realizedHistory, historyProgram, Program.map]

lemma history_prefix {C : ℝ} (a : MatrixAccumulationData m n)
    (engine : ExternalMatrixComposite a.spectral a.p a.κ C) (oracle : Mat m n → Mat m n)
    (s k : ℕ) (hk : k ≤ s) : a.realizedHistory engine oracle s k = a.iterates engine oracle k := by
  induction s with
  | zero =>
    have hkzero : k = 0 := by omega
    subst k
    rfl
  | succ s ih =>
    by_cases he : k = s+1
    · subst k; rfl
    · rw [realizedHistory_succ, Function.update_of_ne he]
      exact ih (by omega)

@[simp] lemma iterates_zero {C : ℝ} (a : MatrixAccumulationData m n)
    (engine : ExternalMatrixComposite a.spectral a.p a.κ C) (oracle : Mat m n → Mat m n) :
    a.iterates engine oracle 0 = a.initial := rfl

lemma iterates_succ {C : ℝ} (a : MatrixAccumulationData m n)
    (engine : ExternalMatrixComposite a.spectral a.p a.κ C) (oracle : Mat m n → Mat m n) (s : ℕ) :
    a.iterates engine oracle (s+1) =
      ((a.stage engine (a.realizedHistory engine oracle s) s).run oracle).value := by
  simp [iterates, realizedHistory_succ]

lemma realized_regularizer {C : ℝ} (a : MatrixAccumulationData m n)
    (engine : ExternalMatrixComposite a.spectral a.p a.κ C) (oracle : Mat m n → Mat m n) (s : ℕ) :
    a.regularizer (a.realizedHistory engine oracle s) (s+1) =
      a.regularizer (a.iterates engine oracle) (s+1) :=
  a.regularizer_congr (s+1) (fun k hk => a.history_prefix engine oracle s k (by omega))

/-- Existence is derived for every actual accumulated objective in the run;
the analytical minimizers are absent from the algorithm constructor. -/
theorem exists_exactMinima {C : ℝ} (a : MatrixAccumulationData m n)
    (engine : ExternalMatrixComposite a.spectral a.p a.κ C)
    (f : Mat m n → ℝ) (grad : Mat m n → Mat m n)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ X, HasFDerivAt f (traceFunctional (grad X)) X)
    (xstar : Mat m n) (hstar : ∀ Y, f xstar ≤ f Y) :
    ∃ z : ℕ → Mat m n, z 0 = xstar ∧ ∀ s Y,
      f (z s) + a.regularizer (a.iterates engine grad) s (z s) ≤
        f Y + a.regularizer (a.iterates engine grad) s Y := by
  have hcont : Continuous f := (show Differentiable ℝ f from fun X => (hg X).differentiableAt).continuous
  have hex (s : ℕ) : ∃ Z, ∀ Y,
      f Z + a.regularizer (a.iterates engine grad) (s+1) Z ≤
        f Y + a.regularizer (a.iterates engine grad) (s+1) Y := by
    simpa only [regularizer, weight, SpectralInput.objective] using
      (a.spectral.objective_existsUnique a.hp f hcont hf xstar hstar a.increment
        (a.iterates engine grad) (s+1) (by omega)
        (fun k hk _ => a.increment_pos (by omega))).exists
  choose z hz using hex
  refine ⟨fun s => match s with | 0 => xstar | k+1 => z k, rfl, ?_⟩
  intro s Y
  cases s with
  | zero => simpa using hstar Y
  | succ s => exact hz s Y

/-- The only gap used by the outer induction is now obtained from an actual
stage execution after its warm-start radius is known. -/
theorem generated_objective_gap {C : ℝ} (a : MatrixAccumulationData m n)
    (engine : ExternalMatrixComposite a.spectral a.p a.κ C)
    (f : Mat m n → ℝ) (grad : Mat m n → Mat m n)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ X, HasFDerivAt f (traceFunctional (grad X)) X)
    (hh : ∀ X Y, a.spectral.snorm (dualExponent a.p) (grad X-grad Y) ≤
      a.L * a.spectral.snorm a.p (X-Y)^(a.κ-1))
    (z : ℕ → Mat m n)
    (hmin : ∀ s Y, f (z s) + a.regularizer (a.iterates engine grad) s (z s) ≤
      f Y + a.regularizer (a.iterates engine grad) s Y)
    (s : ℕ) (hwarm : a.spectral.snorm a.p (z (s+1)-a.iterates engine grad s) ≤ radius a.R s) :
    (f (a.iterates engine grad (s+1)) +
      a.regularizer (a.iterates engine grad) (s+1) (a.iterates engine grad (s+1))) -
      (f (z (s+1)) + a.regularizer (a.iterates engine grad) (s+1) (z (s+1))) ≤
      a.modulus (s+1) / a.p * radius a.R (s+1)^a.p := by
  rw [← a.realized_regularizer engine grad s, a.iterates_succ engine grad s]
  apply engine.objective_gap _ _ _ _ _ _ _ a.hL (a.modulus_pos s)
    (radius_pos a.hR s) (radius_pos a.hR (s+1))
    (by rw [radius_succ]; linarith [radius_pos a.hR s])
    (a.regularizer_jensen _ _)
    (by simpa using a.prox_valid (a.realizedHistory engine grad s) (s+1)) f grad (z (s+1)) hf hg hh
  · rw [a.realized_regularizer engine grad s]
    exact hmin (s+1)
  · change a.spectral.snorm a.p (a.iterates engine grad s-z (s+1)) ≤ radius a.R s
    rw [a.spectral.snorm_sub_rev (by linarith [a.hp])]
    exact hwarm

lemma biasBudget (a : MatrixAccumulationData m n) (N : ℕ) :
    SpectralInput.atomScale a.p * ∑ k ∈ Finset.range N,
      a.weight k * (3 * radius a.R k)^(a.p-1) ≤ a.ε/2 := by
  let A := matrixBiasCoefficient a.p * a.R^(a.p-1)
  have hA : 0 < A := mul_pos (matrixBiasCoefficient_pos a.p) (Real.rpow_pos_of_pos a.hR _)
  calc
    _ = A * ∑ k ∈ Finset.range N, a.weight k * theta a.p ^ k := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (radius_pos a.hR k).le,
        P31.radius_power_history a.hR.le]
      dsimp [A, matrixBiasCoefficient]
      ring
    _ ≤ a.ε/2 := calibrated_history_bound a.hp a.hκ a.hκhi hA a.hε N

lemma stage_budget_eq {C : ℝ} (a : MatrixAccumulationData m n) (n : ℕ) :
    compositeQueryBudget C a.p a.κ a.L (a.modulus (n+1)) (radius a.R n) (radius a.R (n+1)) =
      queryBudget C (matrixBiasCoefficient a.p) a.L a.R a.p a.κ a.ε n := by
  have hr : radius a.R n / radius a.R (n+1) = 2 := by
    rw [radius_succ]
    field_simp [(radius_pos a.hR n).ne']
  unfold compositeQueryBudget queryBudget stageScale modulus firstWeight
  rw [hr]
  congr 1
  ring

lemma stage_calls_le {C : ℝ} (a : MatrixAccumulationData m n)
    (engine : ExternalMatrixComposite a.spectral a.p a.κ C) (hist : ℕ → Mat m n)
    (oracle : Mat m n → Mat m n) (n : ℕ) :
    ((a.stage engine hist n).run oracle).calls ≤
      queryBudget C (matrixBiasCoefficient a.p) a.L a.R a.p a.κ a.ε n := by
  rw [← a.stage_budget_eq n]
  exact engine.calls_le _ _ _ _ _ _ _ _ a.hL (a.modulus_pos n)
    (radius_pos a.hR n) (radius_pos a.hR (n+1))
    (by rw [radius_succ]; linarith [radius_pos a.hR n])

/-- Calls count the actual adaptive execution, not merely a preselected list
of stage certificates or supplied per-stage query counts. -/
theorem historyProgram_calls_le {C : ℝ} (a : MatrixAccumulationData m n)
    (engine : ExternalMatrixComposite a.spectral a.p a.κ C) (oracle : Mat m n → Mat m n) (n : ℕ) :
    ((a.historyProgram engine n).run oracle).calls ≤
      ∑ k ∈ Finset.range n, queryBudget C (matrixBiasCoefficient a.p) a.L a.R a.p a.κ a.ε k := by
  induction n with
  | zero => simp [historyProgram]
  | succ n ih =>
    simp only [historyProgram, Program.calls_bind, Program.map, Program.run_pure, Nat.add_zero]
    rw [Finset.sum_range_succ]
    exact Nat.add_le_add ih (a.stage_calls_le engine _ oracle n)

/-- The actual finite adaptive output program in the nontrivial regime. -/
def outputProgram {C : ℝ} (a : MatrixAccumulationData m n)
    (engine : ExternalMatrixComposite a.spectral a.p a.κ C) : Program (Mat m n) (Mat m n) (Mat m n) :=
  (a.historyProgram engine (stageCount a.L a.R a.κ a.ε)).map
    (fun hist => hist (stageCount a.L a.R a.κ a.ε))

lemma stageCount_ge_one (a : MatrixAccumulationData m n) (hsmall : a.ε < a.L*a.R^(a.κ-1)) :
    1 ≤ stageCount a.L a.R a.κ a.ε := by
  have hq : 1 < 2*a.L*a.R^(a.κ-1)/a.ε := (lt_div_iff₀ a.hε).mpr (by nlinarith [a.hε])
  have hp : 0 < Real.logb 2 (2*a.L*a.R^(a.κ-1)/a.ε)/(a.κ-1) :=
    div_pos (Real.logb_pos (by norm_num) hq) (sub_pos.mpr a.hκ)
  exact Nat.ceil_pos.mpr hp

/-- Corollary 1.4 in the active regime for the actual adaptive matrix program.
All true minima and valid warm starts are derived internally. -/
theorem outputProgram_accuracy_and_complexity {C : ℝ} (a : MatrixAccumulationData m n)
    (hC : 0 ≤ C) (engine : ExternalMatrixComposite a.spectral a.p a.κ C)
    (hsmall : a.ε < a.L*a.R^(a.κ-1))
    (f : Mat m n → ℝ) (grad : Mat m n → Mat m n)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ X, HasFDerivAt f (traceFunctional (grad X)) X)
    (hh : ∀ X Y, a.spectral.snorm (dualExponent a.p) (grad X-grad Y) ≤
      a.L * a.spectral.snorm a.p (X-Y)^(a.κ-1))
    (xstar : Mat m n) (hstar : ∀ Y, f xstar ≤ f Y)
    (hr : a.spectral.snorm a.p (a.initial-xstar) ≤ a.R) :
    a.spectral.snorm (dualExponent a.p) (grad ((a.outputProgram engine).run grad).value) ≤ a.ε ∧
    (((a.outputProgram engine).run grad).calls : ℝ) ≤
      queryConstant C (matrixBiasCoefficient a.p) a.p a.κ *
        (a.L*a.R^(a.κ-1)/a.ε)^beta a.p a.κ := by
  obtain ⟨z, hzero, hmin⟩ := a.exists_exactMinima engine f grad hf hg xstar hstar
  constructor
  · have hInitial : a.spectral.snorm a.p (a.iterates engine grad 0-z 0) ≤ a.R := by
      simpa [hzero] using hr
    have hGap : ∀ s, 1 ≤ s → s ≤ stageCount a.L a.R a.κ a.ε →
        a.spectral.snorm a.p (z s-a.iterates engine grad (s-1)) ≤ a.R / 2^(s-1) →
        a.spectral.objective a.p f a.increment (a.iterates engine grad) s (a.iterates engine grad s) -
          a.spectral.objective a.p f a.increment (a.iterates engine grad) s (z s) ≤
          SpectralInput.modulus a.increment s / a.p * (a.R / 2^s)^a.p := by
      intro s hs _ hwarm
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
      have hg' := a.generated_objective_gap engine f grad hf hg hh z hmin k (by simpa [radius] using hwarm)
      simpa only [SpectralInput.objective, regularizer, weight, radius, a.modulus_eq] using hg'
    have ha := a.spectral.outer_accuracy a.hp f grad a.increment (a.iterates engine grad) z
      (stageCount a.L a.R a.κ a.ε) (a.stageCount_ge_one hsmall) a.hR.le a.hL.le
      (sub_pos.mpr a.hκ).le hf hg hh (fun s hs _ => a.increment_pos (by omega)) hInitial
      (fun s _ => hmin s) hGap
      (by simpa only [weight, radius] using a.biasBudget (stageCount a.L a.R a.κ a.ε))
      (terminal_radius_bound a.hL a.hR a.hκ a.hε)
    simpa [outputProgram, Program.map, iterates, realizedHistory] using ha
  · have hc : (((a.outputProgram engine).run grad).calls : ℝ) ≤
        ∑ k ∈ Finset.range (stageCount a.L a.R a.κ a.ε),
          (queryBudget C (matrixBiasCoefficient a.p) a.L a.R a.p a.κ a.ε k : ℝ) := by
      have hnat := a.historyProgram_calls_le engine grad (stageCount a.L a.R a.κ a.ε)
      simpa only [outputProgram, Program.map, Program.calls_bind, Program.run_pure,
        Nat.add_zero, Nat.cast_sum] using (show
        (((a.historyProgram engine (stageCount a.L a.R a.κ a.ε)).run grad).calls : ℝ) ≤
          ((∑ k ∈ Finset.range (stageCount a.L a.R a.κ a.ε),
            queryBudget C (matrixBiasCoefficient a.p) a.L a.R a.p a.κ a.ε k : ℕ) : ℝ) from
        Nat.cast_le.mpr hnat)
    exact hc.trans (total_query_budget_le hC (matrixBiasCoefficient_pos a.p)
      a.hL a.hR a.hp a.hκ a.hκhi a.hε hsmall.le)

end MatrixAccumulationData

variable {m n : ℕ}

/-- The matrix method for every accuracy; the branch test and all internal
maps depend only on known inputs and the observed gradient transcript. -/
def matrixGradientMethod {C : ℝ} (S : SpectralInput m n) (p κ L R ε : ℝ) (initial : Mat m n)
    (hp : 2 ≤ p) (hκ : 1 < κ) (hκhi : κ ≤ 2) (engine : ExternalMatrixComposite S p κ C) :
    Program (Mat m n) (Mat m n) (Mat m n) :=
  if h : 0 < L ∧ 0 < R ∧ 0 < ε ∧ ε < L*R^(κ-1) then
    let a : MatrixAccumulationData m n :=
      ⟨S, p, κ, L, R, ε, initial, hp, hκ, hκhi, h.1, h.2.1, h.2.2.1⟩
    a.outputProgram engine
  else .pure initial

theorem matrixGradientMethod_zero {C : ℝ} (S : SpectralInput m n) (p κ L R ε : ℝ)
    (initial : Mat m n) (hp : 2 ≤ p) (hκ : 1 < κ) (hκhi : κ ≤ 2)
    (engine : ExternalMatrixComposite S p κ C) (oracle : Mat m n → Mat m n)
    (heasy : L*R^(κ-1) ≤ ε) :
    ((matrixGradientMethod S p κ L R ε initial hp hκ hκhi engine).run oracle).value = initial ∧
    ((matrixGradientMethod S p κ L R ε initial hp hκ hκhi engine).run oracle).calls = 0 := by
  have hn : ¬ (0 < L ∧ 0 < R ∧ 0 < ε ∧ ε < L*R^(κ-1)) :=
    fun h => (not_lt_of_ge heasy) h.2.2.2
  simp [matrixGradientMethod, dif_neg hn]

lemma matrix_gradient_zero_at_minimizer (f : Mat m n → ℝ) (grad : Mat m n → Mat m n)
    (Z : Mat m n) (hg : HasFDerivAt f (traceFunctional (grad Z)) Z)
    (hz : ∀ Y, f Z ≤ f Y) : grad Z = 0 := by
  have hm : IsLocalMin f Z := Filter.Eventually.of_forall hz
  have hcf := hm.hasFDerivAt_eq_zero hg
  apply SpectralInput.traceFunctional_injective
  rw [hcf]
  ext X
  simp [tracePair]

/-- Corollary 1.4 for every positive accuracy, including all degenerate and
zero-query cases, on the actual singular-value Schatten norms. -/
theorem matrixGradientMethod_guarantee {p κ C L R ε : ℝ}
    (S : SpectralInput m n) (hp : 2 ≤ p) (hκ : 1 < κ) (hκhi : κ ≤ 2) (hC : 0 ≤ C)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hε : 0 < ε) (engine : ExternalMatrixComposite S p κ C)
    (initial : Mat m n) (f : Mat m n → ℝ) (grad : Mat m n → Mat m n)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ X, HasFDerivAt f (traceFunctional (grad X)) X)
    (hh : ∀ X Y, S.snorm (dualExponent p) (grad X-grad Y) ≤ L * S.snorm p (X-Y)^(κ-1))
    (xstar : Mat m n) (hstar : ∀ Y, f xstar ≤ f Y) (hr : S.snorm p (initial-xstar) ≤ R) :
    S.snorm (dualExponent p) (grad ((matrixGradientMethod S p κ L R ε initial hp hκ hκhi engine).run grad).value) ≤ ε ∧
    (((matrixGradientMethod S p κ L R ε initial hp hκ hκhi engine).run grad).calls : ℝ) ≤
      queryConstant C (matrixBiasCoefficient p) p κ * (1 + (L*R^(κ-1)/ε)^beta p κ) := by
  have hK := queryConstant_pos hC (matrixBiasCoefficient_pos p) hp hκ
  by_cases hactive : 0 < L ∧ 0 < R ∧ 0 < ε ∧ ε < L*R^(κ-1)
  · let a : MatrixAccumulationData m n :=
      ⟨S, p, κ, L, R, ε, initial, hp, hκ, hκhi, hactive.1, hactive.2.1, hactive.2.2.1⟩
    have h := a.outputProgram_accuracy_and_complexity hC engine hactive.2.2.2 f grad hf hg hh xstar hstar hr
    simp only [matrixGradientMethod, dif_pos hactive]
    refine ⟨h.1, h.2.trans ?_⟩
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by norm_num)) hK.le
  · have heasy : L*R^(κ-1) ≤ ε := by
      by_contra hfail
      have hsmall : ε < L*R^(κ-1) := lt_of_not_ge hfail
      have hM : 0 < L*R^(κ-1) := lt_trans hε hsmall
      have hLpos : 0 < L := by
        rcases lt_or_eq_of_le hL with hpos | heq
        · exact hpos
        · rw [← heq, zero_mul] at hM
          linarith
      have hRpos : 0 < R := by
        rcases lt_or_eq_of_le hR with hpos | heq
        · exact hpos
        · rw [← heq, Real.zero_rpow (ne_of_gt (sub_pos.mpr hκ)), mul_zero] at hM
          linarith
      exact hactive ⟨hLpos, hRpos, hε, hsmall⟩
    have hrun := matrixGradientMethod_zero S p κ L R ε initial hp hκ hκhi engine grad heasy
    refine ⟨?_, ?_⟩
    · rw [hrun.1]
      have hzero := matrix_gradient_zero_at_minimizer f grad xstar (hg xstar) hstar
      have hh' := hh initial xstar
      rw [hzero, sub_zero] at hh'
      exact hh'.trans ((mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (S.snorm_nonneg _ _) hr (sub_pos.mpr hκ).le) hL).trans heasy)
    · rw [hrun.2, Nat.cast_zero]
      have hpow : 0 ≤ (L*R^(κ-1)/ε)^beta p κ :=
        Real.rpow_nonneg (div_nonneg (mul_nonneg hL (Real.rpow_nonneg hR _)) hε.le) _
      exact mul_nonneg hK.le (by linarith)

/-- Dimension-free quantifier order: K is fixed before both rectangular
sizes, all scales and accuracies, and the unknown smooth convex objective. -/
theorem matrix_upper_bound_uniform_constant {p κ C : ℝ}
    (hp : 2 ≤ p) (hκ : 1 < κ) (hκhi : κ ≤ 2) (hC : 0 ≤ C)
    (source : ExternalMatrixCompositeFamily p κ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (S : SpectralInput m n)
      (L R ε : ℝ), 0 ≤ L → 0 ≤ R → 0 < ε →
      ∀ (initial : Mat m n) (f : Mat m n → ℝ) (grad : Mat m n → Mat m n),
      ConvexOn ℝ Set.univ f → (∀ X, HasFDerivAt f (traceFunctional (grad X)) X) →
      (∀ X Y, S.snorm (dualExponent p) (grad X-grad Y) ≤ L * S.snorm p (X-Y)^(κ-1)) →
      ∀ xstar, (∀ Y, f xstar ≤ f Y) → S.snorm p (initial-xstar) ≤ R →
      S.snorm (dualExponent p)
        (grad ((matrixGradientMethod S p κ L R ε initial hp hκ hκhi (source m n hm hn S)).run grad).value) ≤ ε ∧
      (((matrixGradientMethod S p κ L R ε initial hp hκ hκhi (source m n hm hn S)).run grad).calls : ℝ) ≤
        K * (1 + (L*R^(κ-1)/ε)^beta p κ) := by
  refine ⟨queryConstant C (matrixBiasCoefficient p) p κ,
    queryConstant_pos hC (matrixBiasCoefficient_pos p) hp hκ, ?_⟩
  intro m n hm hn S L R ε hL hR hε initial f grad hf hg hh xstar hstar hr
  exact matrixGradientMethod_guarantee S hp hκ hκhi hC hL hR hε (source m n hm hn S)
    initial f grad hf hg hh xstar hstar hr

end P31.Schatten

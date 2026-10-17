import Paper34.RefinementOptimization
import Paper34.SampleMedian
import Paper34.CellOscillation
import Paper34.ArbitraryRepresentatives
import Paper34.ComputationalScope

/-! The source estimator in the exact-LP oracle model. All optimizer queries
are actual weighted-LAD or finite minimax queries, with attained optima proved
before querying the oracle. Neither the unknown p, the noise sigma, nor the
outlier indicators are inputs to the estimator. -/
namespace Paper34
noncomputable section

/-- Observable grid data, including the fixed boundary convention. -/
structure ObservedGrid (n m M : ℕ) where
  location : Fin M → Point n
  label : Fin M → ℝ
  samples : CellIndex n m → Finset (Fin M)
  inside : ∀ j, ∀ i ∈ samples j, location i ∈ closedCell j

/-- The actual fixed half-open assignment used on every input. -/
def observedGridOfBatch {n m M : ℕ} (X : Fin M → Point n) (Y : Fin M → ℝ) : ObservedGrid n m M := by
  classical
  exact ⟨X, Y, fun j => Finset.univ.filter (fun i => X i ∈ halfOpenCell j),
    fun j i hi => halfOpenCell_subset_closedCell j (Finset.mem_filter.mp hi).2⟩

def ObservedGrid.toGood {n m M : ℕ} (D : ObservedGrid n m M)
    (hN : ∀ j, (D.samples j).Nonempty) (inlier : Fin M → Prop) [DecidablePred inlier] :
    GoodSampleGrid n m (Fin M) :=
  ⟨D.samples, D.location, inlier, inferInstance, hN, D.inside⟩

/-- An internal analytic package; its fields are produced by the paper's
norming chain, Dirichlet estimate, and Lemma 5.1. It is not an external axiom. -/
structure RegressionAnalysis (n d m : ℕ) (rho : ℝ) where
  norming : MultisetNorming n d m (zeta rho)
  accuracy_lt_one : zeta rho < 1
  l1_to_sup : L1ToSup n d
  gamma : ℝ
  gamma_lt_one : gamma < 1
  oscillation : ∀ q : PolynomialSpace n d, CellOscillation (m := m) gamma q

/-- The permitted exact optimizer primitive, restricted to the two actual LP
families. Any optimizer returned is admissible. The nonempty minimum proof is
not a source assumption: it is established before each oracle call. -/
structure ExactRegressionLPOracle (n d m : ℕ) [NeZero m] where
  solveLAD : ∀ (M : ℕ) (S : CellIndex n m → Finset (Fin M))
    (X : Fin M → Point n) (Y : Fin M → ℝ),
    (∃ q : PolynomialSpace n d, ∀ r : PolynomialSpace n d, weightedLAD S X Y q ≤ weightedLAD S X Y r) → PolynomialSpace n d
  solveLAD_optimal : ∀ (M : ℕ) (S : CellIndex n m → Finset (Fin M))
    (X : Fin M → Point n) (Y : Fin M → ℝ)
    (h : ∃ q : PolynomialSpace n d, ∀ r : PolynomialSpace n d, weightedLAD S X Y q ≤ weightedLAD S X Y r),
    ∀ r : PolynomialSpace n d, weightedLAD S X Y (solveLAD M S X Y h) ≤ weightedLAD S X Y r
  solveMinimax : ∀ (a : CellIndex n m → Point n) (y : CellIndex n m → ℝ),
    (∃ r : PolynomialSpace n d, ∀ q : PolynomialSpace n d, representativeResidual a y r ≤ representativeResidual a y q) →
      PolynomialSpace n d
  solveMinimax_optimal : ∀ (a : CellIndex n m → Point n) (y : CellIndex n m → ℝ)
    (h : ∃ r : PolynomialSpace n d, ∀ q : PolynomialSpace n d, representativeResidual a y r ≤ representativeResidual a y q),
    ∀ q : PolynomialSpace n d, representativeResidual a y (solveMinimax a y h) ≤ representativeResidual a y q

/-- Existence of a mathematical exact oracle follows from the proved minimum
existence in each submitted query; it introduces no new Lean axiom. -/
def canonicalRegressionLPOracle (n d m : ℕ) [NeZero m] : ExactRegressionLPOracle n d m where
  solveLAD _ _ _ _ h := Classical.choose h
  solveLAD_optimal _ _ _ _ h := Classical.choose_spec h
  solveMinimax _ _ h := Classical.choose h
  solveMinimax_optimal _ _ h := Classical.choose_spec h

/-- Smallest-index observed representative, exactly as permitted in Section 2. -/
def ObservedGrid.representative {n m M : ℕ} (D : ObservedGrid n m M)
    (hN : ∀ j, (D.samples j).Nonempty) (j : CellIndex n m) : Point n :=
  D.location ((D.samples j).min' (hN j))

theorem ObservedGrid.representative_inside {n m M : ℕ} (D : ObservedGrid n m M)
    (hN : ∀ j, (D.samples j).Nonempty) (j : CellIndex n m) :
    D.representative hN j ∈ closedCell j :=
  D.inside j _ ((D.samples j).min'_mem (hN j))

def ObservedGrid.residualMedians {n d m M : ℕ} (D : ObservedGrid n m M)
    (hN : ∀ j, (D.samples j).Nonempty) (q : PolynomialSpace n d) (j : CellIndex n m) : ℝ :=
  enumeratedMedian (D.samples j) (fun i => D.label i-polyEval q (D.location i)) (hN j)

def initialMinimumExists {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (C : RegressionAnalysis n d m rho) (D : ObservedGrid n m M)
    (hN : ∀ j, (D.samples j).Nonempty) :
    ∃ q : PolynomialSpace n d, ∀ r : PolynomialSpace n d, weightedLAD D.samples D.location D.label q ≤
      weightedLAD D.samples D.location D.label r := by
  exact weightedLAD_attains_on_nonempty_grid (D.toGood hN (fun _ => False)) D.label
    C.accuracy_lt_one C.norming C.l1_to_sup

def initialEstimate {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (O : ExactRegressionLPOracle n d m) (C : RegressionAnalysis n d m rho)
    (D : ObservedGrid n m M) (hN : ∀ j, (D.samples j).Nonempty) : PolynomialSpace n d :=
  O.solveLAD M D.samples D.location D.label (initialMinimumExists C D hN)

def correctionMinimumExists {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (C : RegressionAnalysis n d m rho) (D : ObservedGrid n m M)
    (hN : ∀ j, (D.samples j).Nonempty) (q : PolynomialSpace n d) :
    ∃ r : PolynomialSpace n d, ∀ s : PolynomialSpace n d,
      representativeResidual (D.representative hN) (D.residualMedians hN q) r ≤
      representativeResidual (D.representative hN) (D.residualMedians hN q) s :=
  representativeResidual_attains_minimum (D.representative hN) (D.residualMedians hN q)
    (D.representative_inside hN) C.gamma_lt_one C.oscillation

def correction {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (O : ExactRegressionLPOracle n d m) (C : RegressionAnalysis n d m rho)
    (D : ObservedGrid n m M) (hN : ∀ j, (D.samples j).Nonempty)
    (q : PolynomialSpace n d) : PolynomialSpace n d :=
  O.solveMinimax (D.representative hN) (D.residualMedians hN q) (correctionMinimumExists C D hN q)

structure RegressionState (n d : ℕ) where
  estimate : PolynomialSpace n d
  oracleCalls : ℕ

def iterationState {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (O : ExactRegressionLPOracle n d m) (C : RegressionAnalysis n d m rho)
    (D : ObservedGrid n m M) (hN : ∀ j, (D.samples j).Nonempty) : ℕ → RegressionState n d
  | 0 => ⟨initialEstimate O C D hN, 1⟩
  | t+1 => let s := iterationState O C D hN t
    ⟨s.estimate+correction O C D hN s.estimate, s.oracleCalls+1⟩

/-- Exactly one solveLADr query and T refinement queries on this branch. -/
theorem iterationState_calls {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (O : ExactRegressionLPOracle n d m) (C : RegressionAnalysis n d m rho)
    (D : ObservedGrid n m M) (hN : ∀ j, (D.samples j).Nonempty) (T : ℕ) :
    (iterationState O C D hN T).oracleCalls = 1+T := by
  induction T with
  | zero => rfl
  | succ t ih => simpa [iterationState, ih, Nat.add_assoc]

/-- The complete empty-cell branch and fixed-budget nonempty branch. -/
def runRegression {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (O : ExactRegressionLPOracle n d m) (C : RegressionAnalysis n d m rho)
    (D : ObservedGrid n m M) (T : ℕ) : RegressionState n d := by
  classical
  exact if hN : ∀ j, (D.samples j).Nonempty then iterationState O C D hN T else ⟨0, 0⟩

theorem runRegression_calls_le {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (O : ExactRegressionLPOracle n d m) (C : RegressionAnalysis n d m rho)
    (D : ObservedGrid n m M) (T : ℕ) : (runRegression O C D T).oracleCalls ≤ 1+T := by
  classical
  unfold runRegression
  split_ifs with hN
  · rw [iterationState_calls]
  · exact Nat.zero_le _

theorem runRegression_calls_of_nonempty {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (O : ExactRegressionLPOracle n d m) (C : RegressionAnalysis n d m rho)
    (D : ObservedGrid n m M) (T : ℕ) (hN : ∀ j, (D.samples j).Nonempty) :
    (runRegression O C D T).oracleCalls = 1+T := by
  classical
  simp only [runRegression, dif_pos hN]
  exact iterationState_calls O C D hN T

end
end Paper34

import PsgEst.EdgeMartingale
import PsgEst.EdgeVariance
import PsgEst.Regularizer

open Matrix BigOperators Real Finset
namespace PsgEst

/-- The concrete spectral regularizer of the actual stationary edge Laplacian. -/
noncomputable def edgeProcessA {d : ℕ} (Q : Stoch d) (st : Stationary Q) (τ : ℝ) :=
  regularizer (stationaryEdgeH_posSemidef Q st).isHermitian τ

/-- Coordinate identification of the two copies of the state space with `Fin (d+d)`. -/
noncomputable def edgeFinEquiv (d : ℕ) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ ≃ₐ[ℝ] Matrix (Fin (d+d)) (Fin (d+d)) ℝ :=
  Matrix.reindexAlgEquiv ℝ ℝ finSumFinEquiv

lemma edgeFin_posSemidef {d : ℕ} (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ)
    (hM : M.PosSemidef) : (edgeFinEquiv d M).PosSemidef :=
  hM.submatrix finSumFinEquiv.symm

/-- Actual regularized edge observation, in the coordinates of matrix Freedman. -/
noncomputable def edgeProcessK {d : ℕ} (Q : Stoch d) (st : Stationary Q) (τ : ℝ)
    (i j : Fin d) : Matrix (Fin (d+d)) (Fin (d+d)) ℝ :=
  edgeFinEquiv d (regularizedEdge st.mu (edgeProcessA Q st τ) i j)

/-- The actual edge martingale differences of Proposition 1. -/
noncomputable def edgeProcessZ {d m : ℕ} (Q : Stoch d) (st : Stationary Q) (τ : ℝ) :=
  edgeIncrement (m := m) Q (edgeProcessK Q st τ)

lemma edgeProcessK_posSemidef {d : ℕ} (Q : Stoch d) (st : Stationary Q) (τ : ℝ)
    (i j : Fin d) : (edgeProcessK Q st τ i j).PosSemidef :=
  edgeFin_posSemidef _ (regularizedEdge_posSemidef st.mu _ (regularizer_isHermitian _ τ) i j)

/-- The concrete edge observations satisfy both bounds needed for matrix
Freedman: `0 ≤ W ≤ R I` and `W² ≤ R W`, with `R=2/(p τ)`. -/
theorem edgeProcessK_bounds {d : ℕ} [NeZero d] (Q : Stoch d) (st : Stationary Q)
    (τ : ℝ) (hτ : 0 < τ) (i j : Fin d) :
    ((2/(Stationary.star st*τ)) • (1 : Matrix (Fin (d+d)) (Fin (d+d)) ℝ) - edgeProcessK Q st τ i j).PosSemidef ∧
    ((2/(Stationary.star st*τ)) • edgeProcessK Q st τ i j - edgeProcessK Q st τ i j * edgeProcessK Q st τ i j).PosSemidef := by
  have hH := stationaryEdgeH_posSemidef Q st
  have hb := regularizedEdge_bounds st.mu st.pos (edgeProcessA Q st τ)
    (regularizer_isHermitian hH.isHermitian τ) (Stationary.star st) τ
    (Stationary.star_pos st) hτ (Stationary.star_le st)
    (regularizer_energy_le hH.isHermitian hH hτ) i j
  constructor
  · have h := edgeFin_posSemidef _ hb.1
    simpa only [map_sub, map_smul, map_one, edgeProcessK] using h
  · have h := edgeFin_posSemidef _ hb.2
    simpa only [map_sub, map_smul, map_mul, edgeProcessK] using h

/-- The stationary mean of the actual regularized observations is bounded by
identity, as proved for the explicit inverse square root. -/
theorem edgeProcess_population_le_one {d : ℕ} (Q : Stoch d) (st : Stationary Q)
    (τ : ℝ) (hτ : 0 < τ) :
    ((1 : Matrix (Fin (d+d)) (Fin (d+d)) ℝ) -
      ∑ i, st.mu i • edgeRowMean Q (edgeProcessK Q st τ) i).PosSemidef := by
  have hH := stationaryEdgeH_posSemidef Q st
  have hpop : ((1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) -
      ∑ i, st.mu i • edgeRowMean Q (regularizedEdge st.mu (edgeProcessA Q st τ)) i).PosSemidef := by
    rw [regularizedEdge_stationaryMean]
    exact regularizer_population_le_one hH.isHermitian hH hτ
  have h := edgeFin_posSemidef _ hpop
  simpa only [map_sub, map_one, map_sum, map_smul, edgeRowMean, edgeProcessK] using h

/-- Sharp increment norm bound for the constructed process, using the PSD
bounds on both `W` and its actual transition mean `M`. -/
theorem edgeProcess_increment_norm {d m : ℕ} [NeZero d] (Q : Stoch d) (st : Stationary Q)
    (τ : ℝ) (hτ : 0 < τ) (t : Fin m) (Y : Fin (m+1) → Fin d) :
    euclideanMatrixNorm (edgeProcessZ Q st τ t Y) ≤ 2/(Stationary.star st*τ) := by
  have hp := Stationary.star_pos st
  have hM := edgeRowMean_posSemidef Q (edgeProcessK Q st τ) (edgeProcessK_posSemidef Q st τ)
  have hMu := edgeRowMean_upper Q (edgeProcessK Q st τ) (2/(Stationary.star st*τ))
    (fun i j => (edgeProcessK_bounds Q st τ hτ i j).1)
  exact matrixEuclideanNorm_sub_le_of_psd_bounds _ _ _ (by positivity)
    (edgeProcessK_posSemidef Q st τ _ _) (hM _) (edgeProcessK_bounds Q st τ hτ _ _).1 (hMu _)

/-- The full matrix Freedman hypotheses, verified for the actual edge process. -/
theorem edgeProcess_freedman {d m : ℕ} [NeZero d] (Q : Stoch d) (st : Stationary Q)
    (mu : Fin d → ℝ) (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (τ : ℝ) (hτ : 0 < τ) (hinput : MatrixFreedmanInput Q mu) :
    FreedmanJointInput Q mu (2*d) (2/(Stationary.star st*τ))
      (martingaleSumNorm (edgeProcessZ (m := m) Q st τ))
      (predictableVariationNorm Q mu (edgeProcessZ (m := m) Q st τ)) := by
  have hp := Stationary.star_pos st
  have h := matrixFreedman_joint Q mu hinput (2/(Stationary.star st*τ))
    (edgeProcessZ (m := m) Q st τ) hmu hsum (by positivity)
    (edgeIncrement_isHermitian Q _ (fun i j => (edgeProcessK_posSemidef Q st τ i j).isHermitian))
    (edgeIncrement_adapted Q _)
    (edgeIncrement_centered Q mu _)
    (edgeProcess_increment_norm Q st τ hτ)
  simpa only [Nat.two_mul] using h

/-- Actual variation bound (17), with no variance or centering premise. -/
theorem edgeProcess_variation {d m : ℕ} [NeZero d] (Q : Stoch d) (st : Stationary Q)
    (mu : Fin d → ℝ) (τ η : ℝ) (hτ : 0 < τ) (hη : 0 ≤ η)
    (Y : Fin (m+1) → Fin d) (hE : degreeEvent st.mu η Y) :
    predictableVariationNorm Q mu (edgeProcessZ Q st τ) Y ≤
      (2/(Stationary.star st*τ))*(m:ℝ)*(1+η) := by
  have hp := Stationary.star_pos st
  exact predictableVariationNorm_degree_bound Q mu (edgeProcessK Q st τ) st.mu
    (2/(Stationary.star st*τ)) η (by positivity) hη
    (edgeProcessK_posSemidef Q st τ)
    (fun i j => (edgeProcessK_bounds Q st τ hτ i j).2)
    (edgeProcess_population_le_one Q st τ hτ) Y hE

/-- Inequality (18) for the paper's constructed edge martingale, depending
only on the original external matrix Freedman theorem. -/
theorem edgeProcess_tail {d m : ℕ} [NeZero d] (Q : Stoch d) (st : Stationary Q)
    (mu : Fin d → ℝ) (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (τ η : ℝ) (hτ : 0 < τ) (hη : 0 < η) (hη4 : η ≤ 1/4) (hm : 0 < m)
    (hinput : MatrixFreedmanInput Q mu) :
    eventProb Q.P mu (fun Y : Fin (m+1) → Fin d => degreeEvent st.mu η Y ∧
      η*(m:ℝ) < martingaleSumNorm (edgeProcessZ Q st τ) Y)
      ≤ 4*(d:ℝ)*exp (-(3*(m:ℝ)*Stationary.star st*τ*η^2/16)) :=
  freedman_on_degree_event Q mu hmu (Stationary.star st) τ η hm (Stationary.star_pos st)
    hτ hη hη4 (degreeEvent st.mu η) _ _
    (edgeProcess_variation Q st mu τ η hτ hη.le)
    (edgeProcess_freedman Q st mu hmu hsum τ hτ hinput)

end PsgEst

import PsgEst.LaplacianCounts
import PsgEst.BipartiteSpectrum

open Matrix BigOperators Real

namespace PsgEst

variable {d m : ℕ}

/-- A contraction has a positive semidefinite bipartite Laplacian. -/
theorem bipH_nonneg_of_contraction (L : Matrix (Fin d) (Fin d) ℝ)
    (hL : ∀ y : Fin d → ℝ, ∑ i, (L *ᵥ y) i ^ 2 ≤ ∑ i, y i ^ 2)
    (z : Fin d ⊕ Fin d → ℝ) : 0 ≤ z ⬝ᵥ (bipH L *ᵥ z) := by
  let x := z ∘ Sum.inl
  let y := z ∘ Sum.inr
  have hz : z = Sum.elim x y := by ext i; cases i <;> rfl
  rw [hz, bipH_dotProduct, ← dotProduct_mulVec_eq_sum]
  have hsq : 0 ≤ ∑ i, (x i - (L *ᵥ y) i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have he : (∑ i, (x i - (L *ᵥ y) i) ^ 2) =
      (∑ i, x i ^ 2) + (∑ i, (L *ᵥ y) i ^ 2) - 2 * (x ⬝ᵥ (L *ᵥ y)) := by
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hsq
  linarith only [hsq, hL y]

/-- The degree event is sufficient for positivity of every empirical degree. -/
theorem degPos_of_degree_bounds (μ : Fin d → ℝ) (hμ : ∀ i, 0 < μ i)
    (Y : Fin (m+1) → Fin d) (hm : 0 < m) (η : ℝ) (hη : η < 1)
    (hout : degEvent (fun i => (outDeg Y i : ℝ) / (m : ℝ)) μ η)
    (hin : degEvent (fun i => (inDeg Y i : ℝ) / (m : ℝ)) μ η) : degPos Y := by
  intro i
  have hM : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hbase : 0 < (1 - η) * μ i := mul_pos (by linarith) (hμ i)
  have ho := (le_div_iff₀ hM).mp (hout i).1
  have hi := (le_div_iff₀ hM).mp (hin i).1
  have hr : 0 < (outDeg Y i : ℝ) := lt_of_lt_of_le (mul_pos hbase hM) ho
  have hc : 0 < (inDeg Y i : ℝ) := lt_of_lt_of_le (mul_pos hbase hM) hi
  exact ⟨Nat.cast_pos.mp hr, Nat.cast_pos.mp hc⟩

/-- The degree bounds imply the exact diagonal normalization interval. -/
theorem empiricalScale_bounds (μ : Fin d → ℝ) (hμ : ∀ i, 0 < μ i)
    (Y : Fin (m+1) → Fin d) (η : ℝ)
    (hout : degEvent (fun i => (outDeg Y i : ℝ) / (m : ℝ)) μ η)
    (hin : degEvent (fun i => (inDeg Y i : ℝ) / (m : ℝ)) μ η) :
    ∀ a, 1 - η ≤ empiricalScale μ Y a ∧ empiricalScale μ Y a ≤ 1 + η := by
  intro a
  rcases a with i | i
  · change 1 - η ≤ (outDeg Y i : ℝ) / ((m : ℝ) * μ i) ∧
      (outDeg Y i : ℝ) / ((m : ℝ) * μ i) ≤ 1 + η
    rw [← div_div]
    exact ⟨(le_div_iff₀ (hμ i)).mpr (hout i).1, (div_le_iff₀ (hμ i)).mpr (hout i).2⟩
  · change 1 - η ≤ (inDeg Y i : ℝ) / ((m : ℝ) * μ i) ∧
      (inDeg Y i : ℝ) / ((m : ℝ) * μ i) ≤ 1 + η
    rw [← div_div]
    exact ⟨(le_div_iff₀ (hμ i)).mpr (hin i).1, (div_le_iff₀ (hμ i)).mpr (hin i).2⟩

private theorem sortedEigenvalue_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B)
    (j : Fin (Fintype.card ι)) : hA.eigenvalues₀ j = hB.eigenvalues₀ j := by
  subst B
  rfl

/-- Actual deterministic conclusion of Proposition 1. The inputs are the
outgoing/incoming count degree event and quadratic-form bounds (19) for the
empirical mean of the observed edge matrices. The conclusion refers to the
paper's actual sorted second singular values, including multiplicities. -/
theorem prop1_deterministic_counts (hd : 1 < d) (S : Stoch d) (st : Stationary S)
    (k : ℕ) (Y : Fin (m+1) → Fin d) (hm : 0 < m)
    (τ η : ℝ) (hτ : 0 < τ) (hη : 0 < η) (hη' : η ≤ 1/4)
    (hout : degEvent (fun i => (outDeg Y i : ℝ) / (m : ℝ)) st.mu η)
    (hin : degEvent (fun i => (inDeg Y i : ℝ) / (m : ℝ)) st.mu η)
    (hlo : ∀ x : Fin d ⊕ Fin d → ℝ,
      (1 - 2 * η) * (x ⬝ᵥ (bipH (Lk S st k) *ᵥ x)) - η * τ * (x ⬝ᵥ x) ≤
        x ⬝ᵥ (empiricalHbar st.mu Y *ᵥ x))
    (hhi : ∀ x : Fin d ⊕ Fin d → ℝ,
      x ⬝ᵥ (empiricalHbar st.mu Y *ᵥ x) ≤
        (1 + 2 * η) * (x ⬝ᵥ (bipH (Lk S st k) *ᵥ x)) + η * τ * (x ⬝ᵥ x)) :
    degPos Y ∧ |(1 - sigma2 (lHat Y)) - (1 - sigma2 (Lk S st k))| ≤
      η * (3 * (1 - sigma2 (Lk S st k)) + τ) / (1 - η) := by
  have hη1 : η < 1 := by linarith
  have hpos := degPos_of_degree_bounds st.mu st.pos Y hm η hη1 hout hin
  refine ⟨hpos, ?_⟩
  let j : Fin (Fintype.card (Fin d ⊕ Fin d)) :=
    ⟨Fintype.card (Fin d ⊕ Fin d) - 2, by simp; omega⟩
  have hnorm := empiricalHbar_normalize st.mu st.pos Y hm hpos
  have heig := sortedEigenvalue_congr
    (diagonalNormalize (empiricalHbar st.mu Y) (empiricalScale st.mu Y))
    (bipH (lHat Y)) (diagonalNormalize_isHermitian _ (empiricalHbar_isHermitian _ _) _)
    (bipH_isHermitian _) hnorm j
  have hbound := prop1_deterministic_of_matrix_bounds
    (bipH (Lk S st k)) (empiricalHbar st.mu Y) (bipH_isHermitian _)
    (empiricalHbar_isHermitian _ _) τ η hη hη' hτ
    (bipH_nonneg_of_contraction _ (Lk_contraction S st k))
    (empiricalHbar_nonneg _ _) hlo hhi (empiricalScale st.mu Y)
    (empiricalScale_bounds st.mu st.pos Y η hout hin) j
  rw [heig] at hbound
  simpa only [j, lhat_bipH_second_smallest_eq hd Y hpos,
    Lk_bipH_second_smallest_eq hd S st k] using hbound

end PsgEst

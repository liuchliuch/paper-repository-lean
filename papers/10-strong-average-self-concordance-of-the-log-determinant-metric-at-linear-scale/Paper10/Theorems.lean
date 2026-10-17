import Paper10.Proposal
import Paper10.CanonicalBasis
import Paper10.SSCFrame

noncomputable section
open Matrix MeasureTheory
open scoped MatrixOrder
namespace Paper10

/-- Uniform strong average self-concordance of one scaled metric, in a complete canonical
coordinate system. The pointwise auxiliary precision E is arbitrary PSD. -/
def SASC (q : ℕ) (s : ℝ) : Prop :=
  ∃ hs : 0 < s, ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ ρ : ℝ, 0 < ρ ∧
    ∀ (X : Matrix (Fin q) (Fin q) ℝ), X.PosDef →
    ∀ (E : Matrix (Fin (n q)) (Fin (n q)) ℝ) (hE : E.PosSemidef)
      (r : ℝ), 0 < r → r ≤ ρ →
      let H := proposalStep (canonicalF q) (CFC.sqrt X) s r E hs hE
      1 - ε ≤ (stdGaussianMeasure (n q)).real {ω | sascEvent s X (X + H ω) (H ω) ε r}

/-- Definition 1.2 for the family of all linearly scaled log-determinant metrics.
The radius precedes q,s,X,E in the quantifier order. -/
def UniformSASC : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ ρ : ℝ, 0 < ρ ∧
    ∀ (q : ℕ) (hq : 0 < q) (s : ℝ) (hs : c q ≤ s)
      (X : Matrix (Fin q) (Fin q) ℝ), X.PosDef →
    ∀ (E : Matrix (Fin (n q)) (Fin (n q)) ℝ) (hE : E.PosSemidef)
      (r : ℝ), 0 < r → r ≤ ρ →
      let H := proposalStep (canonicalF q) (CFC.sqrt X) s r E (lt_of_lt_of_le (c_pos q) hs) hE
      1 - ε ≤ (stdGaussianMeasure (n q)).real {ω | sascEvent s X (X + H ω) (H ω) ε r}

namespace Main
/-- Theorem 1.3, estimate (6), with an explicit complete n-dimensional Gaussian proposal. -/
theorem thm_1_3_two_sided (q : ℕ) (hq : 0 < q)
    (X : Matrix (Fin q) (Fin q) ℝ) (hX : X.PosDef)
    {s ε r : ℝ} (hs : c q ≤ s) (hε : 0 < ε) (hε1 : ε < 1)
    (hr : 0 < r) (hr1 : r ≤ rEps ε)
    (E : Matrix (Fin (n q)) (Fin (n q)) ℝ) (hE : E.PosSemidef) :
    let H := proposalStep (canonicalF q) (CFC.sqrt X) s r E (lt_of_lt_of_le (c_pos q) hs) hE
    1 - ε ≤ (stdGaussianMeasure (n q)).real {ω | sascEventTwoSided s X (X + H ω) (H ω) ε r} :=
  Paper10.thm_1_3_two_sided hq (canonicalF q) (canonicalF_orthonormal q) X hX hs hε hε1 hr hr1 E hE

/-- Theorem 1.3: every metric at the stated scale is SASC. -/
theorem thm_1_3_sasc (q : ℕ) (hq : 0 < q) {s : ℝ} (hs : c q ≤ s) : SASC q s := by
  refine ⟨lt_of_lt_of_le (c_pos q) hs, ?_⟩
  intro ε hε hε1
  refine ⟨rEps ε, rEps_pos hε, ?_⟩
  intro X hX E hE r hr hr1
  exact Paper10.thm_1_3_sasc hq (canonicalF q) (canonicalF_orthonormal q) X hX hs hε hε1 hr hr1 E hE

/-- Theorem 1.3: the entire family is uniformly SASC with the stated radius. -/
theorem thm_1_3_uniform : UniformSASC := by
  intro ε hε hε1
  refine ⟨rEps ε, rEps_pos hε, ?_⟩
  intro q hq s hs X hX E hE r hr hr1
  exact Paper10.thm_1_3_sasc hq (canonicalF q) (canonicalF_orthonormal q) X hX hs hε hε1 hr hr1 E hE

/-- Theorem 1.3: SSC holds exactly at s≥(q+1)/2. -/
theorem thm_1_3_ssc (q : ℕ) (hq : 0 < q) {s : ℝ} (hs : 0 < s) : SSC q s ↔ c q ≤ s :=
  Paper10.thm_1_3_ssc hq hs

/-- Theorem 1.3, equation (7): the joint SSC/SASC scale has the claimed actual minimum. -/
theorem thm_1_3_min_scale (q : ℕ) (hq : 0 < q) :
    IsLeast {s : ℝ | 0 < s ∧ SSC q s ∧ SASC q s} (c q) := by
  refine ⟨⟨c_pos q, (thm_1_3_ssc q hq (c_pos q)).mpr le_rfl, thm_1_3_sasc q hq le_rfl⟩, ?_⟩
  intro s hs
  exact (thm_1_3_ssc q hq hs.1).mp hs.2.1

end Main
end Paper10

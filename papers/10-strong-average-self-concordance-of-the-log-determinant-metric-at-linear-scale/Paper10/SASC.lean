import Paper10.Basic
import Paper10.Metric
import Paper10.Symm

/-!
# Strong average self-concordance (Definition 1.2)

Uniform SASC: for every ε in (0,1) there is r_ε > 0 such that the Gaussian
proposal H ~ N(0, r²/n (g(X)+ḡ(X))^{-1}), Z = X+H satisfies
  P[Z ∈ S_{++}^q, ‖H‖²_{g(Z)} - ‖H‖²_{g(X)} ≤ 2εr²/n] ≥ 1-ε
uniformly over base points and PSD auxiliary forms.
-/

noncomputable section

open Matrix

namespace Paper10

variable {q : ℕ}

/-- Admissible radius of Theorem 1.3: `r_ε = ε^{3/2} / sqrt 864`. -/
def rEps (ε : ℝ) : ℝ := ε ^ (3 / 2 : ℝ) / Real.sqrt 864

theorem rEps_eq (ε : ℝ) : rEps ε = ε ^ (3 / 2 : ℝ) / Real.sqrt 864 := rfl

theorem rEps_pos {ε : ℝ} (hε : 0 < ε) : 0 < rEps ε := by
  unfold rEps
  positivity

/-- One-sided SASC event (4). -/
def sascEvent (s : ℝ) (X Z H : Matrix (Fin q) (Fin q) ℝ) (ε r : ℝ) : Prop :=
  Z.PosDef ∧ localNormSq s Z H - localNormSq s X H ≤ 2 * ε * r ^ 2 / (n q)

/-- Two-sided SASC event (6). -/
def sascEventTwoSided (s : ℝ) (X Z H : Matrix (Fin q) (Fin q) ℝ) (ε r : ℝ) : Prop :=
  Z.PosDef ∧ |localNormSq s Z H - localNormSq s X H| ≤ 2 * ε * r ^ 2 / (n q)

/-- Positivity of the proposed admissible radius; this alone is not a SASC theorem. -/
theorem admissible_radius_pos (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    0 < rEps ε := by
  exact rEps_pos hε

end Paper10

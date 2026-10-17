import K44K35Free.PairingEstimates
import K44K35Free.SurvivalGeometry
import K44K35Free.Fields
import K44K35Free.Extremal

/-! The complete lower-bound construction and the final extremal conclusion.
All finite geometry, averaging and deletion premises are discharged here. -/
noncomputable section
namespace K44K35Free
open Geometry Construction

/-- An absolute positive constant from the actual local pruning. -/
def constructionConstant : ℝ :=
  1 / 6 ^ (16 * preliminaryLoad) * preliminaryConstant

theorem constructionConstant_pos : 0 < constructionConstant :=
  mul_pos (one_div_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 6) _))
    preliminaryConstant_pos

/-- The full graph construction at every sufficiently large odd finite field. -/
theorem finite_field_construction {F : Type} [Field F] [Fintype F]
    (hodd : Odd (Fintype.card F)) (hq : preliminaryThreshold ≤ Fintype.card F) :
    ∃ G : SimpleGraph (Param F ⊕ Param F), IsK35Free G ∧ G.IsBipartite ∧
      constructionConstant * (Fintype.card F : ℝ)^9 ≤ numK44 G := by
  have hchar : ringChar F ≠ 2 := Geometry.char_ne_two_of_odd_card hodd
  obtain ⟨α, hα⟩ := FiniteField.exists_nonsquare (F := F) hchar
  have hns : IsNonsquare α := by
    intro a ha
    exact hα ⟨a, by simpa [pow_two] using ha.symm⟩
  obtain ⟨c, T, hpre⟩ := exists_preliminary_many_copies α hns hodd hq
  obtain ⟨R, hR, hcount⟩ := proposition10_paper_bound α c hns T preliminaryLoad
    preliminaryConstant hpre
  refine ⟨finalGraph α c T preliminaryLoad R,
    proposition9 α c hns T preliminaryLoad R hR,
    finalGraph_isBipartite α c T preliminaryLoad R, ?_⟩
  have hcopies : ((survivingPairs α c T preliminaryLoad R).card : ℝ) ≤
      numK44 (finalGraph α c T preliminaryLoad R) := by
    exact_mod_cast survivingPairs_card_le_numK44 α c hns T preliminaryLoad R
  exact hcount.trans hcopies

/-- **Theorem 1 (lower bound).** The witnesses are actual bipartite graphs with
exactly n vertices. No construction certificate or additional premise remains. -/
theorem theorem_1_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
        Fintype.card V = n ∧ IsK35Free G ∧ G.IsBipartite ∧
          c * (n : ℝ)^3 ≤ numK44 G := by
  have hconstruct : ∀ k : ℕ, preliminaryThreshold ≤ 3 ^ k →
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
        Fintype.card V = 2 * (3 ^ k)^3 ∧ IsK35Free G ∧ G.IsBipartite ∧
          constructionConstant * (3 ^ k : ℝ)^9 ≤ numK44 G := by
    intro k hk
    have hk0 : k ≠ 0 := by
      intro hk0
      subst k
      norm_num [preliminaryThreshold, pairingDenominator] at hk
    obtain ⟨F, instF, instFin, hcard, hodd, _, _⟩ := exists_field_three_power k hk0
    letI : Field F := instF
    letI : Fintype F := instFin
    obtain ⟨G, hfree, hbip, hcopies⟩ := finite_field_construction hodd (by rwa [hcard])
    refine ⟨Param F ⊕ Param F, inferInstance, G, ?_, hfree, hbip, ?_⟩
    · simp [Param, hcard, two_mul]
    · simpa only [hcard, Nat.cast_pow, Nat.cast_ofNat] using hcopies
  obtain ⟨hpos, n₀, hn₀⟩ := amplify_power_three_construction constructionConstant
    constructionConstant_pos preliminaryThreshold hconstruct
  exact ⟨constructionConstant / 54^3, hpos, n₀, hn₀⟩

/-- The stated consequence `ex(n,K₄,₄,K₃,₅)=Θ(n³)`, expressed as the
positive absolute upper and lower constants in the definition of Θ. -/
theorem theorem_1_cubic_order :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      c * (n : ℝ)^3 ≤ exK44K35 n ∧ (exK44K35 n : ℝ) ≤ C * (n : ℝ)^3 :=
  extremal_cubic_bounds_of_graph_lower_bound theorem_1_lower_bound

end K44K35Free

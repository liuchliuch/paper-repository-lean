import Paper02.StreamingTractability
import Paper02.Basic
import Paper02.RudinShapiro
import Paper02.LSym
import Paper02.Bounds
import Paper02.MeasureCircle
import Paper02.RSWords
import Paper02.LowerBound
import Paper02.Fourier
import Paper02.Cutoff

/-!
# Paper-facing statements (Theorem 1.1 and supporting results)

Paper-facing wrappers for the second-difference certificate and the full
cancellation-cost conclusions. Operational streaming membership is stated
separately from the elementary properties of the witness.
-/

noncomputable section

namespace Paper02.Main

open Paper02 Paper02.RS Paper02.LSym Paper02.Bounds

/-- Target function (1.6). -/
abbrev target : ℤ → ℝ := f

/-- Second-difference operator (2.1). -/
abbrev D : (ℤ → ℝ) → ℤ → ℝ := secondDiff

/-- Lemma 2.4 (2.5)–(2.6): transition counts of `P_m, Q_m`. -/
theorem lemma_2_4_T_add_U (m : ℕ) : T m + U m = 2 ^ m - 1 :=
  T_add_U m

/-- Lemma 2.1 kernel identities used in the positive second-difference measure. -/
theorem lemma_2_1_gaussian (A : ℝ) (k : ℤ) :
    D (fun x : ℤ => A * (x : ℝ) ^ 2) k = A :=
  secondDiff_gaussian A k

theorem lemma_2_1_cos (s : ℝ) (k : ℤ) :
    D (fun x : ℤ => 1 - Real.cos ((x : ℝ) * s)) k
      = (1 - Real.cos s) * Real.cos ((k : ℝ) * s) :=
  secondDiff_cos s k

/-- Corollary 2.2, Gaussian part. -/
theorem cor_2_2_gaussian {ι : Type} [Fintype ι] (a : ι → ℝ) (k : ι → ℤ) (A : ℝ)
    (hA : 0 ≤ A) (M : ℝ) (hM : ∀ t : ℝ, |∑ i, a i * Real.cos ((k i : ℝ) * t)| ≤ M) :
    |∑ i, a i * D (fun x : ℤ => A * (x : ℝ) ^ 2) (k i)| ≤ A * M :=
  dual_gaussian a k A hA M hM

/-- Corollary 2.2, finite atomic jump part. -/
theorem cor_2_2_atomic {ι J : Type} [Fintype ι] [Fintype J]
    (a : ι → ℝ) (k : ι → ℤ) (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) (s : J → ℝ)
    (M : ℝ) (hM : ∀ t : ℝ, |∑ i, a i * Real.cos ((k i : ℝ) * t)| ≤ M) :
    |∑ i, a i * D (fun x : ℤ => ∑ j, c j * (1 - Real.cos ((x : ℝ) * s j))) (k i)|
      ≤ (∑ j, c j * (1 - Real.cos (s j))) * M :=
  dual_atomic a k c hc s M hM

/-- Proposition 3.1 (algebraic form). -/
theorem prop_3_1_algebra (N : ℕ) (η ρ s1 : ℝ)
    (hN : 16 ≤ N) (hη' : η < 1/6)
    (hpair : (1 - 6 * η) * ((N:ℝ) - 3) ≤ s1 * (Real.sqrt (2 * (N:ℝ)) + 3))
    (hs1 : s1 ≤ 3 * ρ) :
    (1 - 6 * η) * ((N:ℝ) - 3) / (3 * (Real.sqrt (2 * (N:ℝ)) + 3)) ≤ ρ :=
  Paper02.Bounds.prop_3_1_algebra N η ρ s1 hN hη' hpair hs1

/-- Proposition 3.3 (algebraic Cauchy–Schwarz / Parseval). -/
theorem prop_3_3_bound (p : ℕ) (c : Fin p → ℝ) (hp : 0 < p)
    (h : ∑ j, |c j| ^ 2 ≤ 9) :
    (∑ j, |c j|) ≤ 3 * Real.sqrt (p:ℝ) :=
  Paper02.Bounds.prop_3_3_bound p c hp h

/-- Basic finite properties of the witness; streaming membership is a separate
operational statement and is not defined by these properties. -/
theorem f_is_even_bounded :
    f 0 = 0 ∧ (∀ k : ℤ, 0 ≤ f k) ∧ (∀ k : ℤ, f k ≤ 3) ∧ (∀ k : ℤ, f (-k) = f k) :=
  ⟨f_zero, fun k => f_nonneg k, fun k => f_le_three k, fun k => f_even k⟩

/-- The complete positive circle measure assertion of Lemma 2.1. -/
theorem lemma_2_1 {g : ℝ → ℝ} (hg : IsLSym g) :
    ∃ μ : MeasureTheory.Measure Real.Angle, MeasureTheory.IsFiniteMeasure μ ∧
      μ Set.univ = ENNReal.ofReal (g 1) ∧
      ∀ k : ℤ, secondDiff (RestrictInt g) k =
        ∫ t : Real.Angle, Real.Angle.cos (k • t) ∂μ :=
  LSym.positive_second_difference_measure hg

/-- Lemma 2.5, including the exact parity-dependent boundary correction. -/
theorem lemma_2_5 (m : ℕ) (hN : 16 ≤ 2 ^ m) :
    (∑ k ∈ Finset.Icc 2 (2 ^ m - 2), rudinShapiro k * secondDiff f (k : ℤ)) =
      if Odd m then -((2 ^ m : ℕ) : ℝ) + 1 else -((2 ^ m : ℕ) : ℝ) + 3 :=
  RS.exact_pairing m hN

/-- Proposition 3.1 from the original Lévy cone and approximation assumptions. -/
theorem proposition_3_1 (m : ℕ) (η ρ : ℝ) (gp gn : ℝ → ℝ)
    (hN : 16 ≤ 2 ^ m) (hη0 : 0 ≤ η) (hη : η < 1 / 6)
    (hp : AdmissibleLSymPair gp gn f (2 ^ m - 1) η ρ) :
    (1 - 6 * η) * (((2 ^ m : ℕ) : ℝ) - 3) /
      (3 * (Real.sqrt (2 * (2 ^ m : ℕ)) + 3)) ≤ ρ :=
  LowerBound.prop_3_1 m η ρ gp gn hN hη0 hη hp

/-- Corollary 3.2 for all cutoffs, with the original strict constant. -/
theorem corollary_3_2 (n : ℕ) (hn : 15 ≤ n) (η : ℝ)
    (hη0 : 0 ≤ η) (hη : η < 1 / 6) :
    (1 - 6 * η) * Real.sqrt ((n : ℝ) + 1) / (8 * Real.sqrt 2) < rho f n η :=
  Cutoff.cor_3_2 n hn η hη0 hη

/-- The exact finite Fourier–Hahn split of Proposition 3.3. -/
theorem proposition_3_3 (n : ℕ) (hn : 1 ≤ n) :
    ∃ gp gn : ℝ → ℝ,
      AdmissibleLSymPair gp gn f n 0 (6 * Real.sqrt (2 * (n : ℝ) + 1)) :=
  Fourier.prop_3_3 n hn

/-- All three cancellation-cost inequalities (1.7). -/
theorem theorem_1_1_bounds (n : ℕ) (hn : 15 ≤ n) (η : ℝ)
    (hη0 : 0 < η) (hη : η < 1 / 6) :
    (1 - 6 * η) * Real.sqrt ((n : ℝ) + 1) / (8 * Real.sqrt 2) < rho f n η ∧
      rho f n η ≤ rho f n 0 ∧ rho f n 0 ≤ 6 * Real.sqrt (2 * (n : ℝ) + 1) :=
  Cutoff.theorem_1_1_bounds n hn η hη0 hη

/-- The square-root order asserted in Theorem 1.1. -/
theorem theorem_1_1_theta (η : ℝ) (hη0 : 0 < η) (hη : η < 1 / 6) :
    Asymptotics.IsTheta Filter.atTop (fun n : ℕ => rho f n η)
      (fun n : ℕ => Real.sqrt (n : ℝ)) :=
  Cutoff.rho_isTheta_sqrt η hη0.le hη

/-- The complete separation theorem: actual bit-space streaming membership,
all three cancellation bounds, the all-cutoff exact upper bound, square-root
order, and failure of the original bivariate polynomial implication. -/
theorem theorem_1_1 :
    BitSpaceModel.IsTEvenPlus f ∧
    (∀ n : ℕ, 15 ≤ n → ∀ η : ℝ, 0 < η → η < 1 / 6 →
      ENNReal.ofReal ((1 - 6 * η) * Real.sqrt ((n : ℝ) + 1) / (8 * Real.sqrt 2)) <
        Cutoff.rhoExtended f n η ∧
      Cutoff.rhoExtended f n η ≤ Cutoff.rhoExtended f n 0 ∧
      Cutoff.rhoExtended f n 0 ≤ ENNReal.ofReal (6 * Real.sqrt (2 * (n : ℝ) + 1))) ∧
    (∀ n : ℕ, 1 ≤ n → rho f n 0 ≤ 6 * Real.sqrt (2 * (n : ℝ) + 1)) ∧
    (∀ η : ℝ, 0 < η → η < 1 / 6 →
      Asymptotics.IsTheta Filter.atTop (fun n : ℕ => rho f n η)
        (fun n : ℕ => Real.sqrt (n : ℝ))) ∧
    (¬ ∃ Q : Polynomial (Polynomial ℝ), ∀ n : ℕ, 1 ≤ n →
      ∀ η : ℝ, 0 < η → η < 1 →
        rho f n η ≤ (Q.eval (Polynomial.C η⁻¹)).eval (Real.log (2 * (n : ℝ)))) :=
  ⟨StreamingTractability.proposition_3_4, Cutoff.theorem_1_1_ennreal_bounds,
    Cutoff.prop_3_3_rho, theorem_1_1_theta,
    Cutoff.controlled_decomposition_conjecture_false_bivariate⟩

end Paper02.Main

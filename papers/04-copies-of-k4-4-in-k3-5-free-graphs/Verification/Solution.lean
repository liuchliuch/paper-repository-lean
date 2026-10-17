import K44K35Free

/-! Independent statements for the official Comparator. All mathematical
objects are concrete; the production root never imports this file. -/
noncomputable section
open scoped BigOperators
open K44K35Free K44K35Free.Geometry K44K35Free.Construction
attribute [local instance] Classical.propDecidable Classical.decEq

theorem Verification.theorem_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      Fintype.card V = n ∧ IsK35Free G ∧ G.IsBipartite ∧
        c * (n : ℝ)^3 ≤ numK44 G := by
  exact K44K35Free.theorem_1

theorem Verification.theorem_1_theta :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    c * (n : ℝ)^3 ≤ exK44K35 n ∧ (exK44K35 n : ℝ) ≤ C * (n : ℝ)^3 := by
  exact K44K35Free.theorem_1_theta

theorem Verification.lemma_2 :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsK35Free G → 8 * numK44 G ≤ (Fintype.card V).choose 3 := by
  exact K44K35Free.lemma_2

theorem Verification.lemma_3 :
    ∀ {F : Type} [Field F] (α : F) (c : Quartic F), IsNonsquare α →
    ∀ (p q r : Param F), p ≠ q → p ≠ r → q ≠ r →
      LinearIndependent F ![point α c p, point α c q, point α c r] := by
  exact K44K35Free.lemma_3_projective

theorem Verification.proposition_4 :
    ∀ {F : Type} [Field F] [Fintype F] (α : F) (c : Quartic F),
    IsNonsquare α → Odd (Fintype.card F) →
    (∀ E : Plane F, ¬ Exceptional α c E → (planeSection α c E).card ≤ 4) ∧
    Disjoint (identityPlanes α c) (Fiber.fiberPlanes (F := F)) ∧
    (identityPlanes α c).card = Fintype.card F ^ 3 * (Fintype.card F + 1) ∧
    (Fiber.fiberPlanes (F := F)).card =
      Fintype.card F ^ 4 + Fintype.card F ^ 3 + Fintype.card F ^ 2 + 1 ∧
    (∑ E ∈ Geometry.exceptionalPlanes α c, (planeSection α c E).card) =
      2 * Fintype.card F ^ 5 + 2 * Fintype.card F ^ 4 + Fintype.card F ^ 3 ∧
    (∀ E : Plane F, Exceptional α c E → (planeSection α c E).card ≤ 2 * Fintype.card F) ∧
    (∀ E : Plane F, IdentityExceptional α c E →
      (planeSection α c E).card = Fintype.card F) ∧
    (∀ p : Param F, ((identityPlanes α c).filter (fun E => point α c p ∈ E.val)).card =
      Fintype.card F * (Fintype.card F + 1)) := by
  exact K44K35Free.proposition_4

theorem Verification.remark_5 :
    ∀ {F : Type} [Field F] [Fintype F] (α : F) (c : Quartic F),
    IsNonsquare α → Odd (Fintype.card F) → ∀ X : Finset (Param F),
    (∀ E : Plane F, IdentityExceptional α c E → (X ∩ planeSection α c E).card ≤ 4) →
      X.card ≤ 4 * Fintype.card F ^ 2 := by
  exact K44K35Free.remark_5

theorem Verification.lemma_6 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ q₀ : ℕ,
    ∀ (F : Type) [Field F] [Fintype F] (α : F), IsNonsquare α →
      Odd (Fintype.card F) → q₀ ≤ Fintype.card F → ∃ c : Quartic F,
        c₀ * (Fintype.card F : ℝ)^9 ≤ (Construction.richPlanes α c).card := by
  obtain ⟨c₀, hc₀, q₀, h⟩ := K44K35Free.lemma_6
  refine ⟨c₀, hc₀, q₀, ?_⟩
  intro F _ _ α hα hodd hq
  exact h F α hα (char_ne_two_of_odd_card hodd) hq

theorem Verification.lemma_7 :
    ∀ {F : Type} [Field F] [Fintype F] (α : F) (c : Quartic F)
    (T : V F ≃ₗ[F] V F) (e : Param F × Param F), e ∈ initialEdges α c T →
      ((Construction.designatedPairs α c T).filter (fun D => e ∈ copyEdges α c D)).card ≤
        gaussianBinom2 (Fintype.card F) := by
  exact K44K35Free.lemma_7

theorem Verification.lemma_7_growth :
    ∀ q : ℕ, 2 ≤ q → gaussianBinom2 q ≤ 6 * q^4 := by
  exact K44K35Free.lemma_7_bound

theorem Verification.lemma_8 :
    ∀ {F : Type} [Field F] [Fintype F] (α : F) (c : Quartic F), IsNonsquare α →
    ∀ (T : V F ≃ₗ[F] V F) (A C E : Plane F),
      (A,C) ∈ Construction.designatedPairs α c T → Exceptional α c E →
      (planeSection α c A ∩ planeSection α c (leftDual T E)).card ≤ 2 ∧
      (planeSection α c C ∩ planeSection α c (rightDual T E)).card ≤ 2 := by
  intro F _ _ α c hα T A C E hD hE
  obtain ⟨hA, hC, hpair⟩ := (mem_designatedPairs α c T (A,C)).mp hD
  exact K44K35Free.lemma_8 α c hα T A C E hpair hA.1 hC.1 hE

theorem Verification.proposition_9 :
    ∀ {F : Type} [Field F] [Fintype F] (α : F) (c : Quartic F), IsNonsquare α →
    ∀ (T : V F ≃ₗ[F] V F) (L : ℕ) (R : Choices α c), ValidChoices α c T R →
      IsK35Free (finalGraph α c T L R) := by
  exact K44K35Free.proposition_9

theorem Verification.proposition_10 :
    ∀ {F : Type} [Field F] [Fintype F] (α : F) (c : Quartic F), IsNonsquare α →
    ∀ (T : V F ≃ₗ[F] V F) (L : ℕ) (c₂ : ℝ),
      c₂ * (Fintype.card F : ℝ)^9 ≤ (preDesignated α c T L).card →
      ∃ R : Choices α c, ValidChoices α c T R ∧
        1 / 6 ^ (16 * L) * c₂ * (Fintype.card F : ℝ)^9 ≤
          (survivingPairs α c T L R).card := by
  exact K44K35Free.proposition_10

theorem Verification.preliminary :
    ∀ {F : Type} [Field F] [Fintype F] (α : F), IsNonsquare α →
    Odd (Fintype.card F) → preliminaryThreshold ≤ Fintype.card F →
      ∃ (c : Quartic F) (T : V F ≃ₗ[F] V F),
        preliminaryConstant * (Fintype.card F : ℝ)^9 ≤
          (preDesignated α c T preliminaryLoad).card := by
  exact K44K35Free.preliminary_lower_bound

theorem Verification.copies :
    ∀ {F : Type} [Field F] [Fintype F] (α : F) (c : Quartic F), IsNonsquare α →
    ∀ (T : V F ≃ₗ[F] V F) (L : ℕ) (R : Choices α c),
      (survivingPairs α c T L R).card ≤ numK44 (finalGraph α c T L R) := by
  exact K44K35Free.designated_copies_le_graph_copies


import Paper27
noncomputable section
open scoped BigOperators Manifold
open Polynomial
namespace P27Check

theorem Degree.genus_nine :
    (2 * (9 : ℤ) - 2) - 2 * (2 * 3 - 2) = 8 :=
  by sorry

theorem Degree.normal_degree :
    ∀ (g n d : ℝ), 2 ≤ g → 2 ≤ n → n * d = 2 - 2 * g →
    d = -(2 * g - 2) / n ∧ d < 0 :=
  by sorry

theorem Degree.same_index :
    ∀ (d t n m : ℝ), d ≠ 0 → n * d = t → m * d = t → n = m :=
  by sorry

theorem Degree.negative_hom_degree :
    ∀ (κ n : ℝ), 0 < κ → 2 ≤ n →
    -κ - (-κ / n) = -κ * (1 - 1 / n) ∧ -κ * (1 - 1 / n) < 0 :=
  by sorry

theorem Local.second_derivative :
    ∀ (m : ℕ) {φ : ℂ → ℂ} {t w φ' : ℂ}, HasDerivAt φ φ' t →
    HasFDerivAt (Paper27.localSecondProjection m φ)
      (Paper27.localSecondDifferential m w φ') (t,w) :=
  by sorry

theorem Local.first_submersion :
    ∀ (m : ℕ) (φ : ℂ → ℂ) (p : ℂ × ℂ),
    Function.Surjective (fderiv ℂ (fun q => (Paper27.localBranchMap m φ q).1) p) :=
  by sorry

theorem Local.second_rank :
    ∀ (m : ℕ), 2 ≤ m → ∀ {φ : ℂ → ℂ} {t w φ' : ℂ}, HasDerivAt φ φ' t →
    (Function.Surjective (fderiv ℂ (Paper27.localSecondProjection m φ) (t,w)) ↔
      w ≠ 0 ∨ φ' ≠ 0) :=
  by sorry

theorem Local.second_critical :
    ∀ (m : ℕ), 2 ≤ m → ∀ {φ : ℂ → ℂ} {t : ℂ}, HasDerivAt φ 0 t →
    ¬ Function.Surjective (fderiv ℂ (Paper27.localSecondProjection m φ) (t,0)) :=
  by sorry

theorem Laurent.character_sum :
    ∀ {n : ℕ} {ζ : ℂ}, IsPrimitiveRoot ζ n → ∀ (e : ℤ),
    (∑ j ∈ Finset.range n, ζ ^ (e * (j : ℤ))) =
      if (n : ℤ) ∣ e then (n : ℂ) else 0 :=
  by sorry

theorem Laurent.equation_six :
    ∀ {n : ℕ} {ζ a : ℂ}, 0 < n → IsPrimitiveRoot ζ n → a ≠ 0 → a ≠ 1 →
    ∀ (c₃ : Paper27.CyclicLaurent.Coefficients), Paper27.CyclicLaurent.PoleBound n c₃ →
    c₃ (1 - (n : ℤ)) = -(1 / (a * (n : ℂ))) →
    a / (a - 1) - 1 / (a - 1) = 1 ∧
    Paper27.CyclicLaurent.TangentRegular (Paper27.CyclicLaurent.affineCombination a
      (Paper27.CyclicLaurent.standardSplittingCoefficients n)
      (Paper27.CyclicLaurent.average n ζ c₃)) ∧
    Paper27.CyclicLaurent.pushforward ζ 1 (Paper27.CyclicLaurent.affineCombination a
      (Paper27.CyclicLaurent.standardSplittingCoefficients n)
      (Paper27.CyclicLaurent.average n ζ c₃)) =
      Paper27.CyclicLaurent.affineCombination a
      (Paper27.CyclicLaurent.standardSplittingCoefficients n)
      (Paper27.CyclicLaurent.average n ζ c₃) :=
  by sorry

theorem Splitting.average_splitting :
    ∀ {G V W : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W],
    ∀ (ρ : G →* V ≃ₗ[ℂ] V) (π : V →ₗ[ℂ] W) (σ : W →ₗ[ℂ] V),
    (∀ g v, π (ρ g v) = π v) → (∀ w, π (σ w) = w) →
    ∀ w, π (Paper27.Splitting.average ρ σ w) = w :=
  by sorry

theorem Splitting.average_invariant :
    ∀ {G V W : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W],
    ∀ (ρ : G →* V ≃ₗ[ℂ] V) (σ : W →ₗ[ℂ] V) (g : G) (w : W),
    ρ g (Paper27.Splitting.average ρ σ w) = Paper27.Splitting.average ρ σ w :=
  by sorry

theorem Splitting.fixed_tangent :
    ∀ {ζ w : ℂ}, ζ ≠ 1 → ∀ (v : ℂ × ℂ),
    (v.1, ζ * v.2) = v → v.1 = w → v = (w,0) :=
  by sorry

theorem Jet.square_coefficient :
    ∀ (F : ℂ[X]) (n : ℕ), (∀ j < n, F.coeff j = 0) →
    (F ^ 2).coeff (2 * n) = (F.coeff n) ^ 2 :=
  by sorry

theorem Jet.composition_coefficient :
    ∀ (F : ℂ[X]) (n : ℕ) (p q : ℂ), (∀ j < n, F.coeff j = 0) →
    (C p * F + C (q / 2) * F ^ 2).coeff (2 * n) =
      p * F.coeff (2 * n) + q / 2 * (F.coeff n) ^ 2 :=
  by sorry

theorem Jet.connection_law :
    ∀ (a p q b b' : ℂ), a ≠ 0 → a ≠ 1 →
    b' * p ^ 2 = p * b + (a ^ 2 - a) / 2 * q →
    (-2 * b' / (a ^ 2 - a)) * p ^ 2 =
      p * (-2 * b / (a ^ 2 - a)) - q :=
  by sorry

theorem Compact.constant_coefficient :
    ∀ {D : Type*} [TopologicalSpace D] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) 1 D] [CompactSpace D] [ConnectedSpace D]
    (a : D → ℂ), MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) a →
    (∀ p, a p ≠ 0) → (∀ p, a p ≠ 1) →
    ∃ c : ℂ, c ≠ 0 ∧ c ≠ 1 ∧ ∀ p, a p = c :=
  by sorry

theorem CoverGroup.product_subgroup :
    ∀ {G₁ G₂ : Type*} [Group G₁] [Group G₂] (Γ : Subgroup (G₁ × G₂)),
    (Paper27.ProductCoverGroup.firstFactor Γ).prod
      (Paper27.ProductCoverGroup.secondFactor Γ) ≤ Γ :=
  by sorry

theorem CoverGroup.finite_index :
    ∀ {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    (Γ : Subgroup (G₁ × G₂)) [Γ.FiniteIndex],
    (Paper27.ProductCoverGroup.firstFactor Γ).FiniteIndex ∧
      (Paper27.ProductCoverGroup.secondFactor Γ).FiniteIndex :=
  by sorry

end P27Check

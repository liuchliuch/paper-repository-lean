import Paper34.Model
import Paper34.Parameters
import Mathlib.Data.Finset.Basic

/-! Weighted LAD algebra from Section 4. The samplewise and finite weighted
inequalities are proved for the actual loss. The norming-to-coercivity bridge
keeps its dependence on the still-unproved Corollary 3.4 explicit. -/
namespace Paper34
open BigOperators
noncomputable section

/-- Cell-normalized Chebyshev-mass weighted averaging, counting every index. -/
def weightedAverage {κ ι : Type*} [Fintype κ]
    (S : κ → Finset ι) (F : κ → ι → ℝ) : ℝ :=
  (Fintype.card κ : ℝ)⁻¹ * ∑ c, ((S c).card : ℝ)⁻¹ * ∑ i ∈ S c, F c i

theorem weightedAverage_mono {κ ι : Type*} [Fintype κ]
    (S : κ → Finset ι) {F G : κ → ι → ℝ}
    (h : ∀ c, ∀ i ∈ S c, F c i ≤ G c i) : weightedAverage S F ≤ weightedAverage S G := by
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro c _
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_le_sum (fun i hi => h c i hi)

theorem weightedAverage_const {κ ι : Type*} [Fintype κ] [Nonempty κ]
    (S : κ → Finset ι) (hS : ∀ c, (S c).Nonempty) (a : ℝ) :
    weightedAverage S (fun _ _ => a) = a := by
  have hcard : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcell : ∀ c, ((S c).card : ℝ) ≠ 0 := by
    intro c
    exact_mod_cast Finset.card_ne_zero.mpr (hS c)
  simp [weightedAverage, Finset.sum_const, nsmul_eq_mul, hcell, hcard]

theorem weightedAverage_sub {κ ι : Type*} [Fintype κ]
    (S : κ → Finset ι) (F G : κ → ι → ℝ) :
    weightedAverage S (fun c i => F c i-G c i) =
      weightedAverage S F-weightedAverage S G := by
  simp only [weightedAverage, Finset.sum_sub_distrib, mul_sub]

/-- The weighted objective (2.6), with arbitrary finite cell samples. -/
def weightedLAD {κ ι : Type*} [Fintype κ] {n d : ℕ}
    (S : κ → Finset ι) (X : ι → Point n) (Y : ι → ℝ)
    (q : PolynomialSpace n d) : ℝ :=
  weightedAverage S (fun _ i => |polyEval q (X i)-Y i|)

/-- The exact reverse-triangle calculation for an inlier. -/
theorem inlier_loss_difference {p e y sigma : ℝ} (hnoise : |p-y| ≤ sigma) :
    |e|-2*sigma ≤ |p+e-y|-|p-y| := by
  have htri : |e| ≤ |p+e-y|+|p-y| := by
    calc |e| = |(p+e-y)-(p-y)| := by congr 1; ring
      _ ≤ |p+e-y|+|p-y| := abs_sub _ _
  linarith

/-- The corresponding calculation puts no restriction on an outlier label. -/
theorem outlier_loss_difference (p e y : ℝ) :
    -|e| ≤ |p+e-y|-|p-y| := by
  have htri : |p-y| ≤ |p+e-y|+|e| := by
    calc |p-y| = |(p+e-y)-e| := by congr 1; ring
      _ ≤ |p+e-y|+|e| := abs_sub _ _
  linarith

/-- Equation (4.4), using the harmless upper bound 2 sigma for all noise terms.
`good` is the true inlier indicator; the loss itself does not observe it. -/
theorem lad_signed_mass_lower {κ ι : Type*} [Fintype κ] [Nonempty κ]
    {n d : ℕ} (S : κ → Finset ι) (hS : ∀ c, (S c).Nonempty)
    (X : ι → Point n) (Y : ι → ℝ) (p e : PolynomialSpace n d)
    (good : ι → Prop) [DecidablePred good] {sigma : ℝ} (hs : 0 ≤ sigma)
    (hnoise : ∀ c, ∀ i ∈ S c, good i → |polyEval p (X i)-Y i| ≤ sigma) :
    weightedAverage S (fun _ i => if good i then |polyEval e (X i)| else -|polyEval e (X i)|)
      - 2*sigma ≤ weightedLAD S X Y (p+e)-weightedLAD S X Y p := by
  have hpoint : ∀ c, ∀ i ∈ S c,
      (if good i then |polyEval e (X i)| else -|polyEval e (X i)|)-2*sigma ≤
        |polyEval (p+e) (X i)-Y i|-|polyEval p (X i)-Y i| := by
    intro c i hi
    rw [polyEval_add]
    by_cases hgi : good i
    · simpa [hgi] using inlier_loss_difference (hnoise c i hi hgi)
    · simp only [hgi, ↓reduceIte]
      have hh := outlier_loss_difference (polyEval p (X i)) (polyEval e (X i)) (Y i)
      linarith
  have h := weightedAverage_mono S hpoint
  rw [weightedAverage_sub, weightedAverage_const S hS, weightedAverage_sub] at h
  exact h

/-- This is the remaining algebra of (4.1), conditional on the independently
needed inlier/outlier norming estimates (4.5) and (4.6). -/
theorem lad_coefficient_lower_of_mass_bounds {L P G B E sigma rho : ℝ}
    (hraw : G-B-2*sigma ≤ L-P)
    (hgood : (1-alpha rho)*(1-zeta rho)*E ≤ G)
    (hbad : B ≤ alpha rho*(1+zeta rho)*E) :
    gap rho/2*E-2*sigma ≤ L-P := by
  have hid := lad_margin_coefficient rho
  have hidE := congrArg (fun v : ℝ => v*E) hid
  nlinarith only [hraw, hgood, hbad, hidE]

/-- The initializer estimate (4.2) follows for any actual loss minimizer once
the coercive LAD lower bound is available. It does not prove that bound. -/
theorem initializer_l1_of_lad_lower {κ ι : Type*} [Fintype κ]
    {n d : ℕ} (S : κ → Finset ι) (X : ι → Point n) (Y : ι → ℝ)
    (p q : PolynomialSpace n d) {sigma g : ℝ} (hg : 0 < g)
    (hlower : g/2*l1Norm (q-p)-2*sigma ≤ weightedLAD S X Y q-weightedLAD S X Y p)
    (hmin : ∀ r : PolynomialSpace n d, weightedLAD S X Y q ≤ weightedLAD S X Y r) :
    l1Norm (q-p) ≤ 4*sigma/g := by
  apply (le_div_iff₀ hg).2
  have h := hmin p
  nlinarith

end
end Paper34

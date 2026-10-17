import UniformBorderRank.GrowthBounds
import UniformBorderRank.FixedWeight
import UniformBorderRank.BlockProducts
import UniformBorderRank.DerivativeDimension
import UniformBorderRank.Comb
import UniformBorderRank.Flattening
import UniformBorderRank.FiniteDiff
import UniformBorderRank.Centralizer
import UniformBorderRank.Contraction
import UniformBorderRank.ProductCurve
import UniformBorderRank.UniformBound
import UniformBorderRank.ProjectiveSecant
import UniformBorderRank.OriginalPresentation

/-!
# Paper statements

Explicit propositions for the numbered results of
"Uniform complex border-rank bounds from all-cut Schmidt ranks"
(source inventory `source-results.json`).

Each proposition states the paper's mathematical content.  Auxiliary
combinatorial envelopes are named honestly as envelopes and are not
substituted for the paper's conclusions.
-/

namespace UniformBorderRank.PaperStatements

open UniformBorderRank Finset

/-- **Lemma 3.1.** The two expressions for `F` agree; `F` is increasing on
positive integers and satisfies `F a + F b ≤ F (a+b)` for `a, b ≥ 1`. -/
def lemma_3_1 : Prop :=
  (∀ q : ℕ, 2 ≤ q → Fsum q = F q)
  ∧ (∀ a b : ℕ, 1 ≤ a → 1 ≤ b → F a + F b ≤ F (a + b))
  ∧ (∀ q : ℕ, 2 ≤ q → F (q - 1) < F q)

/-- **Lemma 2.3 (Centralizer bound).**  Let `q 0, …, q (b-1)` be pairwise
cross-commuting unital sets of matrices in `End(ℂ^r)`, each noncommutative.
Then `b ≤ r^2 - 1`. -/
def lemma_2_3 : Prop :=
  ∀ (r : ℕ) (_hr : 1 ≤ r)
    (q : ℕ → Set (Matrix (Fin r) (Fin r) ℂ)) (b : ℕ)
    (_hcomm : ∀ i j, i < b → j < b → i ≠ j → CrossComm (q i) (q j))
    (_hnc : ∀ k < b, IsNoncommutative (q k)),
    b ≤ r ^ 2 - 1

/-- **Product tensors have CP rank ≤ 1.** -/
def product_rank_le_one : Prop :=
  ∀ (N : ℕ) (d : Fin N → ℕ) (T : Coeffs d), isProduct T → cpRankLe T 1

/-- **Border rank is bounded by CP rank.** -/
def border_of_cp : Prop :=
  ∀ (N : ℕ) (d : Fin N → ℕ) (T : Coeffs d) (b : ℕ),
    cpRankLe T b → borderRankLe T b

/-- **Finite-difference evaluation count (paper (13)).**
The coefficient of `t^k` in a product curve is recovered from `k+1`
evaluations, independently of the product length. -/
def finite_difference_eval_count : Prop :=
  ∀ k : ℕ, evalPoints k = k + 1 ∧ coeffRankBound k = k + 1

/-- **All-cut flattening ranks.**  The paper's hypothesis (1) is the bound
`schmidtRank d T S ≤ D` for every nontrivial cut `S`. -/
def all_cut_hypothesis : Prop :=
  ∀ (N : ℕ) (d : Fin N → ℕ) (T : Coeffs d) (D : ℕ),
    allCutLe d T D ↔
    ∀ S : Finset (Fin N), S ≠ ∅ → S ≠ (Finset.univ) → schmidtRank d T S ≤ D

/-- **Lemma 2.1.** A product contraction is injective on an arbitrary
`r`-dimensional tensor subspace after retaining at most `r-1` factors. -/
def lemma_2_1 : Prop :=
  ∀ (N : ℕ) (d : Fin N → ℕ) (E : Submodule ℂ (Coeffs d)) (r : ℕ),
    r = Module.finrank ℂ E → 1 ≤ r →
    ∃ (J : Finset (Fin N)) (b : ∀ i : Fin N, Fin (d i) → ℂ),
      J.card ≤ r - 1 ∧ Function.Injective (fun T : E => contractCoeffs T.val J b)

/-- **Lemma 2.3, complete conclusion.** In any finite family of cross-commuting
unital matrix algebras there are at most `r²-1` noncommutative sites; the
remaining sites generate a commutative algebra of dimension at most `r²`. -/
def lemma_2_3_full : Prop :=
  ∀ (ι : Type) [Fintype ι] (r : ℕ), 1 ≤ r →
    ∀ (A : ι → Subalgebra ℂ (EndMat r)),
    (∀ i j, i ≠ j → CrossComm (A i : Set (EndMat r)) (A j : Set (EndMat r))) →
    (noncommutativeSites A).card ≤ r ^ 2 - 1 ∧
    (∀ x ∈ Algebra.adjoin ℂ (goodGenerators A),
      ∀ y ∈ Algebra.adjoin ℂ (goodGenerators A), x * y = y * x) ∧
    Module.finrank ℂ (Algebra.adjoin ℂ (goodGenerators A)) ≤ r ^ 2

/-- **Equation (13), actual tensor border-rank conclusion.** -/
def product_curve_coefficient : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (d : Fin N → ℕ)
    (v w : ∀ i : Fin N, Fin (d i) → ℂ) (k : ℕ),
    borderRankLe (prodCurveCoeff d v w k) (k + 1)

/-- **Theorem 1.1, rank-one branch.** -/
def theorem_1_1_rank_one : Prop :=
  ∀ (N : ℕ), 2 ≤ N → ∀ (d : Fin N → ℕ) (T : Coeffs d),
    T ≠ 0 → maxSchmidtRank d T = 1 → isProduct T

/-- **Proposition 3.2.** The tensor of arbitrary linear maps into a
finite-dimensional commutative unital complex algebra has border rank at
most `F` of the algebra dimension, independently of tensor order. -/
def proposition_3_2 : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (d : Fin N → ℕ) (A : Type)
    [CommRing A] [Algebra ℂ A] [FiniteDimensional ℂ A],
    1 ≤ Module.finrank ℂ A →
    ∀ (phi : ∀ i, (Fin (d i) → ℂ) →ₗ[ℂ] A) (ell : A →ₗ[ℂ] ℂ),
    borderRankLe (d := d)
      (fun u => ell (∏ i, phi i (Pi.single (u i) 1))) (F (Module.finrank ℂ A))

/-- **Theorem 1.1, both branches with the actual original maximal cut rank.** -/
def theorem_1_1 : Prop :=
  ∀ (N : ℕ), 2 ≤ N → ∀ (d : Fin N → ℕ) (T : Coeffs d), T ≠ 0 →
    (maxSchmidtRank d T = 1 → isProduct T) ∧
    (2 ≤ maxSchmidtRank d T → borderRankLe T
      ((maxSchmidtRank d T) ^ ((maxSchmidtRank d T) ^ 2 +
        2 * maxSchmidtRank d T - 3) * F ((maxSchmidtRank d T) ^ 2)))

/-- **Corollary 1.2, explicit uniform numerical bound.** The only tensor
hypothesis is the original all-cut rank bound. -/
def all_cut_uniform_bound : Prop :=
  ∀ (N D : ℕ), 2 ≤ N → 1 ≤ D → ∀ (d : Fin N → ℕ) (T : Coeffs d),
    T ≠ 0 → allCutLe d T D → borderRankLe T (Bhat D)

/-- **Corollary 1.2, genuine projective secant containment.** The conclusion
uses projective spans of Segre points and homogeneous-polynomial Zariski
closure, independently of the border-rank predicate. -/
def corollary_1_2 : Prop :=
  ∀ (N D : ℕ), 2 ≤ N → 1 ≤ D → ∀ (d : Fin N → ℕ)
    (T : Coeffs d) (hT : T ≠ 0), allCutLe d T D →
    Projectivization.mk ℂ T hT ∈ projectiveSecant d (Bhat D)

/-- **Proposition 2.2, original anchored representation.** The conclusion
constructs the nonempty disjoint original anchor sets, actual split support
coordinates, supports of dimension `r`, normalized multilinear contraction,
coefficient reconstruction, and cross-commuting arbitrary-order site products.
`OriginalAnchoredPresentation` is the explicit data asserted by the conclusion;
no presentation, support, rank-normalization, or reconstruction is a premise. -/
def proposition_2_2 : Prop :=
  ∀ (N : ℕ), 2 ≤ N → ∀ (d : Fin N → ℕ) (T : Coeffs d),
    T ≠ 0 → 2 ≤ maxSchmidtRank d T →
    Nonempty (OriginalAnchoredPresentation d T (maxSchmidtRank d T))

/-- **Section 5.2, fixed-weight examples.** The actual coefficient tensors
have the stated border-rank and all-flattening bounds; weight zero is a product. -/
def fixed_weight_examples : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (d : Fin N → ℕ) (e₀ e₁ : ∀ i, Fin (d i) → ℂ),
    isProduct (fixedWeightTensor d e₀ e₁ 0) ∧
    ∀ k, borderRankLe (fixedWeightTensor d e₀ e₁ k) (k + 1) ∧
      ∀ S, schmidtRank d (fixedWeightTensor d e₀ e₁ k) S ≤ k + 1

/-- **Section 5.2, disjoint entangled blocks.** The tensor is an actual product
on the disjoint fibers of an original-site label; the block ranks are actual
flattening row-space dimensions. -/
def disjoint_block_examples : Prop :=
  ∀ (N : ℕ) (B : Type) [Fintype B] [DecidableEq B]
    (d : Fin N → ℕ) (block : Fin N → B) (T : ∀ b, BlockCoeffs d block b),
    (∀ S, schmidtRank d (blockProduct d block T) S = ∏ b, blockSchmidtRank T S b) ∧
    (2 ≤ N → blockProduct d block T ≠ 0 →
      ∀ (E : Finset B) (C : B → Finset (Fin N)),
      (∀ b ∈ E, 2 ≤ blockSchmidtRank T (C b) b) →
      2 ^ E.card ≤ maxSchmidtRank d (blockProduct d block T) ∧
      E.card ≤ Nat.log2 (maxSchmidtRank d (blockProduct d block T)))

/-- **Equation (18).** The space is generated by all actual iterated formal
partial derivatives of the source set-multilinear polynomial, including order zero. -/
def full_derivative_dimension : Prop :=
  (∀ (N : ℕ) (d : Fin N → ℕ) (T : Coeffs d),
    Module.finrank ℂ (fullDerivativeSpace (tensorPolynomial d T)) =
      ∑ S : Finset (Fin N), schmidtRank d T S) ∧
  (∀ (N : ℕ), 2 ≤ N → ∀ (d : Fin N → ℕ) (T : Coeffs d), T ≠ 0 →
    Module.finrank ℂ (fullDerivativeSpace (tensorPolynomial d T)) ≤
      2 ^ N * maxSchmidtRank d T) ∧
  (∀ (N : ℕ) (d : Fin N → ℕ) (T : Coeffs d), T ≠ 0 → isProduct T →
    Module.finrank ℂ (fullDerivativeSpace (tensorPolynomial d T)) = 2 ^ N)

/-- **Section 5.2, quantitative and asymptotic growth.** The final existential
is a literal meaning of `Bhat(D) = exp(O(D² log D))`. -/
def numerical_growth : Prop :=
  (∀ q : ℕ, 1 ≤ q → F q ≤ q * 4 ^ (q - 1)) ∧
  (∀ D : ℕ, 2 ≤ D → (Bhat D : ℝ) ≤ Real.exp (5 * (D : ℝ) ^ 2 * Real.log D)) ∧
  ∃ g : ℕ → ℝ,
    Asymptotics.IsBigO Filter.atTop g (fun D : ℕ => (D : ℝ) ^ 2 * Real.log D) ∧
    ∀ D, (Bhat D : ℝ) = Real.exp (g D)

end UniformBorderRank.PaperStatements

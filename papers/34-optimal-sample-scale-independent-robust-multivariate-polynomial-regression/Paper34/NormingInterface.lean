import Paper34.Model
import Paper34.MultisetRepresentative

/-! Shared source statements for the norming chain. These are propositions,
not axioms. Their proofs are supplied by the arbitrary-representative module;
downstream LAD arguments use them as explicit dependency interfaces. -/
namespace Paper34
open BigOperators
noncomputable section

/-- The source functional Phi, with true multiset sums and multiplicities. -/
def multisetPhi {n d m : ℕ} (A : CellIndex n m → Multiset (Point n))
    (q : PolynomialSpace n d) : ℝ :=
  ((m : ℝ)^n)⁻¹ * ∑ j, multisetAverage (A j) (fun x => |polyEval q x|)

def RepresentativeNorming (n d m : ℕ) (z : ℝ) : Prop :=
  ∀ (q : PolynomialSpace n d) (xi : CellIndex n m → Point n),
    (∀ j, xi j ∈ closedCell j) →
    |((m : ℝ)^n)⁻¹ * ∑ j, |polyEval q (xi j)| - l1Norm q| ≤ z*l1Norm q

/-- The exact conclusion of source Corollary 3.4, without hiding premises. -/
def MultisetNorming (n d m : ℕ) (z : ℝ) : Prop :=
  ∀ (q : PolynomialSpace n d) (A : CellIndex n m → Multiset (Point n)),
    (∀ j, A j ≠ 0) → (∀ j x, x ∈ A j → x ∈ closedCell j) →
    (1-z)*l1Norm q ≤ multisetPhi A q ∧ multisetPhi A q ≤ (1+z)*l1Norm q

/-- The standard Dirichlet reproduction consequence (4.7). Its producer is
proved from actual finite Fourier convolution, not stipulated as an axiom. -/
def L1ToSup (n d : ℕ) : Prop :=
  ∀ q : PolynomialSpace n d, supNorm q ≤ (2*(d : ℝ)+1)^n*l1Norm q

/-- The genuinely multivariate multiset step in the proof of Corollary 3.4.
The selecting point may depend jointly on the whole cell index. -/
theorem multisetNorming_of_representativeNorming {n d m : ℕ} {z : ℝ}
    (hrep : RepresentativeNorming n d m z) : MultisetNorming n d m z := by
  intro q A hA hAC
  obtain ⟨xi, hxi⟩ := mvPolynomial_abs_multiset_representatives closedCell A q.1 hA hAC
    isCompact_closedCell convex_closedCell
  have h := hrep q xi (fun j => (hxi j).1)
  have heq : multisetPhi A q = ((m : ℝ)^n)⁻¹ * ∑ j, |polyEval q (xi j)| := by
    unfold multisetPhi
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact (hxi j).2.symm
  rw [← heq] at h
  exact relative_norming_of_abs_error h

end
end Paper34

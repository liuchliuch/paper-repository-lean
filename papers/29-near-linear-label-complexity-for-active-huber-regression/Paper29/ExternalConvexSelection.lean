import Paper29.Attainment
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! Generic published convex-optimization inputs only. The quadratic
regularization limit is the classical Tikhonov/proximal limit (Bauschke and
Combettes, Convex Analysis and Monotone Operator Theory, regularization of
minimization problems; https://doi.org/10.1007/978-3-319-48311-5).
The parameter selection input is the measurable/continuous maximum theorem
specialized to nonnegative continuous convex objectives plus a positive
quadratic; compare Terazono–Matani, SIAM J. Optim.23(2), 2013,
https://doi.org/10.1137/110850189. No Huber, data dependence, pilot or regression
conclusion is included. These are Prop arguments without inhabitants/axioms. -/
noncomputable section
open MeasureTheory Filter
namespace Paper29.ExternalConvexSelection

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def RegularizedMinimizer {d : ℕ} (f : Space d → ℝ) (k : ℕ) (x : Space d) : Prop :=
  ∀ y,f x+((k+1:ℝ)⁻¹)*‖x‖^2 ≤ f y+((k+1:ℝ)⁻¹)*‖y‖^2

def ParametricQuadraticSelection : Prop :=
  ∀ n d (F : (Fin n → ℝ) × Space d → ℝ),Continuous F →
    (∀ b,ConvexOn ℝ Set.univ (fun x => F (b,x))) → (∀ b x,0 ≤ F (b,x)) →
    ∃ z : ℕ → (Fin n → ℝ) → Space d,
      (∀ k,Measurable (z k)) ∧ ∀ k b,
        RegularizedMinimizer (fun x => F (b,x)) k (z k b) ∧
        ∀ x,RegularizedMinimizer (fun x => F (b,x)) k x → x=z k b

def TikhonovConvergence : Prop :=
  ∀ d (f : Space d → ℝ),Continuous f → ConvexOn ℝ Set.univ f →
    ∀ v,(∀ y,f v ≤ f y) → (∀ y,(∀ u,f y ≤ f u) → ‖v‖ ≤ ‖y‖) →
    ∀ z : ℕ → Space d,(∀ k,RegularizedMinimizer f k (z k)) → Tendsto z atTop (nhds v)

end Paper29.ExternalConvexSelection

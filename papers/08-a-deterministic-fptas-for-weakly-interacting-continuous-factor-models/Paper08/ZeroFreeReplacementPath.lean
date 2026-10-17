import Paper08.ZeroFreeMarginal
import Paper08.CubeExponentialPath

/-!
# The actual one-occurrence replacement path and its derivative

The path is the partial cube expectation of the original exponential along
an affine real interpolation. Its derivative is obtained by dominated
differentiation of that actual integral, and it agrees with the replacement
model throughout the closed parameter interval.
-/
noncomputable section
open MeasureTheory Filter
namespace Paper08.ZeroFreeInduction
open Integral CubeMarginal CubeExponentialPath

variable {n m r c : ℕ} {q : ℝ}

/-- Actual partial expectation along one labelled-occurrence interpolation. -/
def replacementPath (M : Model n m r c q) (j : Fin n) (A : Finset (Fin m)) (e : Fin m)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (Fin n)) (x : Fin n → ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  avg S (fun y => Complex.exp (z*((M.freezeSet j A ha hb).total y+
    (t : ℂ)*(M.delta j a b e y : ℂ)))) x

/-- Actual derivative of the same expectation, in the weighted-ratio form. -/
def replacementDerivative (M : Model n m r c q) (j : Fin n) (A : Finset (Fin m)) (e : Fin m)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (Fin n)) (x : Fin n → ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  z*avg S (fun y => (M.delta j a b e y : ℂ)*Complex.exp (z*((M.freezeSet j A ha hb).total y+
    (t : ℂ)*(M.delta j a b e y : ℂ)))) x

/-- The actual path is continuously differentiable at all real parameters;
no model promise outside `[0,1]` is used. -/
theorem replacementPath_hasDerivAt_and_continuous (M : Model n m r c q) (hq : 0 ≤ q)
    (j : Fin n) (A : Finset (Fin m)) (e : Fin m)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (Fin n)) {x : Fin n → ℝ} (hx : x ∈ cube n) (z : ℂ) :
    (∀ t : ℝ, HasDerivAt (replacementPath M j A e ha hb S x z)
      (replacementDerivative M j A e ha hb S x z t) t) ∧
    Continuous (replacementDerivative M j A e ha hb S x z) := by
  let N := M.freezeSet j A ha hb
  let base : (S → ℝ) → ℝ := fun y => N.total (overwrite S x y)
  let delta : (S → ℝ) → ℝ := fun y => M.delta j a b e (overwrite S x y)
  have hbase : AEStronglyMeasurable base (MultiMoments.unitMeasure S) :=
    (integrable_real_section S N.continuous_total hx).aestronglyMeasurable
  have hdelta : AEStronglyMeasurable delta (MultiMoments.unitMeasure S) :=
    (integrable_real_section S (M.continuous_delta j ha hb e) hx).aestronglyMeasurable
  have hbaseB : ∀ᵐ y ∂MultiMoments.unitMeasure S, |base y| ≤ (m : ℝ)*q := by
    filter_upwards [ae_mem_box S] with y hy
    rcases N.total_range (overwrite_mem_cube S hx hy) with ⟨h0,h1⟩
    simpa only [base,abs_of_nonneg h0] using h1
  have hdeltaB : ∀ᵐ y ∂MultiMoments.unitMeasure S, |delta y| ≤ q := by
    filter_upwards [ae_mem_box S] with y hy
    exact M.abs_delta_le j ha hb e (overwrite_mem_cube S hx hy)
  exact real_hasDerivAt_and_continuous (MultiMoments.unitMeasure S) hq
    hbase hdelta hbaseB hdeltaB z

/-- Inside the parameter interval this integral is the genuine mixture model. -/
lemma replacementPath_eq_partial (M : Model n m r c q) (j : Fin n)
    (A : Finset (Fin m)) (e : Fin m) (he : e ∉ A)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (Fin n)) (x : Fin n → ℝ) (z : ℂ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    replacementPath M j A e ha hb S x z t = (M.replacement j A e ha hb t ht).partial S z x := by
  unfold replacementPath Model.partial
  apply congrArg (fun f => avg S f x)
  funext y
  unfold Model.exponential
  rw [M.replacement_total j A e he ha hb t ht y]
  push_cast
  rfl

/-- The actual derivative is the exact weighted marginal used by the ratio
estimate; its integrand is the same genuine replacement model. -/
lemma replacementDerivative_eq_avg (M : Model n m r c q) (j : Fin n)
    (A : Finset (Fin m)) (e : Fin m) (he : e ∉ A)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (Fin n)) (x : Fin n → ℝ) (z : ℂ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    replacementDerivative M j A e ha hb S x z t =
      z*avg S (fun y => (M.delta j a b e y : ℂ)*(M.replacement j A e ha hb t ht).exponential z y) x := by
  unfold replacementDerivative
  apply congrArg (fun v : ℂ => z*v)
  apply congrArg (fun f => avg S f x)
  funext y
  unfold Model.exponential
  rw [M.replacement_total j A e he ha hb t ht y]
  push_cast
  rfl

@[simp] lemma replacementPath_zero (M : Model n m r c q) (j : Fin n)
    (A : Finset (Fin m)) (e : Fin m) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (Fin n)) (x : Fin n → ℝ) (z : ℂ) :
    replacementPath M j A e ha hb S x z 0 = (M.freezeSet j A ha hb).partial S z x := by
  simp only [replacementPath,Complex.ofReal_zero,zero_mul,add_zero,Model.partial]
  rfl

@[simp] lemma replacementPath_one (M : Model n m r c q) (j : Fin n)
    (A : Finset (Fin m)) (e : Fin m) (he : e ∉ A) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (Fin n)) (x : Fin n → ℝ) (z : ℂ) :
    replacementPath M j A e ha hb S x z 1 = (M.freezeSet j (insert e A) ha hb).partial S z x := by
  rw [replacementPath_eq_partial M j A e he ha hb S x z 1 (by constructor <;> norm_num)]
  unfold Model.partial
  apply congrArg (fun f => avg S f x)
  funext y
  unfold Model.exponential Model.replacement
  rw [Model.total_mix]
  norm_num

end Paper08.ZeroFreeInduction

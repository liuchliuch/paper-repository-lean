import PsgEst.AppendixScalar
import PsgEst.MatrixFreedmanProof
import PsgEst.TraceExponential

/-! A proof of scalar Freedman in the project's finite path coordinates.
The prefix conditional expectations are the actual weighted atom averages,
with the same zero-mass convention as `pathMatrixCondExp`. -/

open Matrix BigOperators Real Finset
namespace PsgEst
namespace ScalarFreedman

attribute [local instance] Classical.propDecidable

section FiniteConditioning
variable {Ω : Type*} [Fintype Ω]

noncomputable def atomMass (E : Ω → Ω → Prop) (w : Ω → ℝ) (x : Ω) : ℝ :=
  ∑ y ∈ univ.filter (E x), w y

noncomputable def atomCond (E : Ω → Ω → Prop) (w f : Ω → ℝ) (x : Ω) : ℝ :=
  (atomMass E w x)⁻¹ * ∑ y ∈ univ.filter (E x), w y * f y

lemma atom_filter_eq {E : Ω → Ω → Prop} (hE : Equivalence E) {x y : Ω} (hxy : E x y) :
    univ.filter (E x) = univ.filter (E y) := by
  ext z
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h => hE.trans (hE.symm hxy) h, fun h => hE.trans hxy h⟩

lemma atomMass_eq {E : Ω → Ω → Prop} (hE : Equivalence E) (w : Ω → ℝ)
    {x y : Ω} (hxy : E x y) : atomMass E w x = atomMass E w y := by
  unfold atomMass
  rw [atom_filter_eq hE hxy]

lemma atomCond_eq {E : Ω → Ω → Prop} (hE : Equivalence E) (w f : Ω → ℝ)
    {x y : Ω} (hxy : E x y) : atomCond E w f x = atomCond E w f y := by
  unfold atomCond atomMass
  rw [atom_filter_eq hE hxy]

lemma atomMass_nonneg (E : Ω → Ω → Prop) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (x : Ω) :
    0 ≤ atomMass E w x := sum_nonneg (fun y _ => hw y)

lemma weight_eq_zero_of_atomMass_zero (E : Ω → Ω → Prop) (w : Ω → ℝ)
    (hw : ∀ x, 0 ≤ w x) (x : Ω) (hx : atomMass E w x = 0)
    (y : Ω) (hxy : E x y) : w y = 0 := by
  have hy : y ∈ univ.filter (E x) := by simp [hxy]
  have hle : w y ≤ atomMass E w x := single_le_sum (fun z _ => hw z) hy
  rw [hx] at hle
  exact le_antisymm hle (hw y)

lemma atomCond_mono (E : Ω → Ω → Prop) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    {f g : Ω → ℝ} (hfg : ∀ x, f x ≤ g x) (x : Ω) :
    atomCond E w f x ≤ atomCond E w g x := by
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (atomMass_nonneg E w hw x))
  exact sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hfg y) (hw y))

lemma atomCond_nonneg (E : Ω → Ω → Prop) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) (x : Ω) : 0 ≤ atomCond E w f x :=
  mul_nonneg (inv_nonneg.mpr (atomMass_nonneg E w hw x))
    (sum_nonneg (fun y _ => mul_nonneg (hw y) (hf y)))

lemma atomCond_add (E : Ω → Ω → Prop) (w f g : Ω → ℝ) (x : Ω) :
    atomCond E w (fun y => f y + g y) x = atomCond E w f x + atomCond E w g x := by
  simp only [atomCond, mul_add, sum_add_distrib]

lemma atomCond_const_mul (E : Ω → Ω → Prop) (w f : Ω → ℝ) (c : ℝ) (x : Ω) :
    atomCond E w (fun y => c*f y) x = c*atomCond E w f x := by
  have hs : (∑ y ∈ univ.filter (E x), w y*(c*f y)) =
      c*(∑ y ∈ univ.filter (E x), w y*f y) := by
    rw [mul_sum]
    exact sum_congr rfl (fun y _ => by ring)
  unfold atomCond
  rw [hs]
  ring

lemma atomCond_one_le (E : Ω → Ω → Prop) (w : Ω → ℝ) (x : Ω) :
    atomCond E w (fun _ => 1) x ≤ 1 := by
  have he : atomCond E w (fun _ => 1) x = (atomMass E w x)⁻¹ * atomMass E w x := by
    simp [atomCond, atomMass]
  rw [he]
  by_cases h : atomMass E w x = 0
  · simp [h]
  · rw [inv_mul_cancel₀ h]

lemma atomCond_mul_atom (E : Ω → Ω → Prop) (w f g : Ω → ℝ) (x : Ω)
    (hf : ∀ y, E x y → f y = f x) :
    atomCond E w (fun y => f y*g y) x = f x*atomCond E w g x := by
  have hs : (∑ y ∈ univ.filter (E x), w y*(f y*g y)) =
      f x*(∑ y ∈ univ.filter (E x), w y*g y) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro y hy
    rw [hf y (mem_filter.mp hy).2]
    ring
  unfold atomCond
  rw [hs]
  ring

lemma atomCond_exp_le (E : Ω → Ω → Prop) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (X : Ω → ℝ) (θ g : ℝ)
    (hquad : ∀ y, exp (θ*X y) ≤ 1+θ*X y+g*(X y)^2)
    (x : Ω) (hmean : atomCond E w X x = 0) :
    atomCond E w (fun y => exp (θ*X y)) x ≤
      exp (g*atomCond E w (fun y => (X y)^2) x) := by
  have hle := atomCond_mono E w hw hquad x
  simp_rw [atomCond_add, atomCond_const_mul] at hle
  rw [hmean, mul_zero, add_zero] at hle
  have hone := atomCond_one_le E w x
  exact (hle.trans (add_le_add_right hone _)).trans (by
    simpa only [add_comm] using Real.add_one_le_exp
      (g*atomCond E w (fun y => (X y)^2) x))

end FiniteConditioning

section PrefixConditioning
variable {d m : ℕ}

/-- Scalar entry of the same finite prefix conditional expectation used in
matrix Freedman. -/
noncomputable def pathCond (Q : Stoch d) (mu : Fin d → ℝ) (t : ℕ)
    (f : (Fin (m+1) → Fin d) → ℝ) (Y : Fin (m+1) → Fin d) : ℝ :=
  atomCond (samePrefix t) (pathProb Q.P mu) f Y

lemma samePrefix_equivalence (t : ℕ) :
    Equivalence (samePrefix (d := d) (m := m) t) := by
  refine ⟨?_,?_,?_⟩
  · intro Y k hk; rfl
  · intro Y W h k hk; exact (h k hk).symm
  · intro X Y Z hxy hyz k hk; exact (hxy k hk).trans (hyz k hk)

lemma samePrefix_mono {s t : ℕ} (hst : s ≤ t) {Y W : Fin (m+1) → Fin d}
    (h : samePrefix t Y W) : samePrefix s Y W :=
  fun k hk => h k (hk.trans hst)

lemma pathCond_prefix (Q : Stoch d) (mu : Fin d → ℝ) (t : ℕ)
    (f : (Fin (m+1) → Fin d) → ℝ) {Y W : Fin (m+1) → Fin d}
    (h : samePrefix t Y W) : pathCond Q mu t f Y = pathCond Q mu t f W :=
  atomCond_eq (samePrefix_equivalence t) _ _ h

lemma pathMatrixCondExp_entry (Q : Stoch d) (mu : Fin d → ℝ) (t : ℕ)
    (M : (Fin (m+1) → Fin d) → Matrix (Fin 1) (Fin 1) ℝ)
    (Y : Fin (m+1) → Fin d) :
    pathMatrixCondExp Q mu t M Y 0 0 = pathCond Q mu t (fun W => M W 0 0) Y := by
  simp only [pathMatrixCondExp, pathCond, atomCond, atomMass, eventProb, pathMeasure,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]

lemma pathCond_eq_existing (Q : Stoch d) (mu : Fin d → ℝ) (t : ℕ)
    (f : (Fin (m+1) → Fin d) → ℝ) (Y : Fin (m+1) → Fin d) :
    pathCond Q mu t f Y = MatrixFreedman.pathScalarCondExp Q mu t f Y := rfl

/-- Finite initial sums keep the actual transition index. -/
noncomputable def partialSum (X : Fin m → (Fin (m+1) → Fin d) → ℝ)
    (k : ℕ) (Y : Fin (m+1) → Fin d) : ℝ :=
  ∑ t ∈ univ.filter (fun t : Fin m => t.val < k), X t Y

@[simp] lemma partialSum_zero (X : Fin m → (Fin (m+1) → Fin d) → ℝ) (Y) :
    partialSum X 0 Y = 0 := by simp [partialSum]

lemma partialSum_all (X : Fin m → (Fin (m+1) → Fin d) → ℝ) (Y) :
    partialSum X m Y = ∑ t, X t Y := by
  unfold partialSum
  have he : univ.filter (fun t : Fin m => t.val < m) = univ := by
    ext t; simp only [mem_filter, mem_univ, true_and]; exact iff_true_intro t.isLt
  rw [he]

lemma partialSum_succ (X : Fin m → (Fin (m+1) → Fin d) → ℝ)
    (k : ℕ) (hk : k < m) (Y) :
    partialSum X (k+1) Y = partialSum X k Y + X ⟨k,hk⟩ Y := by
  have he : univ.filter (fun t : Fin m => t.val < k+1) =
      insert ⟨k,hk⟩ (univ.filter (fun t : Fin m => t.val < k)) := by
    ext t
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
    omega
  have hn : (⟨k,hk⟩ : Fin m) ∉ univ.filter (fun t : Fin m => t.val < k) := by simp
  unfold partialSum
  rw [he, sum_insert hn]
  ring

lemma partialSum_prefix (X : Fin m → (Fin (m+1) → Fin d) → ℝ)
    (hX : ∀ t Y W, samePrefix (t.val+1) Y W → X t Y = X t W)
    (k : ℕ) {Y W} (h : samePrefix k Y W) : partialSum X k Y = partialSum X k W := by
  apply sum_congr rfl
  intro t ht
  exact hX t Y W (samePrefix_mono (by have := (mem_filter.mp ht).2; omega) h)

/-- The actual predictable scalar second moment of one increment. -/
noncomputable def varianceIncrement (Q : Stoch d) (mu : Fin d → ℝ)
    (X : Fin m → (Fin (m+1) → Fin d) → ℝ) (t : Fin m) (Y : Fin (m+1) → Fin d) : ℝ :=
  pathCond Q mu t.val (fun W => (X t W)^2) Y

lemma varianceIncrement_nonneg (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i) (X : Fin m → (Fin (m+1) → Fin d) → ℝ) (t) (Y) :
    0 ≤ varianceIncrement Q mu X t Y :=
  atomCond_nonneg _ _ (pathProb_nonneg Q.P mu Q.nonneg hmu) (fun _ => sq_nonneg _) Y

lemma varianceIncrement_prefix (Q : Stoch d) (mu : Fin d → ℝ)
    (X : Fin m → (Fin (m+1) → Fin d) → ℝ) (t : Fin m) {Y W}
    (h : samePrefix t.val Y W) :
    varianceIncrement Q mu X t Y = varianceIncrement Q mu X t W :=
  pathCond_prefix Q mu t.val _ h

lemma partialVariance_prefix (Q : Stoch d) (mu : Fin d → ℝ)
    (X : Fin m → (Fin (m+1) → Fin d) → ℝ) (k : ℕ) {Y W}
    (h : samePrefix k Y W) :
    partialSum (varianceIncrement Q mu X) k Y = partialSum (varianceIncrement Q mu X) k W := by
  apply sum_congr rfl
  intro t ht
  exact varianceIncrement_prefix Q mu X t
    (samePrefix_mono (Nat.le_of_lt (mem_filter.mp ht).2) h)

/-- The compensated exponential is evaluated on the original path, without
conditioning the path measure on the variation event. -/
noncomputable def potential (Q : Stoch d) (mu : Fin d → ℝ)
    (X : Fin m → (Fin (m+1) → Fin d) → ℝ) (θ g : ℝ) (k : ℕ) (Y : Fin (m+1) → Fin d) : ℝ :=
  exp (θ*partialSum X k Y-g*partialSum (varianceIncrement Q mu X) k Y)

lemma potential_step (Q : Stoch d) (mu : Fin d → ℝ)
    (X : Fin m → (Fin (m+1) → Fin d) → ℝ) (θ g : ℝ)
    (k : ℕ) (hk : k < m) (Y) :
    potential Q mu X θ g (k+1) Y =
      (potential Q mu X θ g k Y * exp (-g*varianceIncrement Q mu X ⟨k,hk⟩ Y)) *
        exp (θ*X ⟨k,hk⟩ Y) := by
  unfold potential
  rw [partialSum_succ X k hk, partialSum_succ _ k hk]
  rw [← exp_add, ← exp_add]
  congr 1
  ring

lemma potential_local (Q : Stoch d) (mu : Fin d → ℝ) (hmu : ∀ i, 0 ≤ mu i)
    (X : Fin m → (Fin (m+1) → Fin d) → ℝ)
    (hX : ∀ t Y W, samePrefix (t.val+1) Y W → X t Y = X t W)
    (hmean : ∀ t Y, pathCond Q mu t.val (X t) Y = 0)
    (θ g : ℝ) (_hg : 0 ≤ g)
    (hquad : ∀ t Y, exp (θ*X t Y) ≤ 1+θ*X t Y+g*(X t Y)^2)
    (k : ℕ) (hk : k < m) (Y) :
    pathCond Q mu k (potential Q mu X θ g (k+1)) Y ≤ potential Q mu X θ g k Y := by
  let t : Fin m := ⟨k,hk⟩
  let A := fun W => potential Q mu X θ g k W * exp (-g*varianceIncrement Q mu X t W)
  have hA (W) (h : samePrefix k Y W) : A W = A Y := by
    dsimp [A, potential]
    rw [partialSum_prefix X hX k h, partialVariance_prefix Q mu X k h,
      varianceIncrement_prefix Q mu X t h]
  have he : (fun W => potential Q mu X θ g (k+1) W) =
      (fun W => A W * exp (θ*X t W)) := by
    funext W; exact potential_step Q mu X θ g k hk W
  change pathCond Q mu k (fun W => potential Q mu X θ g (k+1) W) Y ≤ _
  rw [he]
  change atomCond (samePrefix k) (pathProb Q.P mu) _ Y ≤ _
  rw [atomCond_mul_atom _ _ A _ Y hA]
  have hmgf := atomCond_exp_le (samePrefix k) (pathProb Q.P mu)
    (pathProb_nonneg Q.P mu Q.nonneg hmu) (X t) θ g (hquad t) Y (hmean t Y)
  have hmul := mul_le_mul_of_nonneg_left hmgf (show 0 ≤ A Y by exact mul_nonneg (exp_pos _).le (exp_pos _).le)
  apply hmul.trans_eq
  dsimp [A]
  rw [mul_assoc, ← exp_add]
  change potential Q mu X θ g k Y * exp (-g*varianceIncrement Q mu X t Y+g*varianceIncrement Q mu X t Y) = _
  simp only [neg_mul, neg_add_cancel, exp_zero, mul_one]

/-- The true finite-path compensated exponential supermartingale bound. -/
theorem potential_expectation_le_one (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (X : Fin m → (Fin (m+1) → Fin d) → ℝ)
    (hX : ∀ t Y W, samePrefix (t.val+1) Y W → X t Y = X t W)
    (hmean : ∀ t Y, pathCond Q mu t.val (X t) Y = 0)
    (θ g : ℝ) (hg : 0 ≤ g)
    (hquad : ∀ t Y, exp (θ*X t Y) ≤ 1+θ*X t Y+g*(X t Y)^2) :
    MatrixFreedman.pathExpectation Q mu (potential Q mu X θ g m) ≤ 1 := by
  have h := MatrixFreedman.path_potential_expectation_le Q mu hmu m
    (potential Q mu X θ g) (fun k hk Y _ => by
      change pathCond Q mu k _ Y ≤ _
      exact potential_local Q mu hmu X hX hmean θ g hg hquad k hk Y)
  have hzero : MatrixFreedman.pathExpectation Q mu (potential Q mu X θ g 0) = 1 := by
    simpa [MatrixFreedman.pathExpectation, potential] using (pathProb_sum Q.P mu Q.row_stoch).trans hsum
  exact h.trans_eq hzero

/-- The one-sided scalar Freedman inequality, derived from the actual finite
conditional second moments and bounded increments. -/
theorem scalar_freedman_one_sided (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (X : Fin m → (Fin (m+1) → Fin d) → ℝ)
    (hX : ∀ t Y W, samePrefix (t.val+1) Y W → X t Y = X t W)
    (hmean : ∀ t Y, pathCond Q mu t.val (X t) Y = 0)
    (R : ℝ) (hR : 0 < R) (hbound : ∀ t Y, |X t Y| ≤ R)
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    eventProb Q.P mu (fun Y => u ≤ ∑ t, X t Y ∧
      (∑ t, varianceIncrement Q mu X t Y) ≤ v) ≤
      exp (-(u^2)/(2*(v+R*u/3))) := by
  let θ := MatrixFreedman.optimalTheta R u v
  let g := MatrixFreedman.bennettCoefficient R θ
  have hθ : 0 ≤ θ := (MatrixFreedman.optimalTheta_pos R u v hR hu hv).le
  have hg : 0 ≤ g := MatrixFreedman.bennettCoefficient_nonneg R θ
  have hquad (t) (Y) : exp (θ*X t Y) ≤ 1+θ*X t Y+g*(X t Y)^2 :=
    exp_quadratic_bennett θ R (X t Y) hθ hR (hbound t Y)
  have hpot := potential_expectation_le_one Q mu hmu hsum X hX hmean θ g hg hquad
  have h := MatrixFreedman.eventProb_le_freedman_of_potential Q mu hmu
    (potential Q mu X θ g m) (fun Y => (exp_pos _).le)
    (fun Y => u ≤ ∑ t, X t Y ∧ (∑ t, varianceIncrement Q mu X t Y) ≤ v)
    1 R u v (by norm_num) hR hu hv hpot (by
      intro Y hY
      apply Real.exp_le_exp.mpr
      dsimp only [potential]
      rw [partialSum_all, partialSum_all]
      exact sub_le_sub (mul_le_mul_of_nonneg_left hY.1 hθ)
        (mul_le_mul_of_nonneg_left hY.2 hg))
  simpa only [one_mul] using h

lemma pathCond_neg (Q : Stoch d) (mu : Fin d → ℝ) (t : ℕ)
    (X : (Fin (m+1) → Fin d) → ℝ) (Y) :
    pathCond Q mu t (fun W => -X W) Y = -pathCond Q mu t X Y := by
  simpa only [neg_one_mul] using atomCond_const_mul (samePrefix t) (pathProb Q.P mu) X (-1) Y

@[simp] lemma varianceIncrement_neg (Q : Stoch d) (mu : Fin d → ℝ)
    (X : Fin m → (Fin (m+1) → Fin d) → ℝ) (t) (Y) :
    varianceIncrement Q mu (fun t W => -X t W) t Y = varianceIncrement Q mu X t Y := by
  simp only [varianceIncrement, neg_sq]

/-- Two-sided scalar Freedman with the exact denominator `v+Ru/3`.
The variance in the event is the sum of the actual prefix conditional squares. -/
theorem scalar_freedman (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (X : Fin m → (Fin (m+1) → Fin d) → ℝ)
    (hX : ∀ t Y W, samePrefix (t.val+1) Y W → X t Y = X t W)
    (hmean : ∀ t Y, pathCond Q mu t.val (X t) Y = 0)
    (R : ℝ) (hR : 0 < R) (hbound : ∀ t Y, |X t Y| ≤ R)
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    eventProb Q.P mu (fun Y => u ≤ |∑ t, X t Y| ∧
      (∑ t, varianceIncrement Q mu X t Y) ≤ v) ≤
      2*exp (-(u^2)/(2*(v+R*u/3))) := by
  have hpos := scalar_freedman_one_sided Q mu hmu hsum X hX hmean R hR hbound u v hu hv
  have hneg := scalar_freedman_one_sided Q mu hmu hsum (fun t W => -X t W)
    (fun t Y W h => congrArg Neg.neg (hX t Y W h))
    (fun t Y => by rw [pathCond_neg, hmean, neg_zero])
    R hR (fun t Y => by simpa only [abs_neg] using hbound t Y) u v hu hv
  simp only [varianceIncrement_neg, sum_neg_distrib] at hneg
  have hsub : eventProb Q.P mu (fun Y => u ≤ |∑ t, X t Y| ∧
      (∑ t, varianceIncrement Q mu X t Y) ≤ v) ≤
      eventProb Q.P mu (fun Y =>
        (u ≤ ∑ t, X t Y ∧ (∑ t, varianceIncrement Q mu X t Y) ≤ v) ∨
        (u ≤ -(∑ t, X t Y) ∧ (∑ t, varianceIncrement Q mu X t Y) ≤ v)) := by
    apply eventProb_mono Q.P mu Q.nonneg hmu
    intro Y hY
    by_cases h : 0 ≤ ∑ t, X t Y
    · exact Or.inl ⟨by simpa only [abs_of_nonneg h] using hY.1, hY.2⟩
    · exact Or.inr ⟨by simpa only [abs_of_neg (lt_of_not_ge h)] using hY.1, hY.2⟩
  exact (hsub.trans (eventProb_or_le Q.P mu Q.nonneg hmu _ _)).trans
    (by linarith)

/-- In dimension one the Euclidean operator norm is the absolute entry. -/
theorem euclideanMatrixNorm_fin_one (M : Matrix (Fin 1) (Fin 1) ℝ) :
    euclideanMatrixNorm M = |M 0 0| := by
  have he : M = appendixScalarMatrix (M 0 0) := by
    ext a b
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst a; subst b
    simp only [appendixScalarMatrix_apply]
  have hupper := matrixEuclideanNorm_le_of_quadratic (appendixScalarMatrix (M 0 0))
    (appendixScalarMatrix_isHermitian _) |M 0 0| (abs_nonneg _) (by
      intro x
      simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_one, appendixScalarMatrix_apply]
      have h : x 0 * (M 0 0 * x 0) = M 0 0 * (x 0 * x 0) := by ring
      rw [h, abs_mul, abs_of_nonneg (mul_self_nonneg (x 0))] )
  apply le_antisymm
  · rw [he]
    simpa only [appendixScalarMatrix_apply, matrixEuclideanNorm, euclideanMatrixNorm] using hupper
  · rw [he]
    simpa only [appendixScalarMatrix_apply] using appendixScalarMatrix_abs_le_norm (M 0 0)

lemma martingaleSumNorm_fin_one (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin 1) (Fin 1) ℝ)
    (Y : Fin (m+1) → Fin d) :
    martingaleSumNorm Z Y = |∑ t, Z t Y 0 0| := by
  simp only [martingaleSumNorm, euclideanMatrixNorm_fin_one, Matrix.sum_apply]

lemma predictableVariationNorm_fin_one (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin 1) (Fin 1) ℝ)
    (Y : Fin (m+1) → Fin d) :
    predictableVariationNorm Q mu Z Y =
      ∑ t, varianceIncrement Q mu (fun t W => Z t W 0 0) t Y := by
  unfold predictableVariationNorm
  rw [euclideanMatrixNorm_fin_one]
  simp only [Matrix.sum_apply, pathMatrixCondExp_entry]
  have he : (∑ t : Fin m, pathCond Q mu t.val (fun W => (Z t W * Z t W) 0 0) Y) =
      ∑ t, varianceIncrement Q mu (fun t W => Z t W 0 0) t Y := by
    apply sum_congr rfl
    intro t _
    congr 2
    funext W
    simp only [Matrix.mul_apply, Fin.sum_univ_one, pow_two]
  rw [he, abs_of_nonneg (sum_nonneg (fun t _ => varianceIncrement_nonneg Q mu hmu _ t Y))]

/-- The original matrix Freedman statement in the case `D=1`, proved from
finite conditional expectations, bounded increments and their true squares. -/
theorem matrix_freedman_dim_one (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (R : ℝ) (hR : 0 < R)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin 1) (Fin 1) ℝ)
    (_hH : ∀ t Y, (Z t Y).IsHermitian)
    (hadapted : ∀ t Y W, samePrefix (t.val+1) Y W → Z t Y = Z t W)
    (hcenter : ∀ t Y, pathMatrixCondExp Q mu t.val (Z t) Y = 0)
    (hbound : ∀ t Y, euclideanMatrixNorm (Z t Y) ≤ R) :
    FreedmanJointInput Q mu 1 R (martingaleSumNorm Z) (predictableVariationNorm Q mu Z) := by
  intro u v hu hv
  have hmean (t : Fin m) (Y) : pathCond Q mu t.val (fun W => Z t W 0 0) Y = 0 := by
    rw [← pathMatrixCondExp_entry, hcenter]
    rfl
  have h := scalar_freedman Q mu hmu hsum (fun t W => Z t W 0 0)
    (fun t Y W h => congrArg (fun M : Matrix (Fin 1) (Fin 1) ℝ => M 0 0) (hadapted t Y W h))
    hmean R hR (fun t Y => by rw [← euclideanMatrixNorm_fin_one]; exact hbound t Y) u v hu hv
  simpa only [martingaleSumNorm_fin_one, predictableVariationNorm_fin_one Q mu hmu,
    Nat.cast_one, mul_one] using h

/-- Closed Freedman input for the actual Appendix A indicator process. -/
theorem appendixIndicator_freedman (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ a, 0 ≤ mu a) (hsum : ∑ a, mu a = 1) (i : Fin d) :
    FreedmanJointInput Q mu 1 1 (martingaleSumNorm (appendixIndicatorZ (m := m) Q i))
      (predictableVariationNorm Q mu (appendixIndicatorZ (m := m) Q i)) := by
  exact matrix_freedman_dim_one Q mu hmu hsum 1 (by norm_num) (appendixIndicatorZ Q i)
    (edgeIncrement_isHermitian Q _ (fun a b => (appendixIndicatorK_posSemidef i a b).isHermitian))
    (edgeIncrement_adapted Q _) (edgeIncrement_centered Q mu _)
    (appendixIndicator_increment_norm Q i)

/-- Appendix A single-residue count bound with no external concentration premise. -/
theorem appendix_visit_count_tail {d m : ℕ} (Q : Stoch d) (st : Stationary Q)
    (mu : Fin d → ℝ) (hmu : ∀ a, 0 ≤ mu a) (hsum : ∑ a, mu a = 1)
    (η : ℝ) (hη : 0 < η) (hη4 : η ≤ 1/4)
    (hentry : ∀ a b, |Q.P a b / st.mu b - 1| ≤ η/4) (i : Fin d)
    (hsize : 2/η ≤ (m+1 : ℕ)*st.mu i) :
    eventProb Q.P mu (fun Y : Fin (m+1) → Fin d =>
      η*(m+1 : ℕ)*st.mu i < |appendixVisitCount i Y - (m+1 : ℕ)*st.mu i|) ≤
      2*exp (-(η^2*(m+1 : ℕ)*st.mu i/36)) := by
  let N : ℝ := (m+1 : ℕ)*st.mu i
  have hN : 0 < N := mul_pos (Nat.cast_pos.mpr (by omega)) (st.pos i)
  let u : ℝ := η*N/4
  let v : ℝ := (1+η/4)*N
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hinc (Y : Fin (m+1) → Fin d)
      (hY : η*(m+1 : ℕ)*st.mu i < |appendixVisitCount i Y - (m+1 : ℕ)*st.mu i|) :
      u ≤ martingaleSumNorm (appendixIndicatorZ Q i) Y ∧
        predictableVariationNorm Q mu (appendixIndicatorZ Q i) Y ≤ v := by
    constructor
    · let S : ℝ := ∑ t : Fin m, (stateIndicator i (Y t.succ) - Q.P (Y t.castSucc) i)
      have hb := appendixIndicator_bias Q st η hη hentry i hsize Y
      have hdecomp := appendixVisitCount_decomposition Q i Y (st.mu i)
      have htri := abs_add_le S ((stateIndicator i (Y 0)-st.mu i) +
        ∑ t : Fin m, (Q.P (Y t.castSucc) i-st.mu i))
      have hS : u < |S| := by
        rw [hdecomp] at hY
        dsimp [u, N, S] at *
        have heq : (∑ t : Fin m, (stateIndicator i (Y t.succ) - Q.P (Y t.castSucc) i)) +
            (stateIndicator i (Y 0)-st.mu i) + ∑ t : Fin m, (Q.P (Y t.castSucc) i-st.mu i) =
            (∑ t : Fin m, (stateIndicator i (Y t.succ) - Q.P (Y t.castSucc) i)) +
            ((stateIndicator i (Y 0)-st.mu i) + ∑ t : Fin m, (Q.P (Y t.castSucc) i-st.mu i)) := by ring
        rw [heq] at hY
        nlinarith
      have hn := appendixScalarMatrix_abs_le_norm S
      have heq : (∑ t : Fin m, appendixIndicatorZ Q i t Y) = appendixScalarMatrix S :=
        appendixIndicator_sum Q i Y
      rw [← heq] at hn
      exact le_trans hS.le hn
    · simpa only [v, N, mul_assoc] using appendixIndicator_variation Q st mu η hη.le hentry i Y
  have hfree := appendixIndicator_freedman (m := m) Q mu hmu hsum i u v hu hv
  calc _ ≤ eventProb Q.P mu (fun Y : Fin (m+1) → Fin d =>
        u ≤ martingaleSumNorm (appendixIndicatorZ Q i) Y ∧
          predictableVariationNorm Q mu (appendixIndicatorZ Q i) Y ≤ v) :=
      eventProb_mono Q.P mu Q.nonneg hmu hinc
    _ ≤ 2*exp (-(u^2)/(2*(v+u/3))) := by simpa only [Nat.cast_one, mul_one, one_mul] using hfree
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      simpa only [u, v, N, mul_assoc, mul_pow] using appendix_scalar_exponent η N hη hη4 hN


end PrefixConditioning
end ScalarFreedman
end PsgEst

import PsgEst.Concentration
import PsgEst.ProbabilityThinning

/-!
# The edge martingale of Proposition 1

The elementary conditional-mean identity is proved from the finite Markov
path law. In particular no martingale or predictable-variation conclusion is
introduced as an additional hypothesis.
-/
open Matrix BigOperators Real Finset
open scoped InnerProductSpace
namespace PsgEst

attribute [local instance] Classical.propDecidable

/-- A transition-conditioned matrix mean. -/
noncomputable def edgeRowMean {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Stoch d) (K : Fin d → Fin d → Matrix ι ι ℝ) (i : Fin d) : Matrix ι ι ℝ :=
  ∑ j, Q.P i j • K i j

/-- Center one edge observation using its conditional transition mean. -/
noncomputable def centeredEdge {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Stoch d) (K : Fin d → Fin d → Matrix ι ι ℝ) (i j : Fin d) : Matrix ι ι ℝ :=
  K i j - edgeRowMean Q K i

lemma centeredEdge_row_zero {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Stoch d) (K : Fin d → Fin d → Matrix ι ι ℝ) (i : Fin d) :
    ∑ j, Q.P i j • centeredEdge Q K i j = 0 := by
  simp only [centeredEdge, smul_sub, sum_sub_distrib, ← sum_smul, Q.row_stoch, one_smul]
  exact sub_self _

lemma edgeRowMean_isHermitian {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Stoch d) (K : Fin d → Fin d → Matrix ι ι ℝ)
    (hK : ∀ i j, (K i j).IsHermitian) (i : Fin d) : (edgeRowMean Q K i).IsHermitian := by
  unfold edgeRowMean Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  apply sum_congr rfl
  intro j _
  rw [Matrix.conjTranspose_smul, hK i j]
  rfl

lemma centeredEdge_isHermitian {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Stoch d) (K : Fin d → Fin d → Matrix ι ι ℝ)
    (hK : ∀ i j, (K i j).IsHermitian) (i j : Fin d) : (centeredEdge Q K i j).IsHermitian :=
  (hK i j).sub (edgeRowMean_isHermitian Q K hK i)

/-- The increment at index `t` is revealed by the observation at time `t+1`. -/
noncomputable def edgeIncrement {d m : ℕ} {ι : Type*} [Fintype ι]
    (Q : Stoch d) (K : Fin d → Fin d → Matrix ι ι ℝ)
    (t : Fin m) (Y : Fin (m+1) → Fin d) : Matrix ι ι ℝ :=
  centeredEdge Q K (Y t.castSucc) (Y t.succ)

lemma edgeIncrement_adapted {d m : ℕ} {ι : Type*} [Fintype ι]
    (Q : Stoch d) (K : Fin d → Fin d → Matrix ι ι ℝ)
    (t : Fin m) (Y W : Fin (m+1) → Fin d) (h : samePrefix (t.val+1) Y W) :
    edgeIncrement Q K t Y = edgeIncrement Q K t W := by
  unfold edgeIncrement
  rw [h t.castSucc (by simp), h t.succ (by simp)]

lemma edgeIncrement_isHermitian {d m : ℕ} {ι : Type*} [Fintype ι]
    (Q : Stoch d) (K : Fin d → Fin d → Matrix ι ι ℝ)
    (hK : ∀ i j, (K i j).IsHermitian) (t : Fin m) (Y : Fin (m+1) → Fin d) :
    (edgeIncrement Q K t Y).IsHermitian := centeredEdge_isHermitian Q K hK _ _

/-- Integrating any centered scalar edge functional against any function of
the preceding path gives zero. This is the finite Markov martingale identity. -/
theorem markov_centered_edge_prefix_sum {d m : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (t : Fin m) (g : (Fin (t.val+1) → Fin d) → ℝ)
    (k : Fin d → Fin d → ℝ) :
    (∑ Y : Fin (m+1) → Fin d, pathProb Q.P mu Y *
      (g (pathPrefix (Nat.le_of_lt t.isLt) Y) *
        (k (Y t.castSucc) (Y t.succ) - ∑ j, Q.P (Y t.castSucc) j * k (Y t.castSucc) j))) = 0 := by
  classical
  let hstep : t.val+1 ≤ m := t.isLt
  let f : (Fin (t.val+2) → Fin d) → ℝ := fun B =>
    g (fun a => B a.castSucc) *
      (k (B (Fin.castSucc (Fin.last t.val))) (B (Fin.last (t.val+1))) -
        ∑ j, Q.P (B (Fin.castSucc (Fin.last t.val))) j * k (B (Fin.castSucc (Fin.last t.val))) j)
  have hrepr : ∀ Y : Fin (m+1) → Fin d,
      g (pathPrefix (Nat.le_of_lt t.isLt) Y) *
        (k (Y t.castSucc) (Y t.succ) - ∑ j, Q.P (Y t.castSucc) j * k (Y t.castSucc) j)
      = f (pathPrefix hstep Y) := by
    intro Y
    rfl
  simp_rw [hrepr]
  rw [pathPrefix_sum_of_le Q.P mu Q.row_stoch hstep f, sum_path_snoc]
  apply sum_eq_zero
  intro B _
  have hf (x : Fin d) : f (pathSnoc B x) =
      g B * (k (B (Fin.last t.val)) x - ∑ j, Q.P (B (Fin.last t.val)) j * k (B (Fin.last t.val)) j) := by
    dsimp [f]
    simp_rw [pathSnoc_castSucc, pathSnoc_last]
  simp_rw [pathProb_snoc, hf]
  have hscalar : ∑ x : Fin d, Q.P (B (Fin.last t.val)) x *
      (k (B (Fin.last t.val)) x - ∑ j, Q.P (B (Fin.last t.val)) j * k (B (Fin.last t.val)) j) = 0 := by
    simp_rw [mul_sub]
    rw [sum_sub_distrib, ← sum_mul, Q.row_stoch, one_mul, sub_self]
  calc
    _ = pathProb Q.P mu B * g B * (∑ x : Fin d, Q.P (B (Fin.last t.val)) x *
      (k (B (Fin.last t.val)) x - ∑ j, Q.P (B (Fin.last t.val)) j * k (B (Fin.last t.val)) j)) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro x _
      ring
    _ = 0 := by rw [hscalar, mul_zero]

lemma samePrefix_iff_prefix {d m : ℕ} (t : Fin m) (Y W : Fin (m+1) → Fin d) :
    samePrefix t.val Y W ↔ pathPrefix (Nat.le_of_lt t.isLt) Y =
      pathPrefix (Nat.le_of_lt t.isLt) W := by
  constructor
  · intro h
    funext i
    have hi := i.isLt
    have ht := t.isLt
    apply h ⟨i.val, by omega⟩
    change i.val ≤ t.val
    omega
  · intro h k hk
    exact congrFun h ⟨k.val, by omega⟩

/-- The weighted centered increment vanishes on every prefix atom. -/
theorem edgeIncrement_atom_sum_zero {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (K : Fin d → Fin d → Matrix (Fin D) (Fin D) ℝ)
    (t : Fin m) (Y : Fin (m+1) → Fin d) :
    (∑ W ∈ univ.filter (samePrefix t.val Y), pathProb Q.P mu W • edgeIncrement Q K t W) = 0 := by
  classical
  rw [sum_filter]
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, ite_apply]
  have h := markov_centered_edge_prefix_sum Q mu t
    (fun B => if pathPrefix (Nat.le_of_lt t.isLt) Y = B then 1 else 0)
    (fun i j => K i j a b)
  convert h using 1
  apply sum_congr rfl
  intro W _
  simp only [samePrefix_iff_prefix, edgeIncrement, centeredEdge, edgeRowMean,
    Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.sum_apply,
    smul_eq_mul, Matrix.zero_apply] <;> ring

/-- The actual increment has zero conditional expectation on every prefix
atom, including atoms with zero probability. -/
theorem edgeIncrement_centered {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (K : Fin d → Fin d → Matrix (Fin D) (Fin D) ℝ)
    (t : Fin m) (Y : Fin (m+1) → Fin d) :
    pathMatrixCondExp Q mu t.val (edgeIncrement Q K t) Y = 0 := by
  unfold pathMatrixCondExp
  rw [edgeIncrement_atom_sum_zero, smul_zero]

end PsgEst

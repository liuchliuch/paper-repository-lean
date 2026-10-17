import PsgEst.Basic

/-!
# Finite path-space probability for a Markov chain

The sample space is the finite set of trajectories `X : Fin (n+1) → Fin d`
with the Markov measure `μ0(X_0) ∏_t P(X_t, X_{t+1})`.
Probabilities of events are finite sums.  This is the setting of Theorems 1–2.
-/

open Matrix BigOperators Real Finset

namespace PsgEst

variable {d n : ℕ}

/-- Probability of a single trajectory under start law `mu0` and transition `P`. -/
noncomputable def pathProb {d n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (mu0 : Fin d → ℝ) (X : Fin (n + 1) → Fin d) : ℝ :=
  mu0 (X 0) * ∏ t : Fin n, P (X (Fin.castSucc t)) (X (Fin.succ t))

/-- Append a final state to a path of length `n+1`, producing a path of length `n+2`. -/
def pathSnoc {d n : ℕ} (Y : Fin (n + 1) → Fin d) (x : Fin d) : Fin (n + 2) → Fin d :=
  fun i => if h : i.val < n + 1 then Y ⟨i.val, h⟩ else x

lemma pathSnoc_zero {d n : ℕ} (Y : Fin (n + 1) → Fin d) (x : Fin d) :
    pathSnoc Y x 0 = Y 0 := by
  unfold pathSnoc
  have hpos : (0 : Fin (n + 2)).val < n + 1 := by simp
  rw [dif_pos hpos]
  show Y ⟨0, _⟩ = Y 0
  rfl

lemma pathSnoc_castSucc {d n : ℕ} (Y : Fin (n + 1) → Fin d) (x : Fin d)
    (t : Fin (n + 1)) :
    pathSnoc Y x (Fin.castSucc t) = Y t := by
  unfold pathSnoc
  have hpos : (Fin.castSucc t : Fin (n + 2)).val < n + 1 := by simp
  rw [dif_pos hpos]
  show Y ⟨t.val, _⟩ = Y t
  rfl

lemma pathSnoc_succ_castSucc {d n : ℕ} (Y : Fin (n + 1) → Fin d) (x : Fin d)
    (t : Fin n) :
    pathSnoc Y x (Fin.succ (Fin.castSucc t)) = Y (Fin.succ t) := by
  rw [Fin.succ_castSucc, pathSnoc_castSucc]

lemma pathSnoc_succ_last {d n : ℕ} (Y : Fin (n + 1) → Fin d) (x : Fin d) :
    pathSnoc Y x (Fin.succ (Fin.last n)) = x := by
  unfold pathSnoc
  have hneg : ¬(Fin.succ (Fin.last n) : Fin (n + 2)).val < n + 1 := by simp
  rw [dif_neg hneg]

lemma pathSnoc_castSucc_last {d n : ℕ} (Y : Fin (n + 1) → Fin d) (x : Fin d) :
    pathSnoc Y x (Fin.castSucc (Fin.last n)) = Y (Fin.last n) :=
  pathSnoc_castSucc Y x (Fin.last n)

lemma pathSnoc_last {d n : ℕ} (Y : Fin (n + 1) → Fin d) (x : Fin d) :
    pathSnoc Y x (Fin.last (n + 1)) = x := by
  unfold pathSnoc
  have hneg : ¬(Fin.last (n + 1) : Fin (n + 2)).val < n + 1 := by simp
  rw [dif_neg hneg]

/-- Every path of length `n+2` is `pathSnoc` of its prefix and last state. -/
lemma pathSnoc_init_last {d n : ℕ} (X : Fin (n + 2) → Fin d) :
    pathSnoc (fun t => X (Fin.castSucc t)) (X (Fin.last (n + 1))) = X := by
  funext i
  unfold pathSnoc
  by_cases h : i.val < n + 1
  · rw [dif_pos h]
    show X (Fin.castSucc ⟨i.val, h⟩) = X i
    rfl
  · rw [dif_neg h]
    have hi : i = Fin.last (n + 1) := by
      apply Fin.ext
      have : i.val = n + 1 := by omega
      rw [this]
      exact (Fin.val_last (n + 1)).symm
    rw [hi]

/-- Extending a path by one step multiplies the path probability by the last transition. -/
lemma pathProb_snoc {d n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (mu0 : Fin d → ℝ)
    (Y : Fin (n + 1) → Fin d) (x : Fin d) :
    pathProb P mu0 (pathSnoc Y x) = pathProb P mu0 Y * P (Y (Fin.last n)) x := by
  unfold pathProb
  have h0 : pathSnoc Y x 0 = Y 0 := pathSnoc_zero Y x
  have hprod :
      (∏ t : Fin (n + 1),
          P (pathSnoc Y x (Fin.castSucc t)) (pathSnoc Y x (Fin.succ t)))
        = (∏ t : Fin n, P (Y (Fin.castSucc t)) (Y (Fin.succ t)))
          * P (Y (Fin.last n)) x := by
    rw [Fin.prod_univ_castSucc]
    congr 1
    · apply Finset.prod_congr rfl
      intro t _
      rw [pathSnoc_castSucc, pathSnoc_succ_castSucc]
    · rw [pathSnoc_castSucc_last, pathSnoc_succ_last]
  rw [h0, hprod, mul_assoc]

/-- Total mass of the path measure is `∑_i mu0 i`. -/
theorem pathProb_sum (P : Matrix (Fin d) (Fin d) ℝ)
    (mu0 : Fin d → ℝ) (hrow : ∀ i, ∑ j, P i j = 1) :
    ∑ X : Fin (n + 1) → Fin d, pathProb P mu0 X = ∑ i, mu0 i := by
  induction n with
  | zero =>
    have hX : ∀ X : Fin 1 → Fin d, pathProb P mu0 X = mu0 (X 0) := by
      intro X
      unfold pathProb
      rw [Fintype.prod_empty, mul_one]
    have hsum : ∑ X : Fin 1 → Fin d, pathProb P mu0 X = ∑ X : Fin 1 → Fin d, mu0 (X 0) :=
      Finset.sum_congr rfl (fun X _ => hX X)
    rw [hsum, ← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin d)) mu0]
    rfl
  | succ n ih =>
    have hrew :
        ∑ X : Fin (n + 2) → Fin d, pathProb P mu0 X
          = ∑ Y : Fin (n + 1) → Fin d, ∑ x : Fin d, pathProb P mu0 (pathSnoc Y x) := by
      conv_rhs => rw [← Fintype.sum_prod_type']
      -- RHS is now ∑ p : (Fin (n+1) → Fin d) × Fin d, pathProb P mu0 (pathSnoc p.1 p.2)
      refine Finset.sum_bij
        (fun X _ => ((fun t => X (Fin.castSucc t)), X (Fin.last (n + 1))))
        (fun _ _ => by simp) ?_ ?_ ?_
      · intro X₁ _ X₂ _ h
        have h1 : (fun t => X₁ (Fin.castSucc t)) = (fun t => X₂ (Fin.castSucc t)) :=
          congrArg Prod.fst h
        have h2 : X₁ (Fin.last (n + 1)) = X₂ (Fin.last (n + 1)) :=
          congrArg Prod.snd h
        funext i
        by_cases hi : i.val < n + 1
        · have hi' : i = Fin.castSucc ⟨i.val, hi⟩ := Fin.ext (by simp)
          rw [hi']
          show X₁ (Fin.castSucc ⟨i.val, hi⟩) = X₂ (Fin.castSucc ⟨i.val, hi⟩)
          rw [← congrFun h1 ⟨i.val, hi⟩]
        · have hi' : i = Fin.last (n + 1) := by
            apply Fin.ext
            have : i.val = n + 1 := by omega
            rw [this]
            exact (Fin.val_last (n + 1)).symm
          rw [hi', h2]
      · rintro ⟨Y, x⟩ _
        refine ⟨pathSnoc Y x, by simp, ?_⟩
        simp only [Prod.mk.injEq]
        constructor
        · funext t
          exact pathSnoc_castSucc Y x t
        · exact pathSnoc_last Y x
      · intro X _
        rw [pathSnoc_init_last]
    rw [hrew]
    have hinner : ∀ Y : Fin (n + 1) → Fin d,
        ∑ x : Fin d, pathProb P mu0 (pathSnoc Y x) = pathProb P mu0 Y := by
      intro Y
      have h1 : ∀ x : Fin d, pathProb P mu0 (pathSnoc Y x)
          = pathProb P mu0 Y * P (Y (Fin.last n)) x := fun x => pathProb_snoc P mu0 Y x
      calc ∑ x : Fin d, pathProb P mu0 (pathSnoc Y x)
          = ∑ x : Fin d, pathProb P mu0 Y * P (Y (Fin.last n)) x :=
            Finset.sum_congr rfl (fun x _ => h1 x)
        _ = pathProb P mu0 Y := by
          rw [← Finset.mul_sum, hrow, mul_one]
    rw [Finset.sum_congr rfl (fun Y _ => hinner Y)]
    exact ih

/-- Probability of an event `E : Finset (Fin (n+1) → Fin d)`. -/
noncomputable def pathMeasure {d n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (mu0 : Fin d → ℝ) (E : Finset (Fin (n + 1) → Fin d)) : ℝ :=
  ∑ X ∈ E, pathProb P mu0 X

/-- Path probability is nonnegative under nonnegative data. -/
lemma pathProb_nonneg {d n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (mu0 : Fin d → ℝ) (hP : ∀ i j, 0 ≤ P i j) (hmu : ∀ i, 0 ≤ mu0 i)
    (X : Fin (n + 1) → Fin d) : 0 ≤ pathProb P mu0 X := by
  unfold pathProb
  apply mul_nonneg (hmu _)
  exact Finset.prod_nonneg fun t _ => hP _ _

/-- Nonnegativity. -/
theorem pathMeasure_nonneg (P : Matrix (Fin d) (Fin d) ℝ)
    (mu0 : Fin d → ℝ) (hP : ∀ i j, 0 ≤ P i j) (hmu : ∀ i, 0 ≤ mu0 i)
    (E : Finset (Fin (n + 1) → Fin d)) : 0 ≤ pathMeasure P mu0 E := by
  unfold pathMeasure
  exact Finset.sum_nonneg fun X _ => pathProb_nonneg P mu0 hP hmu X

/-- The infimum of a strictly positive vector on a nonempty finite type is positive. -/
lemma iInf_pos_of_forall_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (h : ∀ i, 0 < f i) : 0 < ⨅ i, f i := by
  obtain ⟨i₀, -, himin⟩ := Finset.exists_min_image
    (s := (Finset.univ : Finset ι)) (f := f) Finset.univ_nonempty
  have hle : f i₀ ≤ ⨅ i, f i := le_ciInf (fun j => himin j (Finset.mem_univ j))
  exact lt_of_lt_of_le (h i₀) hle

/-- Pointwise comparison of path probabilities under a change of initial law. -/
lemma pathProb_init_le {d n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (mu0 st : Fin d → ℝ) (hP : ∀ i j, 0 ≤ P i j) (hst : ∀ i, 0 < st i)
    (hmu : ∀ i, mu0 i ≤ st i / ⨅ j, st j)
    (X : Fin (n + 1) → Fin d) :
    pathProb P mu0 X ≤ pathProb P st X / (⨅ j, st j) := by
  haveI : Nonempty (Fin d) := ⟨X 0⟩
  have hπpos : 0 < ⨅ j, st j := iInf_pos_of_forall_pos st hst
  have hprod : 0 ≤ ∏ t : Fin n, P (X (Fin.castSucc t)) (X (Fin.succ t)) :=
    Finset.prod_nonneg fun t _ => hP _ _
  have hmu0 : mu0 (X 0) ≤ st (X 0) / ⨅ j, st j := hmu _
  unfold pathProb
  calc mu0 (X 0) * ∏ t : Fin n, P (X (Fin.castSucc t)) (X (Fin.succ t))
      ≤ (st (X 0) / ⨅ j, st j) * ∏ t : Fin n, P (X (Fin.castSucc t)) (X (Fin.succ t)) :=
    mul_le_mul_of_nonneg_right hmu0 hprod
    _ = (st (X 0) * ∏ t : Fin n, P (X (Fin.castSucc t)) (X (Fin.succ t))) / ⨅ j, st j := by
      rw [div_mul_eq_mul_div, mul_comm, mul_div_assoc]

/-- Comparison (11): `μ_i ≤ π_i / π_⋆` so `P_μ(E) ≤ P_π(E) / π_⋆`. -/
theorem pathMeasure_init_le (P : Matrix (Fin d) (Fin d) ℝ)
    (mu0 st : Fin d → ℝ) (hP : ∀ i j, 0 ≤ P i j) (hst : ∀ i, 0 < st i)
    (hmu : ∀ i, mu0 i ≤ st i / ⨅ j, st j)
    (E : Finset (Fin (n + 1) → Fin d)) :
    pathMeasure P mu0 E ≤ pathMeasure P st E / (⨅ j, st j) := by
  unfold pathMeasure
  have hpt : ∀ X ∈ E, pathProb P mu0 X ≤ pathProb P st X / (⨅ j, st j) :=
    fun X _ => pathProb_init_le P mu0 st hP hst hmu X
  calc ∑ X ∈ E, pathProb P mu0 X
      ≤ ∑ X ∈ E, pathProb P st X / (⨅ j, st j) := Finset.sum_le_sum hpt
    _ = (∑ X ∈ E, pathProb P st X) / (⨅ j, st j) := by
      rw [Finset.sum_div]

/-- Relative entropy between two path measures (natural log). -/
noncomputable def pathKL {d n : ℕ} (P Q : Matrix (Fin d) (Fin d) ℝ)
    (mu0 nu0 : Fin d → ℝ) : ℝ :=
  ∑ X : Fin (n + 1) → Fin d,
    let p := pathProb P mu0 X
    let q := pathProb Q nu0 X
    if p = 0 then 0 else p * log (p / q)

end PsgEst

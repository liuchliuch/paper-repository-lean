import Paper28.FoldingDifferential

/-! Explicit orthogonal coordinate decomposition for cutting one distinguished
edge between two sets of coordinates. It is a native linear isometry. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open WithLp
variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]

/-- Reindex finite edge coordinates as the three Hilbert blocks `(x,z,y)`. -/
def coordinateTriple (e : α ⊕ (Unit ⊕ β) ≃ ι) :
    EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] Triple (EuclideanSpace ℝ α) (EuclideanSpace ℝ β) where
  toFun u := toLp 2 (toLp 2 (fun a => u (e (.inl a))),
    toLp 2 (u (e (.inr (.inl ()))), toLp 2 (fun b => u (e (.inr (.inr b))))))
  invFun v := toLp 2 fun i => Sum.elim (fun a => v.fst a)
    (Sum.elim (fun _ => v.snd.fst) (fun b => v.snd.snd b)) (e.symm i)
  left_inv u := by
    ext i
    change Sum.elim _ (Sum.elim _ _) (e.symm i) = u i
    obtain ⟨j, rfl⟩ := e.surjective i
    simp only [Equiv.symm_apply_apply]
    rcases j with a | j
    · rfl
    · rcases j with z | b
      · cases z
        rfl
      · rfl
  right_inv v := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · ext a
      simp
    · apply (WithLp.equiv 2 _).injective
      apply Prod.ext
      · simp
      · ext b
        simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' u := by
    have hs : (∑ j, (u (e j)) ^ 2) = ∑ i, u i ^ 2 :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    simp only [Fintype.sum_sum_type, Fintype.sum_unique] at hs
    have hsq : ‖toLp 2 (toLp 2 (fun a => u (e (.inl a))),
        toLp 2 (u (e (.inr (.inl ()))), toLp 2 (fun b => u (e (.inr (.inr b))))))‖ ^ 2 =
        ‖u‖ ^ 2 := by
      simp only [prod_norm_sq_eq_of_L2, toLp_fst, toLp_snd,
        EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
      exact hs
    change ‖toLp 2 (toLp 2 (fun a => u (e (.inl a))),
      toLp 2 (u (e (.inr (.inl ()))), toLp 2 (fun b => u (e (.inr (.inr b))))))‖ = ‖u‖
    nlinarith [norm_nonneg u,
      norm_nonneg (toLp 2 (toLp 2 (fun a => u (e (.inl a))),
        toLp 2 (u (e (.inr (.inl ()))), toLp 2 (fun b => u (e (.inr (.inr b)))))))]

/-- Reindex a retained tree as its strict coordinates and its terminal edge. -/
def coordinatePair (e : α ⊕ Unit ≃ ι) :
    EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] WithLp 2 (EuclideanSpace ℝ α × ℝ) where
  toFun u := toLp 2 (toLp 2 (fun a => u (e (.inl a))), u (e (.inr ())))
  invFun v := toLp 2 fun i => Sum.elim (fun a => v.fst a) (fun _ => v.snd) (e.symm i)
  left_inv u := by
    ext i
    obtain ⟨j, rfl⟩ := e.surjective i
    change Sum.elim _ _ (e.symm (e j)) = u (e j)
    rw [e.symm_apply_apply]
    rcases j with a | z
    · rfl
    · cases z
      rfl
  right_inv v := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · ext a
      simp
    · simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' u := by
    have hs : (∑ j, (u (e j)) ^ 2) = ∑ i, u i ^ 2 :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    simp only [Fintype.sum_sum_type, Fintype.sum_unique] at hs
    have hsq : ‖toLp 2 (toLp 2 (fun a => u (e (.inl a))), u (e (.inr ())))‖ ^ 2 =
        ‖u‖ ^ 2 := by
      simp only [prod_norm_sq_eq_of_L2, toLp_fst, toLp_snd,
        EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
      exact hs
    change ‖toLp 2 (toLp 2 (fun a => u (e (.inl a))), u (e (.inr ())))‖ = ‖u‖
    nlinarith [norm_nonneg u,
      norm_nonneg (toLp 2 (toLp 2 (fun a => u (e (.inl a))), u (e (.inr ()))))]

@[simp] theorem coordinatePair_fst (e : α ⊕ Unit ≃ ι) (u : EuclideanSpace ℝ ι) (a : α) :
    (coordinatePair e u).fst a = u (e (.inl a)) := rfl

@[simp] theorem coordinatePair_snd (e : α ⊕ Unit ≃ ι) (u : EuclideanSpace ℝ ι) :
    (coordinatePair e u).snd = u (e (.inr ())) := rfl

@[simp] theorem coordinateTriple_fst (e : α ⊕ (Unit ⊕ β) ≃ ι)
    (u : EuclideanSpace ℝ ι) (a : α) :
    (coordinateTriple e u).fst a = u (e (.inl a)) := rfl

@[simp] theorem coordinateTriple_snd_fst (e : α ⊕ (Unit ⊕ β) ≃ ι)
    (u : EuclideanSpace ℝ ι) : (coordinateTriple e u).snd.fst = u (e (.inr (.inl ()))) := rfl

@[simp] theorem coordinateTriple_snd_snd (e : α ⊕ (Unit ⊕ β) ≃ ι)
    (u : EuclideanSpace ℝ ι) (b : β) :
    (coordinateTriple e u).snd.snd b = u (e (.inr (.inr b))) := rfl

end Paper28

import Paper12.OneHotState

noncomputable section
namespace Paper12
open Matrix Classical

def oneBitBasis (v : Fin 2) : Basis (Fin 1) := fun _ => v

def oneBitEquiv : Basis (Fin 1) ≃ Fin 2 where
  toFun b := b 0
  invFun := oneBitBasis
  left_inv b := by funext x; have hx : x = 0 := Fin.eq_zero x; subst x; rfl
  right_inv _ := rfl

theorem sum_oneBit {A : Type*} [AddCommMonoid A] (f : Basis (Fin 1) → A) :
    (∑ b : Basis (Fin 1), f b) = f (oneBitBasis 0) + f (oneBitBasis 1) := by
  rw [← Equiv.sum_comp oneBitEquiv.symm, Fin.sum_univ_two]
  rfl

theorem ry_oneBit_entry (θ : ℝ) (i j : Basis (Fin 1)) :
    (singleCircuit (ryGate (0 : Fin 1) θ)).unitary i j =
      realRotation (Real.cos (θ / 2)) (Real.sin (θ / 2)) (i 0) (j 0) := by
  rw [singleCircuit_unitary]
  simp only [ryGate, Gate.unitary, OneQubit.unitary, Matrix.of_apply]
  rw [if_pos (by intro w hw; exact (hw (Fin.eq_zero w)).elim)]

def kickbackC : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ)

theorem kickbackC_sq : kickbackC ^ 2 = (1 / 2 : ℂ) := by
  have hr : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  unfold kickbackC
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hr
  simpa only [_root_.Complex.ofReal_pow, _root_.Complex.ofReal_div,
    _root_.Complex.ofReal_ofNat] using hc

theorem ry_prepare_minus :
    applyOp (singleCircuit (ryGate (0 : Fin 1) (-Real.pi / 2))).unitary (zeroKet _) = signedKet kickbackC := by
  funext b
  rw [show zeroKet (Fin 1) = eBasis (fun _ => 0) from rfl, applyOp_eBasis, ry_oneBit_entry]
  have hc : Real.cos ((-Real.pi / 2) / 2) = Real.sqrt 2 / 2 := by
    rw [show (-Real.pi / 2) / 2 = -(Real.pi / 4) by ring, Real.cos_neg, Real.cos_pi_div_four]
  have hs : Real.sin ((-Real.pi / 2) / 2) = -(Real.sqrt 2 / 2) := by
    rw [show (-Real.pi / 2) / 2 = -(Real.pi / 4) by ring, Real.sin_neg, Real.sin_pi_div_four]
  rw [hc, hs]
  generalize hb : b 0 = v
  fin_cases v <;> simp [realRotation, signedKet, hb, kickbackC]

theorem ry_reset_minus :
    applyOp (singleCircuit (ryGate (0 : Fin 1) (Real.pi / 2))).unitary (signedKet kickbackC) = zeroKet _ := by
  funext b
  have hz : b = (fun _ : Fin 1 => (0 : Fin 2)) ↔ b 0 = 0 := by
    constructor
    · intro h; exact congrFun h 0
    · intro h
      funext x
      have hx : x = 0 := Fin.eq_zero x
      subst x; exact h
  simp only [applyOp]
  rw [sum_oneBit]
  simp only [ry_oneBit_entry]
  have hc : Real.cos ((Real.pi / 2) / 2) = Real.sqrt 2 / 2 := by
    rw [show (Real.pi / 2) / 2 = Real.pi / 4 by ring, Real.cos_pi_div_four]
  have hs : Real.sin ((Real.pi / 2) / 2) = Real.sqrt 2 / 2 := by
    rw [show (Real.pi / 2) / 2 = Real.pi / 4 by ring, Real.sin_pi_div_four]
  rw [hc, hs]
  simp only [zeroKet, eBasis, hz]
  generalize hb : b 0 = v
  have hsqrt : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  fin_cases v <;> simp [realRotation, oneBitBasis, signedKet, kickbackC] <;>
    linear_combination hsqrt / 2

theorem OneQubit.right_unitary {J K : Type*} [Fintype J] [Fintype K] (g : OneQubit K) :
    (Gate.one (⟨Sum.inr g.wire, g.u, g.isUnitary⟩ : OneQubit (J ⊕ K))).unitary =
      registerTensor (1 : Op J) g.unitary := by
  simp only [Gate.unitary]
  rw [← tensor_atWire (⟨Sum.inr g.wire, g.u, g.isUnitary⟩ : OneQubit (J ⊕ K))]
  have hm : atWire (Sum.inr g.wire) g.u =
      Sum.elim (fun _ : J => (1 : QMat)) (atWire g.wire g.u) := by
    funext x
    cases x with
    | inl x => simp [atWire]
    | inr x =>
      by_cases hx : x = g.wire
      · subst x; simp [atWire]
      · simp [atWire, hx]
  rw [hm, tensorOp_sum]
  have hI : tensorOp (fun _ : J => (1 : QMat)) = (1 : Op J) := tensorOp_one
  rw [hI, tensor_atWire]

theorem flip_adjustment_zero :
    applyOp (Gate.one (⟨1, pmat .X, pmat_unitary .X⟩ : OneQubit (Fin 2))).unitary
      (eBasis (oneHot (1 : Fin 2))) = zeroKet _ := by
  funext b
  rw [applyOp_eBasis]
  have hoff : (∀ w : Fin 2, w ≠ 1 → b w = oneHot (1 : Fin 2) w) ↔ b 0 = 0 := by
    constructor
    · intro h; simpa [oneHot] using h 0 (by decide)
    · intro h w hw
      fin_cases w
      · simpa [oneHot] using h
      · exact (hw rfl).elim
  have hz : b = (fun _ : Fin 2 => (0 : Fin 2)) ↔ b 0 = 0 ∧ b 1 = 0 := by
    constructor
    · intro h; exact ⟨congrFun h 0, congrFun h 1⟩
    · rintro ⟨h0, h1⟩
      funext x; fin_cases x <;> assumption
  simp only [Gate.unitary, OneQubit.unitary, Matrix.of_apply]
  simp only [hoff, oneHot_apply_eq, zeroKet, eBasis, hz]
  generalize h0 : b 0 = v0
  generalize h1 : b 1 = v1
  fin_cases v0 <;> fin_cases v1 <;> simp [pmat]
end Paper12

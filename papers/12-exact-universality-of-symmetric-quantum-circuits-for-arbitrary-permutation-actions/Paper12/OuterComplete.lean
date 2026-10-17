import Paper12.OuterState

noncomputable section
namespace Paper12
open Matrix Classical
variable {X W : Type*} [Fintype X] [Fintype W]

theorem registerVec_smul_left {J K : Type*} [Fintype J] [Fintype K]
    (z : ℂ) (ψ : Vec J) (χ : Vec K) : registerVec (z • ψ) χ = z • registerVec ψ χ := by
  funext b
  exact mul_assoc _ _ _

theorem outer_vector_recovery (A : Circuit (X ⊕ W)) (V : Op X) (p : ℝ)
    (hV : Vᴴ * V = 1) (hp : 0 < p) (hb : BlockEncodes A.unitary p V) (ψ : Vec X) :
    applyOp ((RS (outerStartMap A p) * RG (outerProjector (X := X) (W := W))) ^ ampK p)
      (applyOp (outerT A p).unitary (embedZero (W := W ⊕ Fin 1) ψ)) =
      ((-1 : ℂ) ^ ampK p) • embedZero (W := W ⊕ Fin 1) (applyOp V ψ) := by
  have h := congrArg (fun M => M * column ψ) (outer_matrix_recovery A V p hV hp hb)
  simp only [outerStartMap, outerGoodMap, Matrix.smul_mul, Matrix.mul_assoc,
    zeroEmbed_column, column_apply] at h
  funext b
  exact congrFun (congrFun h b) ()

theorem outerRaw_clean (A : Circuit (X ⊕ W)) (V : Op X) (p : ℝ)
    (hV : Vᴴ * V = 1) (hp : 0 < p) (hb : BlockEncodes A.unitary p V) (ψ : Vec X) :
    applyOp (outerRaw A p).unitary
      (registerVec (embedZero (W := W ⊕ Fin 1) ψ) (zeroKet (Fin 1))) =
      registerVec (embedZero (W := W ⊕ Fin 1) (applyOp V ψ)) (zeroKet (Fin 1)) := by
  let D := X ⊕ (W ⊕ Fin 1)
  let v := embedZero (W := W ⊕ Fin 1) ψ
  let g := embedZero (W := W ⊕ Fin 1) (applyOp V ψ)
  let s : ℂ := (-1 : ℂ) ^ ampK p
  have hZP : applyOp ((singleCircuit (ryGate (0 : Fin 1) (-Real.pi / 2))).onRight (J := D)).unitary
      (registerVec v (zeroKet (Fin 1))) = registerVec v (signedKet kickbackC) := by
    rw [Circuit.onRight_unitary, registerTensor_apply, applyOp_one, ry_prepare_minus]
  have hT : applyOp ((outerT A p).onLeft (K := Fin 1)).unitary
      (registerVec v (signedKet kickbackC)) =
      registerVec (applyOp (outerT A p).unitary v) (signedKet kickbackC) := by
    rw [Circuit.onLeft_unitary, extendLeft, registerTensor_apply, applyOp_one]
  have hI : applyOp ((outerIteration A p).power (ampK p)).unitary
      (registerVec (applyOp (outerT A p).unitary v) (signedKet kickbackC)) =
      registerVec (s • g) (signedKet kickbackC) := by
    rw [Circuit.power_unitary, (outerIteration_simulates A p kickbackC).power (ampK p),
      outer_vector_recovery A V p hV hp hb]
  have hZR : applyOp ((singleCircuit (ryGate (0 : Fin 1) (Real.pi / 2))).onRight (J := D)).unitary
      (registerVec (s • g) (signedKet kickbackC)) =
      registerVec (s • g) (zeroKet (Fin 1)) := by
    rw [Circuit.onRight_unitary, registerTensor_apply, applyOp_one, ry_reset_minus]
  have hs : s * s = 1 := by
    unfold s
    rw [← mul_pow]
    norm_num
  simp only [outerRaw, Circuit.mul_unitary]
  rw [applyOp_mul, applyOp_mul, applyOp_mul, applyOp_mul, hZP, hT, hI, hZR]
  rw [singleCircuit_unitary, phaseGate_unitary, applyOp_smul, applyOp_one,
    registerVec_smul_left, smul_smul, hs, one_smul]

theorem outerWire_clean (ψ : Vec X) :
    rewireVec (outerWireEquiv (X := X) (W := W))
      (registerVec (embedZero (W := W ⊕ Fin 1) ψ) (zeroKet (Fin 1))) =
      embedZero (W := W ⊕ Fin 2) ψ := by
  simp only [embedZero_registerVec]
  rw [outerWireEquiv, rewireVec_trans, rewireVec_trans, rewireVec_assoc,
    registerVec_zero, rewireVec_sum_generic, rewireVec_zero,
    rewireVec_sum_generic, rewireVec_zero]
  rfl

/-- Exact oblivious amplification by the literal circuit (22), with both new
workspace lines clean and the sign (-1)^K corrected by a permitted one-qubit gate. -/
theorem obliviousCircuit_clean (A : Circuit (X ⊕ W)) (V : Op X) (p : ℝ)
    (hV : Vᴴ * V = 1) (hp : 0 < p) (hb : BlockEncodes A.unitary p V) :
    CleanImplements (obliviousCircuit A p) V := by
  intro ψ
  have hinput := (outerWire_clean (W := W) ψ).symm
  rw [obliviousCircuit, Circuit.rewire_unitary, hinput, rewire_apply,
    outerRaw_clean A V p hV hp hb, outerWire_clean]

theorem lemma_4_1_actual {Γ : Subgroup (X ≃ X)} (A : Circuit (X ⊕ W)) (V : Op X) (p : ℝ)
    (hV : Vᴴ * V = 1) (hsym : Symmetric Γ A) (hp : 0 < p) (_hp1 : p < 1)
    (hb : BlockEncodes A.unitary p V) :
    ∃ C : Circuit (X ⊕ (W ⊕ Fin 2)),
      C.size ≤ 32 * (A.size + 1) * (ampK p + 1) ∧
      Nonempty (Symmetric Γ C) ∧ CleanImplements C V ∧
      ∀ (γ : X ≃ X) (e : (X ⊕ W) ≃ (X ⊕ W)),
        (∀ x, e (Sum.inl x) = Sum.inl (γ x)) → A.Preserved e →
        C.Preserved (outerFinalLift e) :=
  ⟨obliviousCircuit A p, obliviousCircuit_size A p, obliviousCircuit_symmetric hsym p,
    obliviousCircuit_clean A V p hV hp hb, obliviousCircuit_preserved A p⟩
end Paper12

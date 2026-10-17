import Paper12.OneHotState

noncomputable section
set_option maxHeartbeats 2000000
namespace Paper12
open Matrix Classical
variable {X : Type*} [Fintype X]

theorem hammingWeight_eq_zero {J : Type*} [Fintype J] (b : Basis J) :
    hammingWeight b = 0 ↔ b = fun _ => 0 := by
  constructor
  · intro h
    funext x
    have hx := Finset.single_le_sum (s := Finset.univ) (f := fun x => (b x : ℕ))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
    change _ ≤ hammingWeight b at hx
    rw [h] at hx
    exact Fin.ext (Nat.eq_zero_of_le_zero hx)
  · intro h; subst b; simp [hammingWeight]

theorem fin2_add_eq_two (a b : Fin 2) :
    (a : ℕ) + (b : ℕ) = 2 ↔ a = 1 ∧ b = 1 := by
  fin_cases a <;> fin_cases b <;> decide

theorem prepD_good_predicate (α : Coeffs X) (b : Basis (SelectorWire α ⊕ Fin 2)) :
    (∑ x ∈ ({Sum.inr 0, Sum.inr 1} : Finset (SelectorWire α ⊕ Fin 2)),
      (equalityAct (prepWeightTest α) b x : ℕ)) = 2 ↔ prepGood α b := by
  have hc : (∑ x ∈ (prepWeightTest α).controls, (b x : ℕ)) =
      hammingWeight (b ∘ Sum.inl) := by
    simp only [prepWeightTest, Finset.sum_map, Function.Embedding.inl_apply,
      hammingWeight, Function.comp_apply]
  simp only [equalityAct, hc]
  simp only [prepWeightTest]
  by_cases hw : hammingWeight (b ∘ Sum.inl) = 1
  · simp [hw, prepGood, fin2_add_eq_two]
  · simp [hw, prepGood, fin2_add_eq_two]

theorem matrix_eq_of_apply {J : Type*} [Fintype J] {A B : Op J}
    (h : ∀ ψ : Vec J, applyOp A ψ = applyOp B ψ) : A = B := by
  ext i j
  have hh := congrFun (h (eBasis j)) i
  simpa only [applyOp_eBasis] using hh

theorem prepFG_data (α : Coeffs X) :
    (prepD α).unitary * phaseMatrix (fun b =>
      (∑ x ∈ ({Sum.inr 0, Sum.inr 1} : Finset (SelectorWire α ⊕ Fin 2)), (b x : ℕ)) = 2) *
        (prepD α).unitary = phaseMatrix (prepGood α) := by
  apply matrix_eq_of_apply
  intro ψ
  rw [applyOp_mul, applyOp_mul, phaseMatrix_apply, phaseMatrix_apply]
  funext b
  rw [show prepD α = equalityCircuit (prepWeightTest α) from rfl, equalityCircuit_apply]
  simp only [phaseOn]
  simp only [equalityCircuit_apply, prepD_good_predicate]
  rw [equalityAct_involutive (prepWeightTest α) b]

theorem prepFG_simulates (α : Coeffs X) (c : ℂ) :
    KickbackSimulates c (prepFG α).unitary (RG (prepProjector α)) := by
  have hD : KickbackSimulates c (prepD α).onLeft.unitary (prepD α).unitary := by
    rw [Circuit.onLeft_unitary]
    exact kickback_extendLeft c _
  have hE := kickback_equality c ({Sum.inr 0, Sum.inr 1} : Finset (SelectorWire α ⊕ Fin 2)) 2
  have h := hD.mul (hE.mul hD)
  simp only [prepFG, Circuit.mul_unitary] at h ⊢
  have hd : (prepD α).unitary * (phaseMatrix (fun b =>
      (∑ x ∈ ({Sum.inr 0, Sum.inr 1} : Finset (SelectorWire α ⊕ Fin 2)), (b x : ℕ)) = 2) *
        (prepD α).unitary) = RG (prepProjector α) := by
    rw [← Matrix.mul_assoc, prepFG_data, phaseMatrix_reflect]
    rfl
  rw [hd] at h
  exact h

theorem conjugate_reflectRange {J K : Type*} [Fintype J] [Fintype K]
    [DecidableEq J] [DecidableEq K] (T : Matrix J J ℂ) (E : Matrix J K ℂ)
    (hT : T * Tᴴ = 1) : T * reflectRange E * Tᴴ = reflectRange (T * E) := by
  simp only [reflectRange, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_mul]
  rw [hT]
  simp only [Matrix.mul_assoc]

theorem prepF0_simulates (α : Coeffs X) (c : ℂ) :
    KickbackSimulates c (prepF0 α).unitary (reflectRange (column (zeroKet (SelectorWire α ⊕ Fin 2)))) := by
  have h := kickback_equality c (Finset.univ : Finset (SelectorWire α ⊕ Fin 2)) 0
  have hp : (fun b : Basis (SelectorWire α ⊕ Fin 2) =>
      (∑ x ∈ (Finset.univ : Finset (SelectorWire α ⊕ Fin 2)), (b x : ℕ)) = 0) =
      (fun b => b = fun _ => 0) := by
    funext b
    exact propext (hammingWeight_eq_zero b)
  rw [hp, phaseMatrix_reflect, ← zeroKet_projector] at h
  exact h

theorem prepIteration_simulates (α : Coeffs X) (c : ℂ) :
    KickbackSimulates c (prepIteration α).unitary
      (RS (column (prepStart α)) * RG (prepProjector α)) := by
  have hT : KickbackSimulates c (prepT α).onLeft.unitary (prepT α).unitary := by
    rw [Circuit.onLeft_unitary]
    exact kickback_extendLeft c _
  have hTA : KickbackSimulates c (prepT α).onLeft.adjoint.unitary (prepT α).unitaryᴴ := by
    rw [Circuit.adjoint_unitary]
    exact KickbackSimulates.adjoint (Circuit.unitary_isUnitary _) (Circuit.unitary_isUnitary _) hT
  have h := hT.mul ((prepF0_simulates α c).mul (hTA.mul (prepFG_simulates α c)))
  simp only [prepIteration, Circuit.mul_unitary] at h ⊢
  have hconj := conjugate_reflectRange (prepT α).unitary (column (zeroKet _))
    (Matrix.mul_eq_one_comm.mp (Circuit.unitary_isUnitary (prepT α)))
  rw [column_apply] at hconj
  change (prepT α).unitary * reflectRange (column (zeroKet _)) * (prepT α).unitaryᴴ =
    RS (column (prepStart α)) at hconj
  have hd : (prepT α).unitary * (reflectRange (column (zeroKet _)) *
      ((prepT α).unitaryᴴ * RG (prepProjector α))) =
      RS (column (prepStart α)) * RG (prepProjector α) := by
    calc _ = ((prepT α).unitary * reflectRange (column (zeroKet _)) *
        (prepT α).unitaryᴴ) * RG (prepProjector α) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hconj]
  rw [hd] at h
  exact h

theorem prep_two_iterations (α : Coeffs X) (hmass : 0 < coeffMass α) :
    applyOp ((RS (column (prepStart α)) * RG (prepProjector α)) ^ 2) (prepStart α) = prepGoodVec α := by
  have D : TwoReflectionData theta0 (prepProjector α) (column (prepStart α)) (column (prepGoodVec α)) := {
    proj := predicateProjector_orthogonal _
    isoS := prepStart_isometry α
    isoG := column_isometry _ (prepGoodVec_inner α hmass)
    angle := ⟨theta0_pos, theta0_lt_pi_div_two⟩
    key := by rw [column_apply, prep_project_start α hmass]; rfl }
  have h := two_reflection_identity D 2
  norm_num only at h
  have h5 : (5 : ℝ) * theta0 = Real.pi / 2 := five_theta0
  rw [h5, Real.sin_pi_div_two, Real.cos_pi_div_two] at h
  have hmat : (RS (column (prepStart α)) * RG (prepProjector α)) ^ 2 * column (prepStart α) =
      column (prepGoodVec α) := by simpa using h
  rw [column_apply] at hmat
  funext b
  exact congrFun (congrFun hmat b) ()
end Paper12

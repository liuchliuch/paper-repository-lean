import Paper12.OuterSymmetry
import Paper12.OneHotComplete
import Paper12.ZeroEmbedding

noncomputable section
namespace Paper12
open Matrix Classical
variable {X W : Type*} [Fintype X] [Fintype W]

theorem zeroBlock_entry (A : Op (X ⊕ W)) (a b : Basis X) :
    zeroBlock A a b = A (zeroBasisMap a) (zeroBasisMap b) := by
  rw [← zeroEmbed_block A, zeroEmbed_right, zeroEmbed_left]

theorem outerT_unitary (A : Circuit (X ⊕ W)) (p : ℝ) :
    (outerT A p).unitary = rewireOp (Equiv.sumAssoc X W (Fin 1))
      (registerTensor A.unitary (singleCircuit (ryGate (0 : Fin 1) (ampZeta p))).unitary) := by
  rw [outerT, Circuit.rewire_unitary, Circuit.mul_unitary,
    Circuit.onLeft_unitary, Circuit.onRight_unitary]
  change rewireOp _ (registerTensor A.unitary 1 * registerTensor 1 _) = _
  rw [← registerTensor_mul, Matrix.mul_one, Matrix.one_mul]

theorem zeroBlock_regroup_tensor (A : Op (X ⊕ W)) (B : Op (Fin 1)) :
    zeroBlock (rewireOp (Equiv.sumAssoc X W (Fin 1)) (registerTensor A B)) =
      B (fun _ => 0) (fun _ => 0) • zeroBlock A := by
  ext a b
  rw [zeroBlock_entry]
  simp only [rewireOp, registerTensor, Matrix.smul_apply, smul_eq_mul]
  have hL (c : Basis X) :
      (zeroBasisMap (W := W ⊕ Fin 1) c ∘ Equiv.sumAssoc X W (Fin 1)) ∘ Sum.inl =
        zeroBasisMap (W := W) c := by
    funext x; cases x <;> rfl
  have hR (c : Basis X) :
      (zeroBasisMap (W := W ⊕ Fin 1) c ∘ Equiv.sumAssoc X W (Fin 1)) ∘ Sum.inr =
        (fun _ : Fin 1 => (0 : Fin 2)) := by
    funext x; rfl
  rw [hL a, hL b, hR a, hR b, ← zeroBlock_entry A a b]
  exact mul_comm _ _

def outerProjector : Op (X ⊕ (W ⊕ Fin 1)) :=
  zeroEmbed (X := X) (W := W ⊕ Fin 1) * (zeroEmbed (X := X) (W := W ⊕ Fin 1))ᴴ

def outerStartMap (A : Circuit (X ⊕ W)) (p : ℝ) :
    Matrix (Basis (X ⊕ (W ⊕ Fin 1))) (Basis X) ℂ :=
  (outerT A p).unitary * zeroEmbed (X := X) (W := W ⊕ Fin 1)

def outerGoodMap (V : Op X) : Matrix (Basis (X ⊕ (W ⊕ Fin 1))) (Basis X) ℂ :=
  zeroEmbed (X := X) (W := W ⊕ Fin 1) * V

theorem outerT_scaled (A : Circuit (X ⊕ W)) (V : Op X) (p : ℝ) (hp : 0 < p)
    (hb : BlockEncodes A.unitary p V) :
    (zeroEmbed (X := X) (W := W ⊕ Fin 1))ᴴ * (outerT A p).unitary * zeroEmbed (X := X) (W := W ⊕ Fin 1) =
      (Real.sin (ampTheta p) : ℂ) • V := by
  rw [zeroEmbed_block, outerT_unitary, zeroBlock_regroup_tensor, ry_oneBit_entry]
  change (Real.cos (ampZeta p / 2) : ℂ) • zeroBlock A.unitary = _
  rw [hb, smul_smul]
  have hs : (Real.cos (ampZeta p / 2) : ℂ) * (Real.sqrt p : ℂ) = (Real.sin (ampTheta p) : ℂ) := by
    exact_mod_cast (show Real.cos (ampZeta p / 2) * Real.sqrt p = Real.sin (ampTheta p) by
      simpa only [mul_comm] using amp_scale_identity p hp)
  rw [hs]

theorem outer_reflection_data (A : Circuit (X ⊕ W)) (V : Op X) (p : ℝ)
    (hV : Vᴴ * V = 1) (hp : 0 < p) (hb : BlockEncodes A.unitary p V) :
    TwoReflectionData (ampTheta p) (outerProjector (X := X) (W := W))
      (outerStartMap A p) (outerGoodMap (W := W) V) := by
  refine ⟨?_, ?_, ?_, ampTheta_mem p hp, ?_⟩
  · rw [outerProjector, zeroEmbed_projector]
    exact predicateProjector_orthogonal _
  · exact isometry_comp _ _ (Circuit.unitary_isUnitary (outerT A p)) zeroEmbed_isometry
  · exact isometry_comp _ _ zeroEmbed_isometry hV
  · unfold outerProjector outerStartMap outerGoodMap
    calc _ = zeroEmbed (X := X) (W := W ⊕ Fin 1) *
        ((zeroEmbed (X := X) (W := W ⊕ Fin 1))ᴴ * (outerT A p).unitary *
          zeroEmbed (X := X) (W := W ⊕ Fin 1)) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [outerT_scaled A V p hp hb, Matrix.mul_smul]

theorem outerF_simulates (p : ℝ) (c : ℂ) :
    KickbackSimulates c (outerF (X := X) (W := W) p).unitary
      (RG (outerProjector (X := X) (W := W))) := by
  have h := kickback_equality c (workspaceControls X (W ⊕ Fin 1)) 0
  have hp : (fun b : Basis (X ⊕ (W ⊕ Fin 1)) =>
      (∑ x ∈ workspaceControls X (W ⊕ Fin 1), (b x : ℕ)) = 0) =
      (fun b => b ∘ Sum.inr = fun _ => 0) := by
    funext b
    apply propext
    simp only [workspaceControls, Finset.sum_map, Function.Embedding.inr_apply]
    exact hammingWeight_eq_zero (b ∘ Sum.inr)
  rw [hp, phaseMatrix_reflect, ← zeroEmbed_projector] at h
  exact h

theorem outerIteration_simulates (A : Circuit (X ⊕ W)) (p : ℝ) (c : ℂ) :
    KickbackSimulates c (outerIteration A p).unitary
      (RS (outerStartMap A p) * RG (outerProjector (X := X) (W := W))) := by
  have hT : KickbackSimulates c (outerT A p).onLeft.unitary (outerT A p).unitary := by
    rw [Circuit.onLeft_unitary]
    exact kickback_extendLeft c _
  have hTA : KickbackSimulates c (outerT A p).onLeft.adjoint.unitary (outerT A p).unitaryᴴ := by
    rw [Circuit.adjoint_unitary]
    exact KickbackSimulates.adjoint (Circuit.unitary_isUnitary _) (Circuit.unitary_isUnitary _) hT
  have h := hT.mul ((outerF_simulates (X := X) (W := W) p c).mul
    (hTA.mul (outerF_simulates (X := X) (W := W) p c)))
  have hconj := conjugate_reflectRange (outerT A p).unitary (zeroEmbed (X := X) (W := W ⊕ Fin 1))
    (Matrix.mul_eq_one_comm.mp (Circuit.unitary_isUnitary (outerT A p)))
  have hd : (outerT A p).unitary * (RG (outerProjector (X := X) (W := W)) *
      ((outerT A p).unitaryᴴ * RG (outerProjector (X := X) (W := W)))) =
      RS (outerStartMap A p) * RG (outerProjector (X := X) (W := W)) := by
    calc _ = ((outerT A p).unitary * reflectRange (zeroEmbed (X := X) (W := W ⊕ Fin 1)) *
        (outerT A p).unitaryᴴ) * RG (outerProjector (X := X) (W := W)) := by
          simp only [outerProjector, RG, reflect, reflectRange, Matrix.mul_assoc]
      _ = _ := by rw [hconj]; rfl
  simp only [outerIteration, Circuit.mul_unitary] at h ⊢
  rw [hd] at h
  exact h

theorem outer_matrix_recovery (A : Circuit (X ⊕ W)) (V : Op X) (p : ℝ)
    (hV : Vᴴ * V = 1) (hp : 0 < p) (hb : BlockEncodes A.unitary p V) :
    (RS (outerStartMap A p) * RG (outerProjector (X := X) (W := W))) ^ ampK p * outerStartMap A p =
      ((-1 : ℂ) ^ ampK p) • outerGoodMap (W := W) V := by
  have h := two_reflection_identity (outer_reflection_data A V p hV hp hb) (ampK p)
  have hangle : (2 * (ampK p : ℝ) + 1) * ampTheta p = Real.pi / 2 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using twoK_add_one_mul_theta p
  rw [hangle, Real.sin_pi_div_two, Real.cos_pi_div_two] at h
  simpa using h
end Paper12

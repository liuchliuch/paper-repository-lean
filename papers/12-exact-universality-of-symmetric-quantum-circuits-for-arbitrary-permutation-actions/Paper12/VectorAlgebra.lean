import Paper12.OuterState

noncomputable section
namespace Paper12
open Matrix Classical
variable {J K : Type*} [Fintype J] [Fintype K]

theorem rewireVec_smul (e : J ≃ K) (z : ℂ) (ψ : Vec J) :
    rewireVec e (z • ψ) = z • rewireVec e ψ := rfl

theorem applyOp_sum {ι : Type*} (s : Finset ι) (A : Op J) (f : ι → Vec J) :
    applyOp A (∑ i ∈ s, f i) = ∑ i ∈ s, applyOp A (f i) := by
  funext b
  simp only [applyOp, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem applyOp_smul_vec (A : Op J) (z : ℂ) (ψ : Vec J) :
    applyOp A (z • ψ) = z • applyOp A ψ := by
  funext b
  simp only [applyOp, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem registerVec_smul_right (ψ : Vec J) (z : ℂ) (χ : Vec K) :
    registerVec ψ (z • χ) = z • registerVec ψ χ := by
  funext b
  simp only [registerVec, Pi.smul_apply, smul_eq_mul]
  ring

theorem registerVec_sum_right {ι : Type*} (s : Finset ι) (ψ : Vec J) (f : ι → Vec K) :
    registerVec ψ (∑ i ∈ s, f i) = ∑ i ∈ s, registerVec ψ (f i) := by
  funext b
  simp only [registerVec, Finset.sum_apply, Finset.mul_sum]

theorem vecInner_sum_right {ι : Type*} (s : Finset ι) (ψ : Vec J) (f : ι → Vec J) :
    vecInner ψ (∑ i ∈ s, f i) = ∑ i ∈ s, vecInner ψ (f i) := by
  simp only [vecInner, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem vecInner_sum_left {ι : Type*} (s : Finset ι) (f : ι → Vec J) (ψ : Vec J) :
    vecInner (∑ i ∈ s, f i) ψ = ∑ i ∈ s, vecInner (f i) ψ := by
  simp only [vecInner, Finset.sum_apply, star_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem vecInner_smul_right (ψ χ : Vec J) (z : ℂ) :
    vecInner ψ (z • χ) = z * vecInner ψ χ := by
  simp only [vecInner, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem vecInner_smul_left (ψ χ : Vec J) (z : ℂ) :
    vecInner (z • ψ) χ = star z * vecInner ψ χ := by
  simp only [vecInner, Pi.smul_apply, smul_eq_mul, StarMul.star_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem vecInner_adjoint (A : Op J) (ψ χ : Vec J) :
    vecInner ψ (applyOp Aᴴ χ) = vecInner (applyOp A ψ) χ := by
  simp only [vecInner, applyOp, Matrix.conjTranspose_apply, star_sum, StarMul.star_mul,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem vecInner_eBasis_left (a : Basis J) (ψ : Vec J) : vecInner (eBasis a) ψ = ψ a := by
  simp [vecInner, eBasis]

theorem embedZero_eBasis (a : Basis J) :
    embedZero (W := K) (eBasis a) = eBasis (zeroBasisMap (W := K) a) := by
  rw [embedZero_registerVec]
  funext b
  have h := zeroBasisMap_match a b
  simp only [registerVec, zeroKet, eBasis]
  have hz : b = zeroBasisMap a ↔ b ∘ Sum.inl = a ∧ b ∘ Sum.inr = (fun _ => 0) := by
    constructor
    · intro hb
      obtain ⟨hL, hR⟩ := h.mp hb.symm
      exact ⟨hL.symm, hR⟩
    · rintro ⟨hL, hR⟩
      exact (h.mpr ⟨hL.symm, hR⟩).symm
  simp only [hz]
  split_ifs <;> simp_all

theorem zeroBlock_inner (A : Op (J ⊕ K)) (a b : Basis J) :
    zeroBlock A a b = vecInner (embedZero (W := K) (eBasis a))
      (applyOp A (embedZero (W := K) (eBasis b))) := by
  rw [embedZero_eBasis, embedZero_eBasis, vecInner_eBasis_left, applyOp_eBasis,
    zeroBlock_entry]

theorem weightedOneHot_sum (d : J → ℝ) :
    weightedOneHot d = ∑ q : J, (d q : ℂ) • eBasis (oneHot q) := by
  funext b
  simp only [weightedOneHot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, eBasis]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> simp
end Paper12

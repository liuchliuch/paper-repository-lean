import Paper28.ChainIncidenceOrbitInjective
import Paper28.RegularSphereAction

/-! Actual signed l2 barycenters have nonnegative coordinate incidence
profiles on their face chain. Native superlevel reconstruction then proves
that two actual points of one closed barycentric cell in the same regular
orbit are equal. No quotient injectivity is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped Classical
variable {G : Type*} [Group G] [DecidableEq G]

def coordinateSign (A : Finset G) (g : G) : ℝ := if g ∈ A then 1 else -1

theorem coordinateSign_abs (A : Finset G) (g : G) : |coordinateSign A g| = 1 := by
  unfold coordinateSign
  split_ifs <;> norm_num

def signedFaceVector (A F : Finset G) : CoordinateHilbert G :=
  ∑ g ∈ F, lp.single 2 g (coordinateSign A g)

theorem signedFaceVector_apply (A F : Finset G) (g : G) :
    signedFaceVector A F g = if g ∈ F then coordinateSign A g else 0 := by
  simp [signedFaceVector,lp.coeFn_sum,lp.single_apply,Finset.sum_pi_single]

def signedFaceCenter (A F : Finset G) : CoordinateHilbert G := sphericalNormalize (signedFaceVector A F)

theorem signedFaceCenter_apply (A F : Finset G) (g : G) :
    signedFaceCenter A F g = if g ∈ F then ‖signedFaceVector A F‖⁻¹*coordinateSign A g else 0 := by
  change ‖signedFaceVector A F‖⁻¹*(signedFaceVector A F g) = _
  rw [signedFaceVector_apply]
  split_ifs <;> simp

def signedChainRaw (A : Finset G) (C : Finset (Finset G)) (w : Finset G → ℝ) : CoordinateHilbert G :=
  ∑ F ∈ C, w F • signedFaceCenter A F

def signedChainPoint (A : Finset G) (C : Finset (Finset G)) (w : Finset G → ℝ) : CoordinateHilbert G :=
  sphericalNormalize (signedChainRaw A C w)

def signedChainWeights (A : Finset G) (C : Finset (Finset G)) (w : Finset G → ℝ) (F : Finset G) : ℝ :=
  ‖signedChainRaw A C w‖⁻¹*(w F*‖signedFaceVector A F‖⁻¹)

theorem chainIncidenceProfile_smul {α : Type*} [DecidableEq α] (C : Finset (Finset α))
    (w : Finset α → ℝ) (c : ℝ) (x : α) :
    chainIncidenceProfile C (fun F => c*w F) x = c*chainIncidenceProfile C w x := by
  unfold chainIncidenceProfile
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro F _
  split_ifs <;> simp

theorem signedChainRaw_apply (A : Finset G) (C : Finset (Finset G)) (w : Finset G → ℝ) (g : G) :
    signedChainRaw A C w g = coordinateSign A g*
      chainIncidenceProfile C (fun F => w F*‖signedFaceVector A F‖⁻¹) g := by
  simp only [signedChainRaw,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  rw [chainIncidenceProfile,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro F _
  rw [signedFaceCenter_apply]
  by_cases hg : g ∈ F
  · simp only [if_pos hg]
    ring
  · simp only [if_neg hg,mul_zero]

theorem signedChainPoint_apply (A : Finset G) (C : Finset (Finset G)) (w : Finset G → ℝ) (g : G) :
    signedChainPoint A C w g = coordinateSign A g*chainIncidenceProfile C (signedChainWeights A C w) g := by
  change ‖signedChainRaw A C w‖⁻¹*(signedChainRaw A C w g) = _
  rw [signedChainRaw_apply]
  change _ = coordinateSign A g*chainIncidenceProfile C
    (fun F => ‖signedChainRaw A C w‖⁻¹*(w F*‖signedFaceVector A F‖⁻¹)) g
  rw [chainIncidenceProfile_smul]
  ring

theorem signedChainWeights_nonneg (A : Finset G) (C : Finset (Finset G)) (w : Finset G → ℝ)
    (hw : ∀ F ∈ C, 0 ≤ w F) : ∀ F ∈ C, 0 ≤ signedChainWeights A C w F := by
  intro F hF
  exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
    (mul_nonneg (hw F hF) (inv_nonneg.mpr (norm_nonneg _)))

theorem signedChainPoint_abs_apply (A : Finset G) (C : Finset (Finset G)) (w : Finset G → ℝ)
    (hw : ∀ F ∈ C, 0 ≤ w F) (g : G) :
    |signedChainPoint A C w g| = chainIncidenceProfile C (signedChainWeights A C w) g := by
  rw [signedChainPoint_apply,abs_mul,coordinateSign_abs,one_mul,
    abs_of_nonneg (chainIncidenceProfile_nonneg C _ (signedChainWeights_nonneg A C w hw) g)]

theorem signed_chain_point_orbit_injective (A : Finset G) (C : Finset (Finset G))
    (hChain : ∀ F ∈ C, ∀ E ∈ C, F ⊆ E ∨ E ⊆ F)
    (w z : Finset G → ℝ) (hw : ∀ F ∈ C, 0 ≤ w F) (hz : ∀ F ∈ C, 0 ≤ z F)
    (γ : G) (he : leftRegular γ (signedChainPoint A C w) = signedChainPoint A C z) :
    signedChainPoint A C w = signedChainPoint A C z := by
  have hAbs : ∀ g, chainIncidenceProfile C (signedChainWeights A C z) (γ*g) =
      chainIncidenceProfile C (signedChainWeights A C w) g := by
    intro g
    rw [← signedChainPoint_abs_apply A C z hz,← signedChainPoint_abs_apply A C w hw]
    have he' := congrArg (fun u : CoordinateHilbert G => |u (γ*g)|) he
    simpa only [leftRegular_apply,inv_mul_cancel_left] using he'.symm
  have hp := chainIncidenceProfile_orbit_injective C hChain (signedChainWeights A C w)
    (signedChainWeights A C z) (signedChainWeights_nonneg A C w hw) (signedChainWeights_nonneg A C z hz)
    (Equiv.mulLeft γ) hAbs
  ext g
  rw [signedChainPoint_apply,signedChainPoint_apply,congrFun hp g]

end Paper28

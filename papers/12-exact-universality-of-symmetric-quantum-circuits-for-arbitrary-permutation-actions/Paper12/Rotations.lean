import Paper12.Parallel
import Paper12.Selector
import Paper12.Registers

noncomputable section
namespace Paper12
open Matrix Classical
variable {J : Type*} [Fintype J]

def realRotation (c s : ℝ) : QMat := !![(c : ℂ), -(s : ℂ); (s : ℂ), (c : ℂ)]

theorem realRotation_unitary {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    (realRotation c s)ᴴ * realRotation c s = 1 := by
  have hc : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realRotation, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  · linear_combination hc
  · ring
  · ring
  · linear_combination hc

def ryGate (x : J) (θ : ℝ) : Gate J :=
  .one ⟨x, realRotation (Real.cos (θ / 2)) (Real.sin (θ / 2)),
    realRotation_unitary (by nlinarith [Real.sin_sq_add_cos_sq (θ / 2)])⟩

def rotationDen (d : ℝ) : ℝ := Real.sqrt (1 + d ^ 2)

theorem rotationDen_pos (d : ℝ) : 0 < rotationDen d := by
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg d]

def productRotation (d : ℝ) : QMat :=
  realRotation (rotationDen d)⁻¹ (d * (rotationDen d)⁻¹)

theorem productRotation_unitary (d : ℝ) : (productRotation d)ᴴ * productRotation d = 1 := by
  apply realRotation_unitary
  have hs : rotationDen d ^ 2 = 1 + d ^ 2 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg d])
  field_simp [ne_of_gt (rotationDen_pos d)]
  nlinarith

def productPreparation (d : J → ℝ) : Circuit J :=
  parallelCircuit (fun x => productRotation (d x)) (fun x => productRotation_unitary (d x))

def productC (d : J → ℝ) : ℝ := ∏ x : J, (rotationDen (d x))⁻¹

theorem productC_pos (d : J → ℝ) : 0 < productC d :=
  Finset.prod_pos (fun x _ => inv_pos.mpr (rotationDen_pos (d x)))

theorem productC_sq (d : J → ℝ) :
    productC d ^ 2 = (∏ x : J, (1 + (d x) ^ 2))⁻¹ := by
  unfold productC
  rw [← Finset.prod_pow]
  simp only [inv_pow]
  have h : ∀ x : J, rotationDen (d x) ^ 2 = 1 + d x ^ 2 := fun x =>
    Real.sq_sqrt (by nlinarith [sq_nonneg (d x)])
  simp_rw [h]
  exact Finset.prod_inv_distrib (fun x : J => 1 + d x ^ 2)

@[simp] theorem productPreparation_size (d : J → ℝ) :
    (productPreparation d).size = Fintype.card J := parallelCircuit_size _ _

theorem productPreparation_preserved (d : J → ℝ) (e : J ≃ J)
    (he : ∀ x, d (e x) = d x) :
    ∀ L ∈ (productPreparation d).layers, Layer.map e L = L := by
  intro L hL
  simp only [productPreparation, parallelCircuit, List.mem_singleton] at hL
  subst L
  exact parallelLayer_map _ _ e (fun x => congrArg productRotation (he x))

theorem productPreparation_oneHot (d : J → ℝ) (q : J) :
    applyOp (productPreparation d).unitary (zeroKet J) (oneHot q) =
      (productC d : ℂ) * (d q : ℂ) := by
  rw [show zeroKet J = eBasis (fun _ : J => 0) from rfl, applyOp_eBasis]
  rw [show (productPreparation d).unitary = tensorOp (fun x => productRotation (d x))
    from parallelCircuit_unitary _ _]
  unfold tensorOp
  have hentry : ∀ x : J, productRotation (d x) (oneHot q x) 0 =
      (if x = q then (d q : ℂ) else 1) * ((rotationDen (d x))⁻¹ : ℝ) := by
    intro x
    by_cases hx : x = q
    · subst x
      simp [productRotation, realRotation, oneHot]
    · simp [productRotation, realRotation, oneHot, hx]
  simp_rw [hentry]
  rw [Finset.prod_mul_distrib]
  have hdelta : (∏ x : J, if x = q then (d q : ℂ) else 1) = d q := by
    rw [Finset.prod_eq_single q]
    · simp
    · intro x _ hx; simp [hx]
    · intro hq; exact (hq (Finset.mem_univ _)).elim
  rw [hdelta]
  have hc : (∏ x : J, (((rotationDen (d x))⁻¹ : ℝ) : ℂ)) = (productC d : ℂ) := by
    simp only [productC, _root_.Complex.ofReal_prod]
  rw [hc, mul_comm]
end Paper12

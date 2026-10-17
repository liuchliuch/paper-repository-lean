import BoundaryReduction.MeanMap
import Mathlib.Topology.Order.IntermediateValue

open Real Set BigOperators
open scoped Classical
namespace BoundaryReduction.NinePoint

/-- A finite prior over actual NEF component means in C. -/
structure FinitePrior (C : Set (EuclideanSpace ℝ (Fin 2))) where
  n : ℕ
  weights : FinProb (Fin n)
  parameter : Fin n → ℝ × ℝ
  admissible : ∀ j, esMean (pt (parameter j)) ∈ C

namespace FinitePrior
variable {C : Set (EuclideanSpace ℝ (Fin 2))}

noncomputable def mass (V : FinitePrior C) (y : Fin 9) :=
  ∑ j, V.weights.w j * pt (V.parameter j) y

lemma mass_nonneg (V : FinitePrior C) (y : Fin 9) : 0 ≤ V.mass y := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (V.weights.nonneg j) (pt_pos _ _).le

lemma mass_sum (V : FinitePrior C) : ∑ y, V.mass y = 1 := by
  unfold mass
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, pt_sum, mul_one]
  exact V.weights.sum_eq_one

noncomputable def prob (V : FinitePrior C) : FinProb (Fin 9) :=
  ⟨V.mass, V.mass_nonneg, V.mass_sum⟩

lemma mass_pos (V : FinitePrior C) (y : Fin 9) : 0 < V.mass y := by
  have hw : ∃ j, 0 < V.weights.w j := by
    by_contra! h
    have hh := Finset.sum_nonpos (s := Finset.univ) (fun j _ => h j)
    rw [V.weights.sum_eq_one] at hh
    norm_num at hh
  obtain ⟨j,hj⟩ := hw
  exact Finset.sum_pos' (fun k _ => mul_nonneg (V.weights.nonneg k) (pt_pos _ _).le)
    ⟨j, Finset.mem_univ _, mul_pos hj (pt_pos _ _)⟩

lemma expect_eq (V : FinitePrior C) (g : Fin 9 → ℝ) :
    FinProb.expect V.prob g = ∑ j, V.weights.w j * FinProb.expect (tiltProb (V.parameter j)) g := by
  simp only [FinProb.expect, prob, mass, tiltProb, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma expect_lower (V : FinitePrior C) (g : Fin 9 → ℝ) (a : ℝ)
    (h : ∀ θ, esMean (pt θ) ∈ C → a ≤ FinProb.expect (tiltProb θ) g) :
    a ≤ FinProb.expect V.prob g := by
  rw [expect_eq]
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (h _ (V.admissible j)) (V.weights.nonneg j))
  rw [← Finset.sum_mul, V.weights.sum_eq_one, one_mul] at hh
  exact hh

end FinitePrior

noncomputable def information (C : Set (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  sInf {x : ℝ | ∃ V : FinitePrior C, x = FinProb.klPos V.prob baseProb}

def exterior : Set (EuclideanSpace ℝ (Fin 2)) := {μ | r₀ ≤ ‖μ‖}
def boundary : Set (EuclideanSpace ℝ (Fin 2)) := {μ | ‖μ‖ = r₀}

lemma information_bddBelow (C : Set (EuclideanSpace ℝ (Fin 2))) :
    BddBelow {x : ℝ | ∃ V : FinitePrior C, x = FinProb.klPos V.prob baseProb} := by
  refine ⟨0, ?_⟩
  rintro x ⟨V,rfl⟩
  exact FinProb.klPos_nonneg p0_pos

noncomputable def exteriorPrior : FinitePrior exterior where
  n := 8
  weights := ⟨fun _ => 1/8, fun _ => by norm_num, by norm_num⟩
  parameter := fun j => (200:ℝ) • compNormal j
  admissible := fun j => (exterior_200 j).le

lemma prob_ext {α : Type*} [Fintype α] {p q : FinProb α}
    (h : ∀ y, p.w y = q.w y) : p = q := by
  cases p
  cases q
  congr 1
  exact funext h

lemma exteriorPrior_prob : exteriorPrior.prob = mixtureProb 200 := by
  apply prob_ext
  intro y
  change (∑ j : Fin 8, (1/8 : ℝ)*compPt 200 j y) = (1/8 : ℝ)*∑ j, compPt 200 j y
  exact (Finset.mul_sum ..).symm

/-- The strict exterior upper bound uses the fixed, actual eight-component mixture. -/
theorem information_exterior_upper : information exterior < 2 * 10 ^ (-15 : ℤ) := by
  have h := csInf_le (information_bddBelow exterior)
    (show FinProb.klPos exteriorPrior.prob baseProb ∈ _ from ⟨exteriorPrior,rfl⟩)
  rw [exteriorPrior_prob] at h
  have hh := kl_Q200_lt
  norm_num at hh ⊢
  exact lt_of_le_of_lt h (lt_of_lt_of_le hh (by norm_num))

lemma boundary_prior_kl_lower (V : FinitePrior boundary) :
    (7:ℝ)*10^(-12:ℤ) < FinProb.klPos V.prob baseProb := by
  let η := (35/100 : ℝ)*(1-ε)/9*r₀^2
  have hη : 0 ≤ η := by
    dsimp [η]
    have he : 0 ≤ 1-ε := by linarith [ε_lt_one]
    positivity
  have hex : η ≤ FinProb.expect V.prob separator :=
    V.expect_lower separator η (fun θ hθ => separator_boundary hθ)
  have h := FinProb.separator_kl_lower V.prob baseProb V.mass_pos p0_pos
    (by norm_num : (0:ℝ)<1) hη separator_bounded separator_base hex
  have hnum : (7:ℝ)*10^(-12:ℤ) < η^2/(2*(1:ℝ)^2) := by
    dsimp [η]
    rw [ε_eq, r₀_eq]
    norm_num
  exact hnum.trans_le h

/-- A positive origin discrepancy for every exterior component. -/
lemma exterior_parameter_lower {θ : ℝ × ℝ} (hθ : esMean (pt θ) ∈ exterior) :
    r₀ ≤ ‖toES θ‖ := by
  by_cases hs : ‖toES θ‖ ≤ 1/10
  · exact hθ.trans (mean_norm_local (by nlinarith [norm_nonneg (toES θ)]))
  · rw [r₀_eq]
    linarith [lt_of_not_ge hs]

lemma Z_quadratic_lower (θ : ℝ × ℝ) :
    1 + (1/5 : ℝ)*‖toES θ‖^2 ≤ Z θ := by
  obtain ⟨u,v⟩ := θ
  have hcu := cosh_quadratic_lower u
  have hcv := cosh_quadratic_lower v
  have hru := cosh_quadratic_lower (ρ*u)
  have hrv := cosh_quadratic_lower (ρ*v)
  have hm := mul_le_mul hru hrv (by positivity : 0 ≤ 1+(ρ*v)^2/2) (cosh_pos _).le
  have hprod : 0 ≤ (ρ*u)^2*(ρ*v)^2 := by positivity
  have hz8 : 8 + (41/25 : ℝ)*(u^2+v^2) ≤ Z8 u v := by
    dsimp [Z8]
    rw [mul_pow, mul_pow, ρ_sq] at hm hprod
    nlinarith
  rw [Z_eq_cosh, norm_toES, euclNorm, Real.sq_sqrt (by positivity)]
  have hw := mul_le_mul_of_nonneg_left hz8 w_pos.le
  rw [w_eq] at hw ⊢
  have hc : (1/5 : ℝ) ≤ (41/200 : ℝ)*(1-ε) := by rw [ε_eq]; norm_num
  have hh := mul_le_mul_of_nonneg_right hc (show 0 ≤ u^2+v^2 by positivity)
  nlinarith

noncomputable def originCap : ℝ := ε / (1 + (1/5 : ℝ)*r₀^2)
lemma originCap_lt : originCap < ε := by
  unfold originCap
  exact (div_lt_self ε_pos (by nlinarith [r₀_pos])).trans_le le_rfl

lemma exterior_origin_cap {θ : ℝ × ℝ} (hθ : esMean (pt θ) ∈ exterior) :
    pt θ 0 ≤ originCap := by
  have hl := exterior_parameter_lower hθ
  have hz : 1+(1/5 : ℝ)*r₀^2 ≤ Z θ := by
    have h := Z_quadratic_lower θ
    nlinarith [r₀_pos]
  have hd : 0 < 1+(1/5 : ℝ)*r₀^2 := by positivity
  simp only [pt, un, coord, dot, mul_zero, add_zero, exp_zero, one_mul, p0]
  change ε / Z θ ≤ originCap
  exact div_le_div_of_nonneg_left ε_pos.le hd hz

lemma continuous_pt (y : Fin 9) : Continuous (fun θ : ℝ × ℝ => pt θ y) := by
  have hu (z : Fin 9) : Continuous (fun θ : ℝ × ℝ => un θ z) := by
    unfold un dot
    fun_prop
  exact (hu y).div (continuous_finset_sum _ (fun z _ => hu z))
    (fun θ => (Z_pos θ).ne')

lemma continuous_mean : Continuous (fun θ : ℝ × ℝ => esMean (pt θ)) := by
  apply continuous_finset_sum
  intro y _
  exact (continuous_pt y).smul continuous_const

lemma pt_zero : pt (0 : ℝ × ℝ) = p0 := by
  have hz : Z (0 : ℝ × ℝ) = 1 := by simpa [Z, un, dot] using p0_sum
  ext y
  simp [pt, un, dot, hz]

lemma exists_boundary_parameter : ∃ θ : ℝ × ℝ, ‖esMean (pt θ)‖ = r₀ := by
  let f : ℝ → ℝ := fun t => ‖esMean (pt (t • compNormal 0))‖
  have hc : Continuous f := (continuous_mean.comp (continuous_id.smul continuous_const)).norm
  have h0 : f 0 = 0 := by simp [f, pt_zero, base_esMean]
  have h200 : r₀ ≤ f 200 := (exterior_200 0).le
  obtain ⟨t,ht,heq⟩ := intermediate_value_Icc (a := (0:ℝ)) (b := 200)
    (by norm_num) hc.continuousOn (show r₀ ∈ Icc (f 0) (f 200) from
      ⟨by rw [h0]; exact r₀_pos.le, h200⟩)
  exact ⟨t • compNormal 0, heq⟩

lemma boundary_prior_nonempty : Nonempty (FinitePrior boundary) := by
  obtain ⟨θ,hθ⟩ := exists_boundary_parameter
  exact ⟨⟨1, ⟨fun _ => 1, fun _ => by norm_num, by simp⟩,
    fun _ => θ, fun _ => hθ⟩⟩

noncomputable def η : ℝ := (35/100 : ℝ)*(1-ε)/9*r₀^2

lemma η_pos : 0 < η := by
  dsimp [η]
  have he : 0 < 1-ε := by linarith [ε_lt_one]
  have hr := r₀_pos
  positivity

lemma η_numeric : (7:ℝ)*10^(-12:ℤ) < η^2/2 := by
  dsimp [η]
  rw [ε_eq, r₀_eq]
  norm_num

lemma boundary_prior_kl_bound (V : FinitePrior boundary) :
    η^2/2 ≤ FinProb.klPos V.prob baseProb := by
  have hex : η ≤ FinProb.expect V.prob separator :=
    V.expect_lower separator η (fun θ hθ => separator_boundary hθ)
  simpa using FinProb.separator_kl_lower V.prob baseProb V.mass_pos p0_pos
    (by norm_num : (0:ℝ)<1) η_pos.le separator_bounded separator_base hex

/-- The strict boundary information lower bound in Theorem 3.1. -/
theorem information_boundary_lower : (7:ℝ)*10^(-12:ℤ) < information boundary := by
  obtain ⟨V⟩ := boundary_prior_nonempty
  have hn : {x : ℝ | ∃ V : FinitePrior boundary, x = FinProb.klPos V.prob baseProb}.Nonempty :=
    ⟨_, V, rfl⟩
  apply η_numeric.trans_le
  exact le_csInf hn (by rintro x ⟨U,rfl⟩; exact boundary_prior_kl_bound U)

lemma exterior_prior_origin_cap (V : FinitePrior exterior) : V.mass 0 ≤ originCap := by
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (exterior_origin_cap (V.admissible j)) (V.weights.nonneg j))
  rw [← Finset.sum_mul, V.weights.sum_eq_one, one_mul] at h
  exact h

lemma exterior_prior_kl_bound (V : FinitePrior exterior) :
    2*(ε-originCap)^2 ≤ FinProb.klPos V.prob baseProb := by
  have h := FinProb.pinsker_event V.prob baseProb V.mass_pos p0_pos
    {0} (by simp) (by exact ⟨1, by simp⟩)
  simp only [Finset.sum_singleton] at h
  change 2*(V.mass 0-ε)^2 ≤ _ at h
  have hc := exterior_prior_origin_cap V
  have ho := originCap_lt
  nlinarith [sq_nonneg (originCap - V.mass 0)]

/-- Strict positivity follows from the origin atom uniformly over all finite priors. -/
theorem information_exterior_pos : 0 < information exterior := by
  have hn : {x : ℝ | ∃ V : FinitePrior exterior, x = FinProb.klPos V.prob baseProb}.Nonempty :=
    ⟨_, exteriorPrior, rfl⟩
  have hlow : 2*(ε-originCap)^2 ≤ information exterior :=
    le_csInf hn (by rintro x ⟨V,rfl⟩; exact exterior_prior_kl_bound V)
  have hpos : 0 < 2*(ε-originCap)^2 := by
    have hd : 0 < ε-originCap := sub_pos.mpr originCap_lt
    positivity
  exact hpos.trans_le hlow

/-- The complete numerical information separation of (3.5), for arbitrary finite NEF mixtures. -/
theorem theorem_3_1_information :
    0 < information exterior ∧ information exterior < 2*10^(-15:ℤ) ∧
      (7:ℝ)*10^(-12:ℤ) < information boundary :=
  ⟨information_exterior_pos, information_exterior_upper, information_boundary_lower⟩

end BoundaryReduction.NinePoint

import BoundaryReduction.ExposedGeometry
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open Real Set BigOperators Filter MeasureTheory
open scoped Classical
namespace BoundaryReduction.FiniteExponential

variable {α : Type} [Fintype α] [Nonempty α] {d : ℕ}
variable (p : FinProb α) (hp : ∀ y, 0 < p.w y) (Y : α → E d)

lemma Prior.expect_eq {C : Set (E d)} (F : Prior p hp Y C) (g : α → ℝ) :
    FinProb.expect F.prob g = ∑ i, F.weights.w i*FinProb.expect (tilt p hp Y (F.parameter i)) g := by
  simp only [FinProb.expect,Prior.prob,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma Prior.prob_pos {C : Set (E d)} (F : Prior p hp Y C) (y : α) : 0 < F.prob.w y := by
  have hw : ∃ i, 0 < F.weights.w i := by
    by_contra! hn
    have hh := Finset.sum_nonpos (s := Finset.univ) (fun i _ => hn i)
    rw [F.weights.sum_eq_one] at hh
    norm_num at hh
  obtain ⟨i,hi⟩ := hw
  exact Finset.sum_pos' (fun j _ => mul_nonneg (F.weights.nonneg j) (tilt_pos p hp Y _ y).le)
    ⟨i,Finset.mem_univ _,mul_pos hi (tilt_pos p hp Y _ y)⟩

lemma Prior.expect_lower {C : Set (E d)} (F : Prior p hp Y C) (g : α → ℝ) (c : ℝ)
    (h : ∀ θ, mean p hp Y θ ∈ C → c ≤ FinProb.expect (tilt p hp Y θ) g) :
    c ≤ FinProb.expect F.prob g := by
  rw [Prior.expect_eq]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (h _ (F.admissible i)) (F.weights.nonneg i))
  rwa [← Finset.sum_mul,F.weights.sum_eq_one,one_mul] at hh

/-- The general boundary separator bound (3.24) for genuine finite mixtures. -/
theorem information_separator_lower {C : Set (E d)} (hC : Nonempty (Prior p hp Y C))
    (g : α → ℝ) {L η : ℝ} (hL : 0 < L) (hη : 0 ≤ η)
    (hg : ∀ y, |g y| ≤ L) (hpg : FinProb.expect p g = 0)
    (hsep : ∀ θ, mean p hp Y θ ∈ C → η ≤ FinProb.expect (tilt p hp Y θ) g) :
    η^2/(2*L^2) ≤ information p hp Y C := by
  apply le_csInf
  · obtain ⟨F⟩ := hC
    exact ⟨_,⟨F,rfl⟩⟩
  · rintro x ⟨F,rfl⟩
    exact FinProb.separator_kl_lower F.prob p (F.prob_pos p hp Y) hp hL hη hg hpg
      (F.expect_lower p hp Y g η hsep)

variable (V : Finset α) (hV : V.Nonempty) (normal : V → E d)
variable (hexpose : ∀ v : V, ∀ y, y ≠ (v : α) → inner ℝ (normal v) (Y y) < inner ℝ (normal v) (Y v))
include hV hexpose

/-- The same reconstruction obstruction rules out every positive law with the
boundary separator certificate, hence in particular every Borel boundary mixture. -/
theorem no_global_of_separator (B : Set (E d))
    (hVoutside : ∀ v : V, Y v ∉ closure B)
    (g : α → ℝ) {L η : ℝ} (hL : 0 < L) (hη : 0 ≤ η)
    (hg : ∀ y, |g y| ≤ L) (hpg : FinProb.expect p g = 0)
    (hgap : -log (vertexMass p V) < η^2/(2*L^2))
    (Q : FinProb α) (hQ : ∀ y, 0 < Q.w y) (hQg : η ≤ FinProb.expect Q g) :
    ¬ (∀ θ, mean p hp Y θ ∉ B → FinProb.klPos Q p ≤
      FinProb.expect (tilt p hp Y θ) (fun y => log (Q.w y/p.w y))) := by
  intro hglobal
  have hlow := FinProb.separator_kl_lower Q p hQ hp hL hη hg hpg hQg
  have hlim := remote_kl_tendsto p hp Y V hV normal hexpose
  have hupper : FinProb.klPos Q p ≤ -log (vertexMass p V) := by
    apply ge_of_tendsto hlim
    filter_upwards [remote_exterior_eventually p hp Y V hV normal hexpose B hVoutside] with t ht
    let F : Prior p hp Y Bᶜ := ⟨V,inferInstance,vertexWeights p hp V hV,fun v => t • normal v,ht⟩
    have havg := F.expect_lower p hp Y (fun y => log (Q.w y/p.w y)) (FinProb.klPos Q p) hglobal
    have hc := FinProb.klPos_chain_rule (p := F.prob) (q := Q) (r := p) hQ hp
    have hn := FinProb.klPos_nonneg (p := F.prob) hQ
    change FinProb.klPos F.prob p = FinProb.klPos F.prob Q+
      FinProb.expect F.prob (fun y => log (Q.w y/p.w y)) at hc
    change FinProb.klPos Q p ≤ FinProb.klPos F.prob p
    linarith
  linarith

/-- Both information assertions and strict failure in Proposition 3.2. -/
theorem proposition_3_2 [Nontrivial α]
    (B : Set (E d)) (h0 : (0 : E d) ∈ B) (hmean : (∑ y, p.w y • Y y) = 0)
    (hcontained : closure B ⊆ Set.range (mean p hp Y))
    (g : α → ℝ) {L η : ℝ} (hL : 0 < L) (hη : 0 < η)
    (hg : ∀ y, |g y| ≤ L) (hpg : FinProb.expect p g = 0)
    (hsep : ∀ θ, mean p hp Y θ ∈ frontier B → η ≤ FinProb.expect (tilt p hp Y θ) g) :
    information p hp Y Bᶜ ≤ -log (vertexMass p V) ∧
    η^2/(2*L^2) ≤ information p hp Y (frontier B) ∧
    (-log (vertexMass p V) < η^2/(2*L^2) →
      information p hp Y Bᶜ < information p hp Y (frontier B)) := by
  have hout : ∀ v : V, Y v ∉ closure B := fun v hv =>
    exposed_vertex_not_mean p hp Y v (normal v) (hexpose v) (hcontained hv)
  obtain ⟨t,ht⟩ := (remote_exterior_eventually p hp Y V hV normal hexpose B hout).exists
  let v : V := ⟨hV.choose,hV.choose_spec⟩
  have hC := boundary_prior_nonempty p hp Y B h0 hmean (t • normal v) (ht v)
  have hu := proposition_3_2_exterior p hp Y V hV normal hexpose B hcontained
  have hl := information_separator_lower p hp Y hC g hL hη.le hg hpg hsep
  exact ⟨hu,hl,fun hgap => hu.trans_lt (hgap.trans_le hl)⟩

end BoundaryReduction.FiniteExponential

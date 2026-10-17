import BoundaryReduction.ExposedObstruction
import Mathlib.Topology.Connected.Clopen

open Real Set BigOperators Filter
open scoped Classical
namespace BoundaryReduction.FiniteExponential

variable {α : Type} [Fintype α] [Nonempty α] {d : ℕ}
variable (p : FinProb α) (hp : ∀ y, 0 < p.w y) (Y : α → E d)
include hp

lemma continuous_tilt (y : α) : Continuous (fun θ : E d => (tilt p hp Y θ).w y) := by
  have hc (z : α) : Continuous (fun θ : E d => p.w z*exp (inner ℝ θ (Y z))) :=
    by fun_prop
  exact (hc y).div (continuous_finset_sum _ (fun z _ => hc z)) (fun θ => (partition_pos p hp Y θ).ne')

lemma continuous_mean : Continuous (mean p hp Y) :=
  continuous_finset_sum _ (fun y _ => (continuous_tilt p hp Y y).smul continuous_const)

lemma mean_zero (hmean : (∑ y, p.w y • Y y) = 0) : mean p hp Y 0 = 0 := by
  have hZ : partition p Y 0 = 1 := by simpa [partition] using p.sum_eq_one
  simpa [mean,tilt,hZ] using hmean

lemma exposed_vertex_not_mean [Nontrivial α] (v : α) (n : E d)
    (hexpose : ∀ y, y ≠ v → inner ℝ n (Y y) < inner ℝ n (Y v)) :
    Y v ∉ Set.range (mean p hp Y) := by
  rintro ⟨θ,hθ⟩
  obtain ⟨z,hz⟩ := exists_ne v
  have hle (y : α) : inner ℝ n (Y y) ≤ inner ℝ n (Y v) := by
    by_cases hy : y = v
    · simp [hy]
    · exact (hexpose y hy).le
  have hs := Finset.sum_lt_sum
    (fun y (_ : y ∈ Finset.univ) => mul_le_mul_of_nonneg_left (hle y) (tilt_pos p hp Y θ y).le)
    ⟨z,Finset.mem_univ _,mul_lt_mul_of_pos_left (hexpose z hz) (tilt_pos p hp Y θ z)⟩
  rw [← Finset.sum_mul,(tilt p hp Y θ).sum_eq_one,one_mul] at hs
  have hm : inner ℝ n (mean p hp Y θ) = ∑ y, (tilt p hp Y θ).w y*inner ℝ n (Y y) := by
    simp [mean,inner_sum,real_inner_smul_right]
  rw [← hm,hθ] at hs
  exact lt_irrefl _ hs

lemma boundary_prior_nonempty (B : Set (E d)) (h0 : (0 : E d) ∈ B)
    (hmean : (∑ y, p.w y • Y y) = 0) (θ : E d) (hθ : mean p hp Y θ ∉ B) :
    Nonempty (Prior p hp Y (frontier B)) := by
  have hnon : ((mean p hp Y) ⁻¹' B).Nonempty := ⟨0,by rwa [Set.mem_preimage,mean_zero p hp Y hmean]⟩
  have hne : (mean p hp Y) ⁻¹' B ≠ Set.univ := by
    intro hh
    have hx : θ ∈ (mean p hp Y) ⁻¹' B := hh.symm ▸ Set.mem_univ θ
    exact hθ hx
  obtain ⟨r,hr⟩ := nonempty_frontier_iff.mpr ⟨hnon,hne⟩
  have hboundary : mean p hp Y r ∈ frontier B := (continuous_mean p hp Y).frontier_preimage_subset B hr
  exact ⟨⟨Unit,inferInstance,⟨fun _ => 1,fun _ => by norm_num,by simp⟩,fun _ => r,fun _ => hboundary⟩⟩

/-- The geometric hypotheses in Proposition 3.2 imply the exposed-mean feasibility condition. -/
theorem proposition_3_2_exterior [Nontrivial α]
    (V : Finset α) (hV : V.Nonempty) (normal : V → E d)
    (hexpose : ∀ v : V, ∀ y, y ≠ (v : α) → inner ℝ (normal v) (Y y) < inner ℝ (normal v) (Y v))
    (B : Set (E d)) (hcontained : closure B ⊆ Set.range (mean p hp Y)) :
    information p hp Y Bᶜ ≤ -log (vertexMass p V) := by
  apply information_exterior_le p hp Y V hV normal hexpose B
  intro v hv
  exact exposed_vertex_not_mean p hp Y v (normal v) (hexpose v) (hcontained hv)

end BoundaryReduction.FiniteExponential

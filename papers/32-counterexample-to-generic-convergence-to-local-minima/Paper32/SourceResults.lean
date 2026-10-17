import Paper32.Main
import Paper32.FunctionClass
import Paper32.Epigraph
import Paper32.TiltMeasure

/-! Literal bundles of the source geometry and first-step statements.
These bundles reuse proved statements about the original objects; they introduce
no extra analytic assumptions or external theorem interfaces. -/
open Set Filter Topology
namespace Paper32

/-- The bounded-orbit event in the literal Euclidean norm of (2.3). -/
def euclideanBoundedOrbitEvent {Ω : Type*} (z : ℕ → Ω → Point) : Set Ω :=
  {ω | ∃ C : ℝ, ∀ k, euclideanNorm (z k ω) ≤ C}

theorem euclideanBoundedOrbitEvent_eq {Ω : Type*} (z : ℕ → Ω → Point) :
    euclideanBoundedOrbitEvent z = boundedOrbitEvent z := by
  ext ω
  constructor
  · rintro ⟨C,hC⟩
    exact ⟨C,fun k => (norm_le_euclideanNorm (z k ω)).trans (hC k)⟩
  · rintro ⟨C,hC⟩
    exact ⟨2*C,fun k => (euclideanNorm_le_two_norm (z k ω)).trans (by linarith [hC k])⟩

/-- Lemma 3.1, with the exact coefficients and strict inequality of (3.1). -/
theorem source_lemma_3_1 :
    (∀ z, 0 ≤ F z) ∧ Tendsto F (cocompact Point) atTop ∧ LipschitzWith 8 F ∧
    SemialgebraicFunction F ∧ ContinuousPiecewiseAffine F ∧
    (∀ v, U v → (∀ z, (1-max |v.1| |v.2|)*l1 z ≤ tilt v z) ∧
      (∀ z ≠ 0, (99/100:ℝ)*l1 z < tilt v z) ∧
      (∀ z, 0 ≤ tilt v z) ∧ Tendsto (tilt v) (cocompact Point) atTop) ∧
    (∀ z, l1 z < 4 → F z=g z+8) := by
  exact ⟨F_nonneg,F_coercive,lipschitz_F,semialgebraic_F,continuousPiecewiseAffine_F,
    fun v hv => ⟨tilt_lower v,fun _ hz => tilt_strict_lower hv hz,tilt_nonneg hv,tilt_coercive hv⟩,
    fun _ hz => F_eq_core hz⟩

/-- Proposition 3.2: both standard subdifferentials, with the rectangle inclusion. -/
theorem source_proposition_3_2 :
    limitingSubdiff F 0=limitingSegments ∧ limitingSubdiff g 0=limitingSegments ∧
    clarkeSubdiff F 0=convexHull ℝ sectorGradients ∧
    clarkeSubdiff g 0=convexHull ℝ sectorGradients ∧
    ∀ w : Point, |w.1| ≤ 1 → |w.2| ≤ 2 → w ∈ clarkeSubdiff F 0 := by
  refine ⟨limiting_F_zero,limiting_g_zero,clarke_F_zero,clarke_g_zero,?_⟩
  intro w hx hy
  rw [clarke_F_zero,← clarke_g_zero]
  exact rectangle_subset_clarke_g_zero hx hy

/-- All conclusions of Corollary 3.3, including actual epigraph regularity. -/
theorem source_corollary_3_3 {v : Point} (hv : U v) :
    (0 : Point) ∈ clarkeSubdiff (tilt v) 0 ∧
    (0 : Point) ∉ limitingSubdiff (tilt v) 0 ∧
    ¬ IsLocalMin (tilt v) 0 ∧ ¬ EpigraphClarkeRegularAt F 0 ∧
    ∀ ρ : ℝ, 0 ≤ ρ → ¬ LocallyWeaklyConvex ρ := by
  exact ⟨(criticality_gap hv).1,(criticality_gap hv).2.1,(criticality_gap hv).2.2,
    not_epigraphClarkeRegular_F_zero,not_locallyWeaklyConvex⟩

/-- Lemma 4.1 with an arbitrary true Clarke oracle value at any basin point. -/
theorem source_lemma_4_1 {v z w ν : Point} {γ : ℝ} (hv : U v)
    (hγhi : γ < 1) (hz : Dstar z)
    (hw : w ∈ clarkeSubdiff (tilt v) z)
    (hν : |ν.1| ≤ 1/100 ∧ |ν.2| ≤ 1/100) :
    |(z-powerStep γ 0 • (w+ν)).1| < (36/5)*powerStep γ 0 ∧
    |(z-powerStep γ 0 • (w+ν)).2| < (5/2)*powerStep γ 0 := by
  have hlocal : l1 z < 4 := by unfold l1; linarith [hz.1,hz.2]
  have hbound := clarke_tilt_coordinate_bound hlocal hw
  have h := first_step_capture (powerStep_initial_lower hγhi) hz.1 hz.2 hv.1 hv.2
    hbound.1 hbound.2 hν.1 hν.2
  simpa only [Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,Prod.fst_add,
    Prod.snd_add,smul_eq_mul,← mul_add] using h

end Paper32

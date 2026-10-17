import Paper32.Subdifferential

open Set Filter Topology
namespace Paper32

lemma linCLM_injective : Function.Injective linCLM := by
  intro v w h
  apply Prod.ext
  · have h1 := congrArg (fun L : Point →L[ℝ] ℝ => L (1,0)) h
    simpa [linCLM, lin] using h1
  · have h2 := congrArg (fun L : Point →L[ℝ] ℝ => L (0,1)) h
    simpa [linCLM, lin] using h2

/-- Gradient limits depend only on the function on a neighborhood. -/
lemma gradientLimits_congr_of_eventuallyEq {f h : Point → ℝ} {z : Point}
    (heq : f =ᶠ[𝓝 z] h) : gradientLimits f z = gradientLimits h z := by
  have incl : ∀ (f h : Point → ℝ), f =ᶠ[𝓝 z] h → gradientLimits f z ⊆ gradientLimits h z := by
    intro f h heq w hw
    obtain ⟨a,b,ha,hb,hd⟩ := hw
    have hlocal : ∀ᶠ n in atTop, f =ᶠ[𝓝 (a n)] h := ha.eventually heq.eventually_nhds
    obtain ⟨N,hN⟩ := eventually_atTop.mp hlocal
    refine ⟨fun n => a (n+N), fun n => b (n+N),
      ha.comp (tendsto_add_atTop_nat N), hb.comp (tendsto_add_atTop_nat N), ?_⟩
    intro n
    exact (hd (n+N)).congr_of_eventuallyEq (hN (n+N) (by omega)).symm
  exact Subset.antisymm (incl f h heq) (incl h f heq.symm)

lemma clarkeSubdiff_congr_of_eventuallyEq {f h : Point → ℝ} {z : Point}
    (heq : f =ᶠ[𝓝 z] h) : clarkeSubdiff f z = clarkeSubdiff h z := by
  simp only [clarkeSubdiff, gradientLimits_congr_of_eventuallyEq heq]

/-- On an affine neighborhood all genuine gradient limits equal its coefficient. -/
theorem gradientLimits_locally_affine {f : Point → ℝ} {z w : Point} {c : ℝ}
    (heq : f =ᶠ[𝓝 z] fun q => lin w q + c) : gradientLimits f z = {w} := by
  rw [gradientLimits_congr_of_eventuallyEq heq]
  apply Set.Subset.antisymm
  · intro u hu
    obtain ⟨a,b,ha,hb,hd⟩ := hu
    have hbw : b = fun _ => w := by
      funext n
      apply linCLM_injective
      exact (hd n).unique (((linCLM w).hasFDerivAt).add_const c)
    subst b
    exact mem_singleton_iff.mpr (tendsto_nhds_unique hb tendsto_const_nhds)
  · intro u hu
    have hu' : u = w := mem_singleton_iff.mp hu
    subst u
    exact ⟨fun _ => z, fun _ => w, tendsto_const_nhds, tendsto_const_nhds,
      fun _ => ((linCLM w).hasFDerivAt).add_const c⟩

/-- The standard Clarke multifunction is a singleton on any affine neighborhood. -/
theorem clarkeSubdiff_locally_affine {f : Point → ℝ} {z w : Point} {c : ℝ}
    (heq : f =ᶠ[𝓝 z] fun q => lin w q + c) : clarkeSubdiff f z = {w} := by
  simp [clarkeSubdiff, gradientLimits_locally_affine heq]

end Paper32

namespace Paper32
open Set Filter Topology

/-- Adding a constant leaves the genuine gradient-limit set unchanged. -/
lemma gradientLimits_add_const (f : Point → ℝ) (c : ℝ) (z : Point) :
    gradientLimits (fun q => f q+c) z = gradientLimits f z := by
  ext w
  constructor
  · rintro ⟨a,b,ha,hb,hd⟩
    refine ⟨a,b,ha,hb,?_⟩
    intro n
    convert (hd n).sub_const c using 1
    ext q
    simp
  · rintro ⟨a,b,ha,hb,hd⟩
    exact ⟨a,b,ha,hb,fun n => (hd n).add_const c⟩

lemma clarkeSubdiff_add_const (f : Point → ℝ) (c : ℝ) (z : Point) :
    clarkeSubdiff (fun q => f q+c) z = clarkeSubdiff f z := by
  simp only [clarkeSubdiff, gradientLimits_add_const]

lemma F_eventually_eq_core {z : Point} (hz : l1 z < 4) :
    F =ᶠ[𝓝 z] fun q => g q+8 := by
  have hc : Continuous l1 := by unfold l1; fun_prop
  filter_upwards [hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds hz)] with q hq
  exact F_eq_core hq

/-- The standard Clarke multifunction forces the ordinary tilted gradient off N. -/
theorem clarke_tilt_off_singular {v z : Point} (hz : l1 z < 4)
    (hx : z.1 ≠ 0) (hy : z.2 ≠ 0) (hb : |z.2| ≠ 2*|z.1|) :
    clarkeSubdiff (tilt v) z = {gradCore z-v} :=
  clarkeSubdiff_locally_affine (tilt_locally_affine hz hx hy hb)

end Paper32

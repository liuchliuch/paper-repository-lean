import Paper28.NeighborhoodPushforwardInput
import Mathlib.Analysis.Normed.Group.Basic

/-! Extend an actual map on an open neighborhood by the identity outside.
The extension preserves the exact local Lipschitz constant on the open
set. The extension outside that set is only a total-function convenience. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Set
open scoped Classical
open scoped Topology
variable {X : Type*} [MetricSpace X]

def openNeighborhoodExtension (U : Set X) (f : U → X) (x : X) : X :=
  if hx : x ∈ U then f ⟨x,hx⟩ else x

theorem openNeighborhoodExtension_apply {U : Set X} (f : U → X) (x : X) (hx : x ∈ U) :
    openNeighborhoodExtension U f x = f ⟨x,hx⟩ := dif_pos hx

theorem openNeighborhoodExtension_local_constant (U : Set X) (hU : IsOpen U) (f : U → X)
    (L : NNReal) (hf : ∀ q, ∃ V : Set U, V ∈ 𝓝 q ∧ LipschitzOnWith L f V) :
    ∀ x ∈ U, ∃ V : Set X, V ∈ 𝓝 x ∧ LipschitzOnWith L (openNeighborhoodExtension U f) V := by
  intro x hx
  obtain ⟨V,hV,hLip⟩ := hf ⟨x,hx⟩
  obtain ⟨W,hW,hWV⟩ := (mem_nhds_subtype U ⟨x,hx⟩ V).mp hV
  refine ⟨W ∩ U,inter_mem hW (hU.mem_nhds hx),LipschitzOnWith.of_dist_le_mul ?_⟩
  intro y hy z hz
  rw [openNeighborhoodExtension_apply f y hy.2,openNeighborhoodExtension_apply f z hz.2]
  exact hLip.dist_le_mul ⟨y,hy.2⟩ (hWV hy.1) ⟨z,hz.2⟩ (hWV hz.1)

theorem openNeighborhoodExtension_near_lipschitz (U : Set X) (hU : IsOpen U) (f : U → X)
    (L : NNReal) (hf : ∀ q, ∃ V : Set U, V ∈ 𝓝 q ∧ LipschitzOnWith L f V) :
    LipschitzNearSet inferInstance inferInstance (openNeighborhoodExtension U f) U := by
  intro x hx
  obtain ⟨V,hV,hLip⟩ := openNeighborhoodExtension_local_constant U hU f L hf x hx
  exact ⟨L,V,hV,hLip⟩

theorem exists_positive_eta_mass_control (k : ℕ) (m ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ (1+η)^k*m ≤ m+ε := by
  have ho : IsOpen {η : ℝ | (1+η)^k*m < m+ε} := isOpen_lt (by fun_prop) continuous_const
  have h0 : (0 : ℝ) ∈ {η : ℝ | (1+η)^k*m < m+ε} := by
    simp only [Set.mem_setOf_eq,add_zero,one_pow,one_mul]
    linarith
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp ho 0 h0
  refine ⟨r/2,by positivity,(hball ?_).le⟩
  simp only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < r/2)]
  linarith

end Paper28

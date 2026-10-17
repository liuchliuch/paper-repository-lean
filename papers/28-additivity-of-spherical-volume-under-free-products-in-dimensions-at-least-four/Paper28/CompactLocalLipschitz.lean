import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Isometry

/-! The compact local-to-global Lipschitz argument used by the homotopy:
a Lebesgue number controls close pairs and bounded image controls far pairs. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Metric Set
open scoped Topology
variable {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]

theorem exists_lipschitzWith_of_compactSpace [CompactSpace X]
    (f : X → Y) (hf : LocallyLipschitz f) : ∃ L : NNReal, LipschitzWith L f := by
  classical
  have hball : ∀ x : X, ∃ L : NNReal, ∃ r : ℝ, 0 < r ∧ LipschitzOnWith L f (ball x r) := by
    intro x
    obtain ⟨L,s,hs,hL⟩ := hf x
    obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hs
    exact ⟨L,r,hr,hL.mono hrs⟩
  choose L r hr hLip using hball
  have hcover : (univ : Set X) ⊆ ⋃ x : X, ball x (r x) := by
    intro x _
    exact mem_iUnion.mpr ⟨x,by simpa using hr x⟩
  obtain ⟨C,hC⟩ := isCompact_univ.elim_finite_subcover (fun x : X => ball x (r x))
    (fun _ => isOpen_ball) hcover
  have hcoverC : (univ : Set X) ⊆ ⋃ x : C, ball x.val (r x.val) := by
    intro x hx
    obtain ⟨y,hy⟩ := mem_iUnion.mp (hC hx)
    obtain ⟨hyC,hxy⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨⟨y,hyC⟩,hxy⟩
  obtain ⟨δ,hδ,hδC⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun x : C => isOpen_ball (x := x.val) (ε := r x.val)) hcoverC
  obtain ⟨B,hB0,hB⟩ := (Metric.isBounded_iff_exists_ge 0).mp
    (isCompact_univ.image hf.continuous).isBounded
  let L0 : NNReal := C.sup L
  let L1 : NNReal := ⟨max (L0 : ℝ) (B/δ),le_trans L0.coe_nonneg (le_max_left _ _)⟩
  refine ⟨L1,LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  by_cases hxy : dist y x < δ
  · obtain ⟨z,hz⟩ := hδC x (mem_univ _)
    have hxz : x ∈ ball z.val (r z.val) := hz (by simpa using hδ)
    have hyz : y ∈ ball z.val (r z.val) := hz hxy
    have hLL : L z.val ≤ L0 := Finset.le_sup z.property
    have hLL' : (L z.val : ℝ) ≤ (L1 : ℝ) :=
      (show (L z.val : ℝ) ≤ (L0 : ℝ) from hLL).trans (le_max_left _ _)
    exact (hLip z.val |>.dist_le_mul x hxz y hyz).trans
      (mul_le_mul_of_nonneg_right hLL' dist_nonneg)
  · have hd : δ ≤ dist x y := by simpa only [dist_comm] using not_lt.mp hxy
    have hfar : B ≤ (L1 : ℝ)*dist x y := by
      have hb : B/δ ≤ (L1 : ℝ) := le_max_right _ _
      have hb' : B ≤ (L1 : ℝ)*δ := (div_le_iff₀ hδ).mp hb
      exact hb'.trans (mul_le_mul_of_nonneg_left hd L1.coe_nonneg)
    exact (hB (mem_image_of_mem f (mem_univ x)) (mem_image_of_mem f (mem_univ y))).trans hfar

theorem exists_lipschitzWith_compact_restriction
    {T : Type*} [MetricSpace T] [CompactSpace T]
    (U K : Set X) (hK : IsCompact K) (hKU : K ⊆ U)
    (f : T×U → Y) (hf : LocallyLipschitz f) :
    ∃ L : NNReal, LipschitzWith L
      (fun p : T×K => f (p.1,⟨p.2.val,hKU p.2.property⟩)) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let e : T×K → T×U := fun p => (p.1,⟨p.2.val,hKU p.2.property⟩)
  have he : Isometry e := Isometry.of_dist_eq (fun _ _ => rfl)
  exact exists_lipschitzWith_of_compactSpace _ (hf.comp he.lipschitz.locallyLipschitz)

end Paper28

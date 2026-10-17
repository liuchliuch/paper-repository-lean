import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Module

/-! A common Lipschitz constant glues over a finite closed cover of a
real interval. The proof deletes one closed piece at its last point and
uses the actual interval length, so the constant is preserved. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set Metric
variable {Idx Y : Type*} [DecidableEq Idx] [PseudoMetricSpace Y]

theorem finite_closed_cover_dist_bound (s : Finset Idx) (cells : Idx → Set ℝ) (f : ℝ → Y)
    (L : NNReal) (a b : ℝ) (hab : a ≤ b)
    (hClosed : ∀ j ∈ s, IsClosed (cells j))
    (hLip : ∀ j ∈ s, LipschitzOnWith L f (cells j ∩ Icc a b))
    (hCover : Icc a b ⊆ ⋃ j ∈ s, cells j) : dist (f a) (f b) ≤ (L : ℝ)*(b-a) := by
  classical
  induction s using Finset.strongInductionOn generalizing a b with
  | _ s ih =>
    obtain ⟨j,hjs,hja⟩ := mem_iUnion₂.mp (hCover ⟨le_rfl,hab⟩)
    obtain ⟨c,hc,hmax⟩ := (isCompact_Icc.inter_right (hClosed j hjs)).exists_isGreatest ⟨a,⟨le_rfl,hab⟩,hja⟩
    have hac : a ≤ c := hc.1.1
    have hcb : c ≤ b := hc.1.2
    have hca : c ∈ cells j := hc.2
    have hLeft : dist (f a) (f c) ≤ (L : ℝ)*(c-a) := by
      have h := (hLip j hjs).dist_le_mul a ⟨hja,le_rfl,hab⟩ c ⟨hca,hac,hcb⟩
      simpa only [Real.dist_eq,abs_sub_comm a c,abs_of_nonneg (sub_nonneg.mpr hac)] using h
    by_cases he : c = b
    · simpa only [he] using hLeft
    · have hcb' : c < b := lt_of_le_of_ne hcb he
      have hRemClosed : IsClosed (⋃ l ∈ s.erase j, cells l) :=
        isClosed_biUnion_finset (fun l hl => hClosed l (Finset.mem_of_mem_erase hl))
      have hRem : Ioc c b ⊆ ⋃ l ∈ s.erase j, cells l := by
        intro t ht
        have htOrig : t ∈ Icc a b := ⟨hac.trans ht.1.le,ht.2⟩
        obtain ⟨l,hls,hlt⟩ := mem_iUnion₂.mp (hCover htOrig)
        have hlj : l ≠ j := by
          intro he
          subst l
          exact (not_le_of_gt ht.1) (hmax ⟨htOrig,hlt⟩)
        exact mem_iUnion₂.mpr ⟨l,Finset.mem_erase.mpr ⟨hlj,hls⟩,hlt⟩
      have hRemCover : Icc c b ⊆ ⋃ l ∈ s.erase j, cells l := by
        rw [← closure_Ioc hcb'.ne]
        exact (closure_mono hRem).trans hRemClosed.closure_subset
      have hRight : dist (f c) (f b) ≤ (L : ℝ)*(b-c) :=
        ih (s.erase j) (Finset.erase_ssubset hjs) c b hcb
          (fun l hl => hClosed l (Finset.mem_of_mem_erase hl))
          (fun l hl => (hLip l (Finset.mem_of_mem_erase hl)).mono
            (fun t ht => ⟨ht.1,hac.trans ht.2.1,ht.2.2⟩)) hRemCover
      calc
        _ ≤ dist (f a) (f c)+dist (f c) (f b) := dist_triangle _ _ _
        _ ≤ (L : ℝ)*(c-a)+(L : ℝ)*(b-c) := add_le_add hLeft hRight
        _ = (L : ℝ)*(b-a) := by ring

theorem lipschitzOn_finite_closed_cover_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset Idx) (cells : Idx → Set E) (N : Set E) (hN : Convex ℝ N)
    (f : E → Y) (L : NNReal) (hClosed : ∀ j ∈ s, IsClosed (cells j))
    (hLip : ∀ j ∈ s, LipschitzOnWith L f (cells j ∩ N))
    (hCover : N ⊆ ⋃ j ∈ s, cells j) : LipschitzOnWith L f N := by
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  let γ : ℝ → E := fun t => a+t • (b-a)
  have hγ : LipschitzWith ‖b-a‖₊ γ := by
    apply LipschitzWith.of_dist_le_mul
    intro t u
    have he : γ t-γ u = (t-u) • (b-a) := by dsimp [γ]; module
    rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,Real.dist_eq]
    exact le_of_eq (mul_comm |t-u| ‖b-a‖)
  have hγN : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ N := by
    intro t ht
    have he : γ t = (1-t) • a+t • b := by dsimp [γ]; module
    rw [he]
    exact hN ha hb (by linarith [ht.2]) ht.1 (by ring)
  have hBound := finite_closed_cover_dist_bound s (fun j => γ ⁻¹' cells j) (fun t => f (γ t))
    (L*‖b-a‖₊) 0 1 (by norm_num)
    (fun j hj => (hClosed j hj).preimage hγ.continuous) (fun j hj => ?_)
    (fun t ht => by
      obtain ⟨j,hj,hm⟩ := mem_iUnion₂.mp (hCover (hγN t ht))
      exact mem_iUnion₂.mpr ⟨j,hj,hm⟩)
  · simpa only [γ,zero_smul,add_zero,one_smul,add_sub_cancel,sub_zero,NNReal.coe_mul,
      coe_nnnorm,mul_one,dist_eq_norm,norm_sub_rev] using hBound
  · apply LipschitzOnWith.of_dist_le_mul
    intro t ht u hu
    exact ((hLip j hj).dist_le_mul (γ t) ⟨ht.1,hγN t ht.2⟩ (γ u) ⟨hu.1,hγN u hu.2⟩).trans
      (by simpa only [NNReal.coe_mul,coe_nnnorm,mul_assoc] using
        mul_le_mul_of_nonneg_left (hγ.dist_le_mul t u) L.coe_nonneg)

end Paper28

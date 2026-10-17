import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-! Separation of a compact convex attainable set from a cone upper closure.
This supplies the strong-duality step for the fixed-distribution MC program. -/
open scoped Pointwise
open Set
noncomputable section
namespace Paper22

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Strict separation gives a positive dual multiplier for a compact convex
attainable set. The scalar multiplier is positive because a zero-resource
attainable point is available. -/
theorem compact_cone_dual_certificate
    {K : Set (E × ℝ)} (hKconv : Convex ℝ K) (hKcompact : IsCompact K)
    {C : Set E} (hCconv : Convex ℝ C) (hCclosed : IsClosed C)
    (hCzero : (0:E) ∈ C) (hCsmul : ∀ {r : ℝ}, 0 ≤ r → ∀ {x}, x ∈ C → r • x ∈ C)
    {b₀ : ℝ} (hzero : ((0:E),b₀) ∈ K)
    {x : E} (hx : x ∈ C) {a : ℝ}
    (hout : (x,a) ∉ K + (C ×ˢ Ici 0)) :
    ∃ (g : E →L[ℝ] ℝ) (β : ℝ), 0 < β ∧ (∀ y ∈ C, 0 ≤ g y) ∧
      ∀ z ∈ K, g x + β*a < g z.1 + β*z.2 := by
  let U : Set (E × ℝ) := C ×ˢ Ici 0
  have hUconv : Convex ℝ U := hCconv.prod (convex_Ici 0)
  have hUclosed : IsClosed U := hCclosed.prod isClosed_Ici
  obtain ⟨f,u,hpoint,hsep⟩ := geometric_hahn_banach_point_closed
    (hKconv.add hUconv) (hUclosed.add_left_of_isCompact hKcompact) hout
  let g : E →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let β : ℝ := f (0,1)
  have hdecomp (y : E) (t : ℝ) : f (y,t) = g y + β*t := by
    have hp : (y,t) = (y,0) + t • ((0:E),(1:ℝ)) := by ext <;> simp
    rw [hp, map_add, map_smul]
    change g y + t*β = g y + β*t
    ring
  have hpositive (v : E × ℝ) (hv : v ∈ U) : 0 ≤ f v := by
    by_contra hn
    have hneg : f v < 0 := lt_of_not_ge hn
    obtain ⟨N,hN⟩ := exists_nat_gt ((f (0,b₀)-u) / (-f v))
    have hN' := (div_lt_iff₀ (neg_pos.mpr hneg)).mp hN
    have hNv : N • v ∈ U := by
      constructor
      · simpa only [Prod.smul_fst, Nat.cast_smul_eq_nsmul] using
          hCsmul (Nat.cast_nonneg N) hv.1
      · change 0 ≤ N • v.2
        exact nsmul_nonneg (show 0 ≤ v.2 from hv.2) N
    have hlt := hsep ((0,b₀) + N • v) (Set.mem_add.mpr ⟨(0,b₀),hzero,N • v,hNv,rfl⟩)
    rw [map_add, map_nsmul, nsmul_eq_mul] at hlt
    nlinarith
  have hg : ∀ y ∈ C, 0 ≤ g y := by
    intro y hy
    simpa only [hdecomp, mul_zero, add_zero] using hpositive (y,0) ⟨hy,by simp⟩
  have hb : 0 ≤ β := hpositive (0,1) ⟨hCzero,by norm_num⟩
  have hβ : 0 < β := by
    by_contra hβ
    have hz : β = 0 := le_antisymm (le_of_not_gt hβ) hb
    have hlt := hpoint.trans (hsep (0,b₀) (Set.mem_add.mpr
      ⟨(0,b₀),hzero,0,⟨hCzero,by simp⟩,by simp⟩))
    rw [hdecomp, hdecomp, hz, zero_mul, zero_mul, add_zero, add_zero, map_zero] at hlt
    exact (hg x hx).not_gt hlt
  refine ⟨g,β,hβ,hg,?_⟩
  intro z hz
  have hlt := hpoint.trans (hsep z (Set.mem_add.mpr
    ⟨z,hz,0,⟨hCzero,by simp⟩,by simp⟩))
  simpa only [hdecomp] using hlt

end Paper22
end

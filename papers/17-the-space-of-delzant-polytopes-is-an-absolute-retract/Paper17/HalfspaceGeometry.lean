import Paper17.SupportBounds
import Paper17.ConeMultiplicity
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Order.Filter.Finite

/-!
# Geometry of finitely many supporting halfspaces

Finite slack bounds give actual feasible small motions. Consequently the
active constraints at an extreme point have trivial common tangent kernel.
These facts underpin the geometric polytopal realization of stellar steps.
-/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace Paper17
section
variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- The actual intersection of finitely many closed supporting halfspaces. -/
def finiteHalfspaces (a : ι → V n) (h : ι → ℝ) : Set (V n) :=
  {x | ∀ i, dot (a i) x ≤ h i}

theorem finiteHalfspaces_convex (a : ι → V n) (h : ι → ℝ) :
    Convex ℝ (finiteHalfspaces a h) := by
  rw [convex_iff_add_mem]
  intro x hx y hy α β hα hβ hsum i
  rw [dot_add_right, dot_smul_right, dot_smul_right]
  calc α * dot (a i) x + β * dot (a i) y ≤ α * h i + β * h i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) hα) (mul_le_mul_of_nonneg_left (hy i) hβ)
    _ = h i := by rw [← add_mul, hsum, one_mul]

theorem finiteHalfspaces_isClosed (a : ι → V n) (h : ι → ℝ) :
    IsClosed (finiteHalfspaces a h) := by
  have hc := isClosed_iInter (fun i => isClosed_le (continuous_dot (a i))
    (continuous_const : Continuous (fun _ : V n => h i)))
  simpa only [finiteHalfspaces, Set.setOf_forall] using hc

/-- The constraints that are actually active at a point. -/
def activeConstraints (a : ι → V n) (h : ι → ℝ) (x : V n) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => dot (a i) x = h i)

@[simp] theorem mem_activeConstraints (a : ι → V n) (h : ι → ℝ) (x : V n) (i : ι) :
    i ∈ activeConstraints a h x ↔ dot (a i) x = h i := by
  classical
  simp [activeConstraints]

/-- There is an actual uniform small-motion radius for all inactive
constraints. The remaining active constraints are tested by their slopes. -/
theorem finiteHalfspaces_small_motion (a : ι → V n) (h : ι → ℝ)
    {x : V n} (hx : x ∈ finiteHalfspaces a h) (v : V n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      (∀ i ∈ activeConstraints a h x, t * dot (a i) v ≤ 0) →
      x + t • v ∈ finiteHalfspaces a h := by
  have hlocal : ∀ i : ι, ∀ᶠ t : ℝ in 𝓝 0,
      i ∈ activeConstraints a h x ∨ dot (a i) (x + t • v) < h i := by
    intro i
    by_cases hi : i ∈ activeConstraints a h x
    · exact Filter.Eventually.of_forall (fun _ => Or.inl hi)
    · have hstrict : dot (a i) x < h i := lt_of_le_of_ne (hx i)
        (fun heq => hi ((mem_activeConstraints a h x i).mpr heq))
      have hc : Continuous (fun t : ℝ => dot (a i) (x + t • v)) :=
        (continuous_dot (a i)).comp (continuous_const.add (continuous_id.smul continuous_const))
      have hevent : ∀ᶠ t : ℝ in 𝓝 0, dot (a i) (x + t • v) < h i := by
        have hz : dot (a i) (x + (0 : ℝ) • v) < h i := by simpa only [zero_smul, add_zero] using hstrict
        exact (isOpen_lt hc continuous_const).mem_nhds hz
      exact hevent.mono (fun _ ht => Or.inr ht)
  have hAll := Filter.eventually_all.mpr hlocal
  obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff.mp hAll
  refine ⟨δ, hδ, ?_⟩
  intro t ht hslope i
  have hdist : dist t 0 < δ := by simpa only [dist_zero_right, Real.norm_eq_abs] using ht
  rcases hbound hdist i with hi | hi
  · rw [dot_add_right, dot_smul_right, (mem_activeConstraints a h x i).mp hi]
    linarith [hslope i hi]
  · exact hi.le

/-- A direction that is tangent to every active constraint permits motion in
both signs near the point. -/
theorem finiteHalfspaces_tangent_motion (a : ι → V n) (h : ι → ℝ)
    {x : V n} (hx : x ∈ finiteHalfspaces a h) (v : V n)
    (hv : ∀ i ∈ activeConstraints a h x, dot (a i) v = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → x + t • v ∈ finiteHalfspaces a h := by
  obtain ⟨δ, hδ, hbound⟩ := finiteHalfspaces_small_motion a h hx v
  exact ⟨δ, hδ, fun t ht => hbound t ht (fun i hi => by rw [hv i hi, mul_zero])⟩

/-- A nonzero common tangent at an extreme point would give a genuine
nontrivial feasible segment through it. -/
theorem extreme_active_kernel_eq_zero (a : ι → V n) (h : ι → ℝ)
    {x : V n} (hx : x ∈ (finiteHalfspaces a h).extremePoints ℝ) (v : V n)
    (hv : ∀ i ∈ activeConstraints a h x, dot (a i) v = 0) : v = 0 := by
  obtain ⟨δ, hδ, hbound⟩ := finiteHalfspaces_tangent_motion a h hx.1 v hv
  let t : ℝ := δ / 2
  have ht : 0 < t := div_pos hδ (by norm_num)
  have htd : |t| < δ := by rw [abs_of_pos ht]; dsimp [t]; linarith
  have hplus := hbound t htd
  have hminus := hbound (-t) (by simpa only [abs_neg] using htd)
  have hsegment : x ∈ openSegment ℝ (x + t • v) (x + (-t) • v) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have heq := (mem_extremePoints.mp hx).2 _ hplus _ hminus hsegment
  have hz : t • v = 0 := by
    apply add_left_cancel (a := x)
    simpa only [add_zero] using heq.1
  exact (smul_eq_zero.mp hz).resolve_left ht.ne'

/-- Evaluation by active normals, as an actual real linear map. -/
def activeEvaluation (a : ι → V n) (h : ι → ℝ) (x : V n) :
    V n →ₗ[ℝ] (activeConstraints a h x → ℝ) where
  toFun v := fun i => dot (a i.val) v
  map_add' v w := by ext i; exact dot_add_right _ _ _
  map_smul' t v := by ext i; exact dot_smul_right _ _ _

theorem extreme_activeEvaluation_injective (a : ι → V n) (h : ι → ℝ)
    {x : V n} (hx : x ∈ (finiteHalfspaces a h).extremePoints ℝ) :
    Function.Injective (activeEvaluation a h x) := by
  intro v w heq
  apply sub_eq_zero.mp
  apply extreme_active_kernel_eq_zero a h hx (v - w)
  intro i hi
  have hh := congrFun heq ⟨i, hi⟩
  change dot (a i) v = dot (a i) w at hh
  change ∑ j, a i j * (v j - w j) = 0
  simp only [mul_sub, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr hh

/-- Every extreme point has at least `n` active constraints. Under generic
heights there are at most `n`, so the active matrix is square and invertible. -/
theorem extreme_active_card_ge (a : ι → V n) (h : ι → ℝ)
    {x : V n} (hx : x ∈ (finiteHalfspaces a h).extremePoints ℝ) :
    n ≤ (activeConstraints a h x).card := by
  have hh := LinearMap.finrank_le_finrank_of_injective (extreme_activeEvaluation_injective a h hx)
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_coe] using hh

end
end Paper17

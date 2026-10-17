import Paper17.ChainPartition
import Paper17.NerveLabels

/-!
# Global extension by face-compatible labels

Two actual subordinate partitions of unity perform the barycentric gluing.
The strict upper-level faces of the first partition form a locally finite open
cover; active faces of a subordinate second partition are nested. This makes
chain interpolation globally continuous without a dimension bound.
-/
noncomputable section
open scoped Topology BigOperators
open Set Filter Function
namespace Paper17

/-- Locally, all values lie in the convex hull of one finite set of labels in
`Y`. The neighborhood is taken in the full source space. -/
def LocallyFiniteConvexLabels {X E : Type*} [TopologicalSpace X]
    [AddCommGroup E] [Module ℝ E] (F : X → E) (D : Set X) (Y : Set E) : Prop :=
  ∀ x ∈ D, ∃ U ∈ 𝓝 x, ∃ s : Finset E,
    (↑s : Set E) ⊆ Y ∧ ∀ y ∈ U, F y ∈ convexHull ℝ (↑s : Set E)

/-- Theorem 3.1, with the global cover, recursive labels, interpolation and
continuity at every prescribed boundary value constructed in the proof. -/
theorem extension_by_barycentric_cover_controlled {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Y : Set E} {r : E → E → Prop} (hY : Y.Nonempty) (h : ExtensionHypotheses Y r) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X), IsClosed A →
      ∀ f : A → E, Continuous f → (∀ a, f a ∈ Y) →
      ∃ F : X → E, Continuous F ∧ (∀ x, F x ∈ Y) ∧ (∀ a : A, F a = f a) ∧
        LocallyFiniteConvexLabels F Aᶜ Y := by
  classical
  intro X _ A hA f hf hfY
  by_cases hA0 : A = ∅
  · obtain ⟨y₀, hy₀⟩ := hY
    refine ⟨fun _ => y₀, continuous_const, fun _ => hy₀, ?_, ?_⟩
    · intro a
      exact False.elim (by simpa [hA0] using a.property)
    · intro x _
      refine ⟨Set.univ, Filter.univ_mem, {y₀}, ?_, ?_⟩
      · simpa only [Finset.coe_singleton, Set.singleton_subset_iff] using hy₀
      · intro y _
        exact subset_convexHull ℝ _ (by simp)
  have hAne : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA0
  obtain ⟨y₀, hy₀⟩ := hY
  let Z := ↥Aᶜ
  let d : Z → ℝ := fun z => Metric.infDist z.val A
  have hd : ∀ z, 0 < d z := fun z => (hA.notMem_iff_infDist_pos hAne).mp z.property
  have haex : ∀ z : Z, ∃ a : A, dist z.val a.val < 2 * d z := by
    intro z
    obtain ⟨a, ha, hda⟩ := exists_approx_minimizer hAne (z := z.val) rfl (hd z)
    exact ⟨⟨a, ha⟩, hda⟩
  choose a had using haex
  let U : Z → Set Z := fun z => Metric.ball z (d z / 4)
  have hUcover : (Set.univ : Set Z) ⊆ ⋃ z, U z := by
    intro z _
    exact Set.mem_iUnion.mpr ⟨z, Metric.mem_ball_self (div_pos (hd z) (by norm_num))⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : PartitionOfUnity Z Z Set.univ, φ.IsSubordinate U :=
    PartitionOfUnity.exists_isSubordinate isClosed_univ U (fun z => Metric.isOpen_ball) hUcover
  let V : Finset Z → Set Z := strictFace (fun i x => φ i x)
  have hVopen : ∀ s, IsOpen (V s) :=
    isOpen_strictFace (fun i => (φ i).continuous) φ.locallyFinite
  have hVcover : (Set.univ : Set Z) ⊆ ⋃ s, V s := by
    rw [strictFace_cover φ]
  obtain ⟨β, hβ⟩ : ∃ β : PartitionOfUnity (Finset Z) Z Set.univ, β.IsSubordinate V :=
    PartitionOfUnity.exists_isSubordinate isClosed_univ V hVopen hVcover
  have hface : ∀ (x : Z) (s : Finset Z), β s x ≠ 0 → x ∈ V s := by
    intro x s hs
    exact hβ s (subset_tsupport _ (Function.mem_support.mpr hs))
  let target : Finset Z → ↥Y := fun s =>
    if hs : s.Nonempty then ⟨f (a hs.choose), hfY _⟩ else ⟨y₀, hy₀⟩
  let radius : Finset Z → ℝ := fun s => if hs : s.Nonempty then d hs.choose else 1
  have hrad : ∀ s, 0 < radius s := by
    intro s
    dsimp [radius]
    split_ifs
    · exact hd _
    · norm_num
  let q := nerveLabel h target radius hrad
  have hq : ∀ s, (q s).val ∈ Y := fun s => (q s).property
  have hqmono : ∀ s t, s.Nonempty → s ⊆ t → r (q s).val (q t).val := by
    intro s t hs hst
    by_cases heq : s = t
    · subst t
      exact h.refl _ (hq s)
    · exact (nerveLabel_spec h target radius hrad t).2 s hs
        (Finset.ssubset_iff_subset_ne.mpr ⟨hst, heq⟩)
  let G : Z → E := fun x => ∑ᶠ s, β s x • (q s).val
  have hGc : Continuous G := β.continuous_finsum_smul (fun s x hx => continuousAt_const)
  have hGY : ∀ x, G x ∈ Y := by
    intro x
    exact chain_partition_value_mem h β (fun s => (q s).val) hq hqmono x
      (fun s hs => (hface x s hs).1)
      (fun s t hs ht => strictFace_chain (hface x s hs) (hface x t ht))
  /- Every active face is anchored at an original partition index active at x. -/
  have hlabel : ∀ (x : Z) (s : Finset Z) (hs : β s x ≠ 0),
      ∃ i : Z, dist (q s).val (f (a i)) < d i ∧
        dist x.val i.val < d i / 4 := by
    intro x s hs
    have hfs := hface x s hs
    let i := hfs.1.choose
    have his : i ∈ s := hfs.1.choose_spec
    have hnear := (nerveLabel_spec h target radius hrad s).1
    change dist (q s).val (target s).val < radius s at hnear
    have htarget : (target s).val = f (a i) := by
      dsimp [target, i]
      rw [dif_pos hfs.1]
    have hradius : radius s = d i := by
      dsimp [radius, i]
      rw [dif_pos hfs.1]
    rw [htarget, hradius] at hnear
    have hipos : 0 < φ i x := hfs.2.1 i his
    have hxin : x ∈ U i := hφ i (subset_tsupport _ (Function.mem_support.mpr hipos.ne'))
    exact ⟨i, hnear, hxin⟩
  let F : X → E := fun x => if hx : x ∈ A then f ⟨x, hx⟩ else G ⟨x, hx⟩
  have hFeq : ∀ a : A, F a = f a := by
    intro a
    dsimp [F]
    rw [dif_pos a.property]
  have hFY : ∀ x, F x ∈ Y := by
    intro x
    dsimp [F]
    split_ifs
    · exact hfY _
    · exact hGY _
  have hFZ : ContinuousOn F Aᶜ := by
    apply continuousOn_iff_continuous_restrict.mpr
    have heq : (fun z : Z => F z.val) = G := by
      funext z
      dsimp [F]
      rw [dif_neg z.property]
    change Continuous (fun z : Z => F z.val)
    rw [heq]
    exact hGc
  have hFA : ∀ a₀ : A, ContinuousAt F a₀.val := by
    intro a₀
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    obtain ⟨δf, hδf, hfδ⟩ := (Metric.continuousAt_iff.mp hf.continuousAt)
      (ε / 2) (by positivity)
    let δ := min (3 * ε / 8) (δf / 4)
    refine ⟨δ, lt_min (by positivity) (by positivity), ?_⟩
    intro x hx
    rw [hFeq a₀]
    have hxε : dist x a₀.val < 3 * ε / 8 := hx.trans_le (min_le_left _ _)
    have hxf : dist x a₀.val < δf / 4 := hx.trans_le (min_le_right _ _)
    by_cases hxA : x ∈ A
    · have hdist : dist (⟨x, hxA⟩ : A) a₀ < δf := by
        change dist x a₀.val < δf
        linarith
      have hh := hfδ hdist
      have hFx : F x = f ⟨x, hxA⟩ := by dsimp [F]; rw [dif_pos hxA]
      rw [hFx]
      exact hh.trans (by linarith)
    · let z : Z := ⟨x, hxA⟩
      have hgz : G z ∈ Metric.ball (f a₀) ε := by
        apply β.finsum_smul_mem_convex (g := fun s _ => (q s).val)
          (Set.mem_univ z) _ (convex_ball (f a₀) ε)
        intro s hs
        obtain ⟨i, hqi, hzi⟩ := hlabel z s hs
        have hri : d i < (4 / 3 : ℝ) * dist x a₀.val := by
          have hscale := (scale_estimate hA (x := x) (z := i.val) (r := d i) hzi rfl hAne hxA).1
          exact hscale.trans_le (mul_le_mul_of_nonneg_left
            (Metric.infDist_le_dist_of_mem a₀.property) (by norm_num))
        have hanchor : dist (a i).val a₀.val < 4 * dist x a₀.val := by
          have h1 := dist_triangle (a i).val i.val a₀.val
          have h2 := dist_triangle i.val x a₀.val
          rw [dist_comm (a i).val i.val] at h1
          rw [dist_comm i.val x] at h2
          have hai := had i
          linarith
        have hanchorδ : dist (a i) a₀ < δf := by
          change dist (a i).val a₀.val < δf
          linarith
        have hfi : dist (f (a i)) (f a₀) < ε / 2 := hfδ hanchorδ
        have hsum := dist_triangle (q s).val (f (a i)) (f a₀)
        change dist (q s).val (f a₀) < ε
        linarith
      have hFx : F x = G z := by dsimp [F]; rw [dif_neg hxA]
      rw [hFx]
      exact hgz
  have hFc : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x ∈ A
    · exact hFA ⟨x, hx⟩
    · exact hFZ.continuousAt (hA.isOpen_compl.mem_nhds hx)
  refine ⟨F, hFc, hFY, hFeq, ?_⟩
  intro x hx
  let z : Z := ⟨x, hx⟩
  obtain ⟨t, ht, hfin⟩ := β.locallyFinite z
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ht
  let s : Finset E := hfin.toFinset.image (fun i => (q i).val)
  refine ⟨Metric.ball x ε ∩ Aᶜ, Filter.inter_mem (Metric.ball_mem_nhds x hε)
    (hA.isOpen_compl.mem_nhds hx), s, ?_, ?_⟩
  · intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact hq i
  · intro y hy
    let y' : Z := ⟨y, hy.2⟩
    have hyt : y' ∈ t := hball hy.1
    have hFy : F y = G y' := by dsimp [F]; rw [dif_neg hy.2]
    rw [hFy]
    apply β.finsum_smul_mem_convex (g := fun i _ => (q i).val)
      (Set.mem_univ y') _ (convex_convexHull ℝ _)
    intro i hi
    apply subset_convexHull ℝ _
    apply Finset.mem_image.mpr
    exact ⟨i, hfin.mem_toFinset.mpr ⟨y', hi, hyt⟩, rfl⟩

/-- The extension criterion, forgetting its additional finite-label control. -/
theorem extension_by_barycentric_cover {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Y : Set E} {r : E → E → Prop} (hY : Y.Nonempty) (h : ExtensionHypotheses Y r) :
    IsAbsoluteExtensor Y := by
  intro X _ A hA f hf hfY
  obtain ⟨F, hFc, hFY, hFeq, _⟩ :=
    extension_by_barycentric_cover_controlled hY h X A hA f hf hfY
  exact ⟨F, hFc, hFY, hFeq⟩

/-- **Theorem 3.1**: the original extension criterion, proved by the constructed
barycentric cover and boundary estimates above. -/
theorem theorem_3_1 {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Y : Set E} {preceq : E → E → Prop}
    (hY : Y.Nonempty) (h : ExtensionHypotheses Y preceq) : IsAbsoluteExtensor Y :=
  extension_by_barycentric_cover hY h

end Paper17

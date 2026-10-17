import Paper17.ContinuousApproximation

/-! Chain interpolation of arbitrary cover labels with quantitative control
through a linear Lipschitz map. The comparison function need not be continuous;
its local label bounds are supplied by the actual open cover. -/
noncomputable section
open scoped Topology BigOperators
open Set Function Filter
namespace Paper17

theorem labelled_approximation_through_linear_map
    {X E F ι : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Y : Set E} {r : E → E → Prop} (hY : Y.Nonempty) (h : ExtensionHypotheses Y r)
    (p : ι → ↥Y) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (U : ι → Set X) (hUopen : ∀ i, IsOpen (U i)) (hUcover : (Set.univ : Set X) ⊆ ⋃ i, U i)
    (T : E →ₗ[ℝ] F) {C : NNReal} (hT : LipschitzWith C T)
    (D : Set X) (f : X → F) (ε : X → ℝ)
    (hbudget : ∀ x ∈ D, ∀ i, x ∈ U i → (C : ℝ) * δ i + dist (T (p i).val) (f x) ≤ ε x) :
    ∃ G : X → E, Continuous G ∧ (∀ x, G x ∈ Y) ∧
      (∀ x ∈ D, dist (T (G x)) (f x) ≤ ε x) ∧ LocallyFiniteConvexLabels G Set.univ Y := by
  classical
  obtain ⟨y₀, hy₀⟩ := hY
  obtain ⟨φ, hφ⟩ : ∃ φ : PartitionOfUnity ι X Set.univ, φ.IsSubordinate U :=
    PartitionOfUnity.exists_isSubordinate isClosed_univ U hUopen hUcover
  let V : Finset ι → Set X := strictFace (fun i x => φ i x)
  have hVopen : ∀ s, IsOpen (V s) :=
    isOpen_strictFace (fun i => (φ i).continuous) φ.locallyFinite
  have hVcover : (Set.univ : Set X) ⊆ ⋃ s, V s := by rw [strictFace_cover φ]
  obtain ⟨β, hβ⟩ : ∃ β : PartitionOfUnity (Finset ι) X Set.univ, β.IsSubordinate V :=
    PartitionOfUnity.exists_isSubordinate isClosed_univ V hVopen hVcover
  have hface : ∀ x s, β s x ≠ 0 → x ∈ V s := by
    intro x s hs
    exact hβ s (subset_tsupport _ (Function.mem_support.mpr hs))
  let target : Finset ι → ↥Y := fun s => if hs : s.Nonempty then p hs.choose else ⟨y₀, hy₀⟩
  let radius : Finset ι → ℝ := fun s => if hs : s.Nonempty then δ hs.choose else 1
  have hrad : ∀ s, 0 < radius s := by
    intro s
    dsimp [radius]
    split_ifs with hs
    · exact hδ _
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
  let G : X → E := fun x => ∑ᶠ s, β s x • (q s).val
  have hGc : Continuous G := β.continuous_finsum_smul (fun s x hx => continuousAt_const)
  have hGY : ∀ x, G x ∈ Y := by
    intro x
    exact chain_partition_value_mem h β (fun s => (q s).val) hq hqmono x
      (fun s hs => (hface x s hs).1)
      (fun s t hs ht => strictFace_chain (hface x s hs) (hface x t ht))
  refine ⟨G, hGc, hGY, ?_, ?_⟩
  · intro x hxD
    change G x ∈ T ⁻¹' Metric.closedBall (f x) (ε x)
    apply β.finsum_smul_mem_convex (g := fun s _ => (q s).val)
      (Set.mem_univ x) _ ((convex_closedBall (f x) (ε x)).linear_preimage T)
    intro s hs
    have hfs := hface x s hs
    let i := hfs.1.choose
    have his : i ∈ s := hfs.1.choose_spec
    have hnear := (nerveLabel_spec h target radius hrad s).1
    change dist (q s).val (target s).val < radius s at hnear
    have htarget : (target s).val = (p i).val := by
      dsimp [target, i]
      rw [dif_pos hfs.1]
    have hradius : radius s = δ i := by
      dsimp [radius, i]
      rw [dif_pos hfs.1]
    rw [htarget, hradius] at hnear
    have hipos : 0 < φ i x := hfs.2.1 i his
    have hxU : x ∈ U i := hφ i (subset_tsupport _ (Function.mem_support.mpr hipos.ne'))
    change dist (T (q s).val) (f x) ≤ ε x
    calc dist (T (q s).val) (f x)
        ≤ dist (T (q s).val) (T (p i).val) + dist (T (p i).val) (f x) := dist_triangle _ _ _
      _ ≤ (C : ℝ) * dist (q s).val (p i).val + dist (T (p i).val) (f x) :=
        add_le_add_right (hT.dist_le_mul _ _) _
      _ ≤ (C : ℝ) * δ i + dist (T (p i).val) (f x) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hnear.le C.coe_nonneg) _
      _ ≤ ε x := hbudget x hxD i hxU
  · intro x _
    obtain ⟨t, ht, hfin⟩ := β.locallyFinite x
    let s : Finset E := hfin.toFinset.image (fun i => (q i).val)
    refine ⟨t, ht, s, ?_, ?_⟩
    · intro v hv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      exact hq i
    · intro y hy
      apply β.finsum_smul_mem_convex (g := fun i _ => (q i).val)
        (Set.mem_univ y) _ (convex_convexHull ℝ _)
      intro i hi
      apply subset_convexHull ℝ _
      apply Finset.mem_image.mpr
      exact ⟨i, hfin.mem_toFinset.mpr ⟨y, hi, hy⟩, rfl⟩

end Paper17

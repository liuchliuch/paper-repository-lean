import Paper17.Dugundji

/-!
# Continuous approximation using refinement chains

Pointwise density supplies initial labels. The finite upper-bound property
makes them compatible across all faces, and two actual locally finite
partitions glue them into a continuous approximation with a prescribed
positive continuous error function. The output retains finite local labels.
-/
noncomputable section
open scoped Topology BigOperators
open Set Function Filter
namespace Paper17

/-- Continuous controlled approximation from pointwise density and the same
chain criterion used in Theorem 3.1. -/
theorem continuous_approximation_by_chains {X E : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Y : Set E} {r : E → E → Prop} (hY : Y.Nonempty) (h : ExtensionHypotheses Y r)
    (F : X → E) (hF : Continuous F) (ε : X → ℝ) (hε : Continuous ε)
    (hpos : ∀ x, 0 < ε x)
    (happrox : ∀ x (δ : ℝ), 0 < δ → ∃ p ∈ Y, dist p (F x) < δ) :
    ∃ G : X → E, Continuous G ∧ (∀ x, G x ∈ Y) ∧
      (∀ x, dist (G x) (F x) < ε x) ∧ LocallyFiniteConvexLabels G Set.univ Y := by
  classical
  obtain ⟨y₀, hy₀⟩ := hY
  have hex : ∀ i : X, ∃ p : ↥Y, dist p.val (F i) < ε i / 8 := by
    intro i
    obtain ⟨p, hp, hd⟩ := happrox i (ε i / 8) (div_pos (hpos i) (by norm_num))
    exact ⟨⟨p, hp⟩, hd⟩
  choose p hp using hex
  let U : X → Set X := fun i => {x | dist (F x) (F i) < ε i / 4 ∧ ε i < 2 * ε x}
  have hUopen : ∀ i, IsOpen (U i) := by
    intro i
    exact (isOpen_lt (hF.dist continuous_const) continuous_const).inter
      (isOpen_lt continuous_const (continuous_const.mul hε))
  have hUcover : (Set.univ : Set X) ⊆ ⋃ i, U i := by
    intro x _
    apply Set.mem_iUnion.mpr
    refine ⟨x, ?_, ?_⟩
    · change dist (F x) (F x) < ε x / 4
      simp only [dist_self]
      exact div_pos (hpos x) (by norm_num)
    · change ε x < 2 * ε x
      linarith [hpos x]
  obtain ⟨φ, hφ⟩ : ∃ φ : PartitionOfUnity X X Set.univ, φ.IsSubordinate U :=
    PartitionOfUnity.exists_isSubordinate isClosed_univ U hUopen hUcover
  let V : Finset X → Set X := strictFace (fun i x => φ i x)
  have hVopen : ∀ s, IsOpen (V s) :=
    isOpen_strictFace (fun i => (φ i).continuous) φ.locallyFinite
  have hVcover : (Set.univ : Set X) ⊆ ⋃ s, V s := by rw [strictFace_cover φ]
  obtain ⟨β, hβ⟩ : ∃ β : PartitionOfUnity (Finset X) X Set.univ, β.IsSubordinate V :=
    PartitionOfUnity.exists_isSubordinate isClosed_univ V hVopen hVcover
  have hface : ∀ x s, β s x ≠ 0 → x ∈ V s := by
    intro x s hs
    exact hβ s (subset_tsupport _ (Function.mem_support.mpr hs))
  let target : Finset X → ↥Y := fun s => if hs : s.Nonempty then p hs.choose else ⟨y₀, hy₀⟩
  let radius : Finset X → ℝ := fun s => if hs : s.Nonempty then ε hs.choose / 8 else 1
  have hrad : ∀ s, 0 < radius s := by
    intro s
    dsimp [radius]
    split_ifs with hs
    · exact div_pos (hpos hs.choose) (by norm_num)
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
  · intro x
    apply β.finsum_smul_mem_convex (g := fun s _ => (q s).val)
      (Set.mem_univ x) _ (convex_ball (F x) (ε x))
    intro s hs
    have hfs := hface x s hs
    let i := hfs.1.choose
    have his : i ∈ s := hfs.1.choose_spec
    have hnear := (nerveLabel_spec h target radius hrad s).1
    change dist (q s).val (target s).val < radius s at hnear
    have htarget : (target s).val = (p i).val := by
      dsimp [target, i]
      rw [dif_pos hfs.1]
    have hradius : radius s = ε i / 8 := by
      dsimp [radius, i]
      rw [dif_pos hfs.1]
    rw [htarget, hradius] at hnear
    have hipos : 0 < φ i x := hfs.2.1 i his
    have hxU : x ∈ U i := hφ i (subset_tsupport _ (Function.mem_support.mpr hipos.ne'))
    have hanchor : dist (F i) (F x) < ε i / 4 := by
      rw [dist_comm]
      exact hxU.1
    have htri := dist_triangle (q s).val (p i).val (F x)
    have htri' := dist_triangle (p i).val (F i) (F x)
    have hpi := hp i
    change dist (q s).val (F x) < ε x
    linarith [hxU.2]
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

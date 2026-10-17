import Paper17.EuclideanSupport

/-! Equation (2.2) for the exact inner-product norm, including arbitrary
finite compact nonempty summands and a compact convex target. -/
noncomputable section
open scoped Topology Pointwise BigOperators
namespace Paper17.EuclideanSupport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem dist_sum_smul_le {ι : Type*} (s : Finset ι) (w : ι → ℝ) (x y : ι → E)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    dist (∑ i ∈ s, w i • x i) (∑ i ∈ s, w i • y i) ≤
      ∑ i ∈ s, w i * dist (x i) (y i) := by
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  calc ‖∑ i ∈ s, (w i • x i - w i • y i)‖ ≤
        ∑ i ∈ s, ‖w i • x i - w i • y i‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, w i * dist (x i) (y i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i hi), dist_eq_norm]

/-- The full finite Minkowski convex-combination bound with the exact
Euclidean Hausdorff distance. -/
theorem hausdorffDist_minkowskiComb_le_max {K : Set E}
    (hK : IsCompact K) (hneK : K.Nonempty) (hconvK : Convex ℝ K)
    (ι : Type*) (s : Finset ι) (w : ι → ℝ) (P : ι → Set E)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hP : ∀ i ∈ s, IsCompact (P i) ∧ (P i).Nonempty)
    {δ : ℝ} (hδ : ∀ i ∈ s, Metric.hausdorffDist (P i) K ≤ δ) :
    Metric.hausdorffDist ((∑ i ∈ s, (w i) • (P i : Set E) : Set E)) K ≤ δ := by
  classical
  have hsne : s.Nonempty := by
    by_contra h
    simp [Finset.not_nonempty_iff_eq_empty.1 h] at hsum
  have hδ0 : 0 ≤ δ := by
    obtain ⟨i0, hi0⟩ := hsne
    exact le_trans Metric.hausdorffDist_nonneg (hδ i0 hi0)
  refine Metric.hausdorffDist_le_of_mem_dist hδ0 ?_ ?_
  · -- Every point of S = ∑ wᵢ • Pᵢ is within δ of some point of K.
    intro x hx
    have hx' : x ∈ ∑ i ∈ s, (w i) • (P i : Set E) := hx
    rw [Set.mem_finset_sum] at hx'
    obtain ⟨g, hg, hgsum⟩ := hx'
    have hex : ∀ i : ι, ∃ p, (i ∈ s → p ∈ P i) ∧ (i ∈ s → g i = w i • p) := by
      intro i
      by_cases hi : i ∈ s
      · obtain ⟨p, hp, hgip⟩ := Set.mem_smul_set.1 (hg (i := i) hi)
        exact ⟨p, fun _ => hp, fun _ => hgip.symm⟩
      · exact ⟨0, fun h => absurd h hi, fun h => absurd h hi⟩
    choose p hp hgp using hex
    have hnear : ∀ i : ι, ∃ y, (i ∈ s → y ∈ K) ∧ (i ∈ s → dist (p i) y ≤ δ) := by
      intro i
      by_cases hi : i ∈ s
      · obtain ⟨y, hy, hyd⟩ := hK.exists_infDist_eq_dist hneK (p i)
        refine ⟨y, fun _ => hy, fun _ => ?_⟩
        rw [← hyd]
        have hfin : EMetric.hausdorffEdist (P i) K ≠ ⊤ :=
          Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded (hP i hi).2 hneK
            (hP i hi).1.isBounded hK.isBounded
        exact le_trans (Metric.infDist_le_hausdorffDist_of_mem (hp i hi) hfin) (hδ i hi)
      · exact ⟨0, fun h => absurd h hi, fun h => absurd h hi⟩
    choose y hy hdy using hnear
    refine ⟨∑ i ∈ s, w i • y i, hconvK.sum_mem hw hsum (fun i hi => hy i hi), ?_⟩
    have hrew : x = ∑ i ∈ s, w i • p i := by
      rw [← hgsum]
      exact Finset.sum_congr rfl fun i hi => hgp i hi
    rw [hrew]
    refine le_trans (dist_sum_smul_le s w p y (fun i hi => hw i hi)) ?_
    refine le_trans (Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (hdy i hi) (hw i hi)) ?_
    rw [← Finset.sum_mul, hsum, one_mul]
  · -- Every point of K is within δ of some point of S.
    intro y hy
    have hy' : y = ∑ i ∈ s, w i • y := by
      rw [← Finset.sum_smul, hsum, one_smul]
    have hnear : ∀ i : ι, ∃ x, (i ∈ s → x ∈ P i) ∧ (i ∈ s → dist y x ≤ δ) := by
      intro i
      by_cases hi : i ∈ s
      · obtain ⟨x, hx, hxd⟩ := (hP i hi).1.exists_infDist_eq_dist (hP i hi).2 y
        refine ⟨x, fun _ => hx, fun _ => ?_⟩
        rw [← hxd]
        have hfin : EMetric.hausdorffEdist K (P i) ≠ ⊤ :=
          Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded hneK (hP i hi).2
            hK.isBounded (hP i hi).1.isBounded
        calc Metric.infDist y (P i) ≤ Metric.hausdorffDist K (P i) :=
               Metric.infDist_le_hausdorffDist_of_mem hy hfin
             _ = Metric.hausdorffDist (P i) K := Metric.hausdorffDist_comm
             _ ≤ δ := hδ i hi
      · exact ⟨0, fun h => absurd h hi, fun h => absurd h hi⟩
    choose x hx hdx using hnear
    refine ⟨∑ i ∈ s, w i • x i, ?_, ?_⟩
    · rw [Set.mem_finset_sum]
      refine ⟨fun i => w i • x i, ?_, rfl⟩
      intro i hi
      exact Set.smul_mem_smul_set (hx i hi)
    · rw [hy']
      refine le_trans (dist_sum_smul_le s w (fun _ => y) x (fun i hi => hw i hi)) ?_
      refine le_trans (Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (hdx i hi) (hw i hi)) ?_
      rw [← Finset.sum_mul, hsum, one_mul]


theorem hausdorffDist_minkowskiComb_le_sum {K : Set E}
    (hK : IsCompact K) (hneK : K.Nonempty) (hconvK : Convex ℝ K)
    (ι : Type*) (s : Finset ι) (w : ι → ℝ) (P : ι → Set E)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hP : ∀ i ∈ s, IsCompact (P i) ∧ (P i).Nonempty)
    : Metric.hausdorffDist ((∑ i ∈ s, (w i) • (P i : Set E) : Set E)) K ≤
        ∑ i ∈ s, w i * Metric.hausdorffDist (P i) K := by
  classical
  have hδ0 : 0 ≤ ∑ i ∈ s, w i * Metric.hausdorffDist (P i) K :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) Metric.hausdorffDist_nonneg
  refine Metric.hausdorffDist_le_of_mem_dist hδ0 ?_ ?_
  · -- Every point of S = ∑ wᵢ • Pᵢ is within δ of some point of K.
    intro x hx
    have hx' : x ∈ ∑ i ∈ s, (w i) • (P i : Set E) := hx
    rw [Set.mem_finset_sum] at hx'
    obtain ⟨g, hg, hgsum⟩ := hx'
    have hex : ∀ i : ι, ∃ p, (i ∈ s → p ∈ P i) ∧ (i ∈ s → g i = w i • p) := by
      intro i
      by_cases hi : i ∈ s
      · obtain ⟨p, hp, hgip⟩ := Set.mem_smul_set.1 (hg (i := i) hi)
        exact ⟨p, fun _ => hp, fun _ => hgip.symm⟩
      · exact ⟨0, fun h => absurd h hi, fun h => absurd h hi⟩
    choose p hp hgp using hex
    have hnear : ∀ i : ι, ∃ y, (i ∈ s → y ∈ K) ∧ (i ∈ s → dist (p i) y ≤ Metric.hausdorffDist (P i) K) := by
      intro i
      by_cases hi : i ∈ s
      · obtain ⟨y, hy, hyd⟩ := hK.exists_infDist_eq_dist hneK (p i)
        refine ⟨y, fun _ => hy, fun _ => ?_⟩
        rw [← hyd]
        have hfin : EMetric.hausdorffEdist (P i) K ≠ ⊤ :=
          Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded (hP i hi).2 hneK
            (hP i hi).1.isBounded hK.isBounded
        exact Metric.infDist_le_hausdorffDist_of_mem (hp i hi) hfin
      · exact ⟨0, fun h => absurd h hi, fun h => absurd h hi⟩
    choose y hy hdy using hnear
    refine ⟨∑ i ∈ s, w i • y i, hconvK.sum_mem hw hsum (fun i hi => hy i hi), ?_⟩
    have hrew : x = ∑ i ∈ s, w i • p i := by
      rw [← hgsum]
      exact Finset.sum_congr rfl fun i hi => hgp i hi
    rw [hrew]
    refine le_trans (dist_sum_smul_le s w p y (fun i hi => hw i hi)) ?_
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (hdy i hi) (hw i hi)
  · -- Every point of K is within δ of some point of S.
    intro y hy
    have hy' : y = ∑ i ∈ s, w i • y := by
      rw [← Finset.sum_smul, hsum, one_smul]
    have hnear : ∀ i : ι, ∃ x, (i ∈ s → x ∈ P i) ∧ (i ∈ s → dist y x ≤ Metric.hausdorffDist (P i) K) := by
      intro i
      by_cases hi : i ∈ s
      · obtain ⟨x, hx, hxd⟩ := (hP i hi).1.exists_infDist_eq_dist (hP i hi).2 y
        refine ⟨x, fun _ => hx, fun _ => ?_⟩
        rw [← hxd]
        have hfin : EMetric.hausdorffEdist K (P i) ≠ ⊤ :=
          Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded hneK (hP i hi).2
            hK.isBounded (hP i hi).1.isBounded
        calc Metric.infDist y (P i) ≤ Metric.hausdorffDist K (P i) :=
               Metric.infDist_le_hausdorffDist_of_mem hy hfin
             _ = Metric.hausdorffDist (P i) K := Metric.hausdorffDist_comm
      · exact ⟨0, fun h => absurd h hi, fun h => absurd h hi⟩
    choose x hx hdx using hnear
    refine ⟨∑ i ∈ s, w i • x i, ?_, ?_⟩
    · rw [Set.mem_finset_sum]
      refine ⟨fun i => w i • x i, ?_, rfl⟩
      intro i hi
      exact Set.smul_mem_smul_set (hx i hi)
    · rw [hy']
      refine le_trans (dist_sum_smul_le s w (fun _ => y) x (fun i hi => hw i hi)) ?_
      exact Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (hdx i hi) (hw i hi)


/-- Both inequalities of source (2.2), with a genuine maximizing summand. -/
theorem equation_2_2_full {K : Set E}
    (hK : IsCompact K) (hneK : K.Nonempty) (hconvK : Convex ℝ K)
    (ι : Type*) (s : Finset ι) (w : ι → ℝ) (P : ι → Set E)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hP : ∀ i ∈ s, IsCompact (P i) ∧ (P i).Nonempty) :
    ∃ j ∈ s, (∀ i ∈ s, Metric.hausdorffDist (P i) K ≤ Metric.hausdorffDist (P j) K) ∧
      Metric.hausdorffDist ((∑ i ∈ s, w i • (P i : Set E) : Set E)) K ≤
        ∑ i ∈ s, w i * Metric.hausdorffDist (P i) K ∧
      (∑ i ∈ s, w i * Metric.hausdorffDist (P i) K) ≤ Metric.hausdorffDist (P j) K := by
  classical
  have hsne : s.Nonempty := by
    by_contra h
    simp [Finset.not_nonempty_iff_eq_empty.1 h] at hsum
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun i => Metric.hausdorffDist (P i) K) hsne
  refine ⟨j, hj, hmax, hausdorffDist_minkowskiComb_le_sum hK hneK hconvK ι s w P hw hsum hP, ?_⟩
  calc (∑ i ∈ s, w i * Metric.hausdorffDist (P i) K) ≤
        ∑ i ∈ s, w i * Metric.hausdorffDist (P j) K :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hmax i hi) (hw i hi)
    _ = Metric.hausdorffDist (P j) K := by rw [← Finset.sum_mul, hsum, one_mul]


end Paper17.EuclideanSupport

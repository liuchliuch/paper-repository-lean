import Verification.Bridge

/-!
# Finite normal-fan control for finite Minkowski interpolation

These are the canonical fans of actual carriers, including normal cones at
all carrier points. Positive rescaling leaves them unchanged. The fan of a
Minkowski sum is the family of intersections, so a nonnegative finite sum's
fan depends only on which coefficients are positive.
-/
noncomputable section
open scoped BigOperators Pointwise Topology
namespace P17Contract

/-- Normal cones of actual Minkowski sums are intersections. -/
theorem normalCone_add_sets {n : ℕ} {K L : Set (V n)}
    {x y : V n} (hx : x ∈ K) (hy : y ∈ L) :
    normalCone (K + L) (x + y) = normalCone K x ∩ normalCone L y := by
  ext u
  constructor
  · intro hu
    constructor
    · intro z hz
      have hh := hu (z + y) (Set.add_mem_add hz hy)
      change Paper17.dot u (z + y) ≤ Paper17.dot u (x + y) at hh
      rw [Paper17.dot_add_right, Paper17.dot_add_right] at hh
      change Paper17.dot u z ≤ Paper17.dot u x
      linarith
    · intro z hz
      have hh := hu (x + z) (Set.add_mem_add hx hz)
      change Paper17.dot u (x + z) ≤ Paper17.dot u (x + y) at hh
      rw [Paper17.dot_add_right, Paper17.dot_add_right] at hh
      change Paper17.dot u z ≤ Paper17.dot u y
      linarith
  · rintro ⟨huK, huL⟩ z ⟨v, hv, w, hw, rfl⟩
    change Paper17.dot u (v + w) ≤ Paper17.dot u (x + y)
    rw [Paper17.dot_add_right, Paper17.dot_add_right]
    exact add_le_add (huK v hv) (huL w hw)

/-- Exact canonical fan formula, independent of vertex presentations. -/
theorem normalFan_add_sets {n : ℕ} (K L : Set (V n)) :
    normalFan (K + L) = (fun p : Set (V n) × Set (V n) => p.1 ∩ p.2) ''
      (normalFan K ×ˢ normalFan L) := by
  ext C
  constructor
  · rintro ⟨z, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨(normalCone K x, normalCone L y), ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩,
      (normalCone_add_sets hx hy).symm⟩
  · rintro ⟨⟨C, D⟩, ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩, rfl⟩
    exact ⟨x + y, Set.add_mem_add hx hy, normalCone_add_sets hx hy⟩

/-- Positive rescaling preserves every geometric normal cone. -/
theorem normalCone_smul_sets {n : ℕ} (K : Set (V n)) (x : V n)
    {t : ℝ} (ht : 0 < t) :
    normalCone (t • K) (t • x) = normalCone K x := by
  ext u
  constructor
  · intro hu y hy
    have hh := hu (t • y) (Set.smul_mem_smul_set hy)
    change Paper17.dot u (t • y) ≤ Paper17.dot u (t • x) at hh
    rw [Paper17.dot_smul_right, Paper17.dot_smul_right] at hh
    exact (mul_le_mul_iff_of_pos_left ht).mp hh
  · intro hu y hy
    obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.mp hy
    change Paper17.dot u (t • z) ≤ Paper17.dot u (t • x)
    rw [Paper17.dot_smul_right, Paper17.dot_smul_right]
    exact mul_le_mul_of_nonneg_left (hu z hz) ht.le

theorem normalFan_smul_sets {n : ℕ} (K : Set (V n)) {t : ℝ} (ht : 0 < t) :
    normalFan (t • K) = normalFan K := by
  ext C
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (normalCone_smul_sets K x ht).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨t • x, Set.smul_mem_smul_set hx, normalCone_smul_sets K x ht⟩

/-- The canonical fan of a finite nonnegative Minkowski sum depends only on
its positive support, without any refinement-chain hypothesis. -/
theorem normalFan_weighted_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (K : ι → Set (V n)) (hK : ∀ i ∈ s, (K i).Nonempty)
    (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    normalFan (∑ i ∈ s, w i • K i) =
      normalFan (∑ i ∈ s.filter (fun i => 0 < w i), K i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hsK := fun j hj => hK j (Finset.mem_insert_of_mem hj)
    have hsw := fun j hj => hw j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi]
    by_cases hwi : 0 < w i
    · rw [Finset.filter_insert, if_pos hwi,
        Finset.sum_insert (fun hh => hi (Finset.mem_filter.mp hh).1),
        normalFan_add_sets, normalFan_add_sets, normalFan_smul_sets _ hwi, ih hsK hsw]
    · have hz : w i = 0 := le_antisymm (le_of_not_gt hwi) (hw i (Finset.mem_insert_self _ _))
      rw [hz, Set.zero_smul_set (hK i (Finset.mem_insert_self _ _)), zero_add,
        Finset.filter_insert, if_neg (by simpa [hz]), ih hsK hsw]

/-- Equality of support functions on the dual unit ball determines any two
nonempty compact convex carriers, including lower-dimensional carriers. -/
theorem carrier_eq_of_support_on_dualBall {n : ℕ} {K L : Set (V n)}
    (hK : IsCompact K) (hneK : K.Nonempty) (hcK : Convex ℝ K)
    (hL : IsCompact L) (hneL : L.Nonempty) (hcL : Convex ℝ L)
    (h : ∀ u : Paper17.dualUnitBall n,
      Paper17.supportFunction K u.val = Paper17.supportFunction L u.val) : K = L := by
  have heq : ∀ u : V n, Paper17.supportFunction K u = Paper17.supportFunction L u := by
    intro u
    let S : ℝ := ∑ i, |u i|
    have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg _
    by_cases hz : S = 0
    · have hu : u = 0 := by
        ext i
        have hi : |u i| ≤ S := Finset.single_le_sum
          (fun j _ => abs_nonneg (u j)) (Finset.mem_univ i)
        exact abs_nonpos_iff.mp (hz ▸ hi)
      subst u
      simp [Paper17.supportFunction, Paper17.dot, hneK, hneL]
    · let v : Paper17.dualUnitBall n := ⟨S⁻¹ • u, by
        change ∑ i, |S⁻¹ * u i| ≤ 1
        simp_rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hS)]
        rw [← Finset.mul_sum]
        change S⁻¹ * S ≤ 1
        rw [inv_mul_cancel₀ hz]⟩
      have hh := h v
      change Paper17.supportFunction K (S⁻¹ • u) =
        Paper17.supportFunction L (S⁻¹ • u) at hh
      rw [Paper17.supportFunction_direction_smul hK hneK u (inv_nonneg.mpr hS),
        Paper17.supportFunction_direction_smul hL hneL u (inv_nonneg.mpr hS)] at hh
      exact mul_left_cancel₀ (inv_ne_zero hz) hh
  apply Set.Subset.antisymm
  · apply Paper17.subset_of_forall_dot_le_supportFunction hL hneL hcL
    intro u x hx
    rw [← heq u]
    exact Paper17.supportFunction_ub hK hx
  · apply Paper17.subset_of_forall_dot_le_supportFunction hK hneK hcK
    intro u x hx
    rw [heq u]
    exact Paper17.supportFunction_ub hL hx

/-- Only finitely many canonical normal fans arise from actual Delzant carriers
whose support functions lie in the convex hull of a fixed finite set of
Delzant support functions. -/
theorem finite_normalFans_convexHull {n : ℕ} (s : Finset (Paper17.SupportSpace n))
    (hs : (↑s : Set (Paper17.SupportSpace n)) ⊆ Paper17.delzantSet n) :
    {C | ∃ P : DelzantSpace n, toSupport P ∈ convexHull ℝ (↑s : Set (Paper17.SupportSpace n)) ∧
      normalFan P.carrier = C}.Finite := by
  classical
  have hex : ∀ y : ↑s, ∃ P : Paper17.DelzantPolytope n, Paper17.delzantSupport P = y.val :=
    fun y => hs y.property
  choose P hP using hex
  let K : Paper17.SupportSpace n → Set (V n) := fun y =>
    if hy : y ∈ s then (P ⟨y, hy⟩).carrier else {0}
  have hK : ∀ y ∈ s, IsCompact (K y) ∧ (K y).Nonempty ∧ Convex ℝ (K y) := by
    intro y hy
    dsimp [K]
    rw [dif_pos hy]
    exact ⟨(P ⟨y, hy⟩).val.isCompact, (P ⟨y, hy⟩).val.nonempty, (P ⟨y, hy⟩).val.convex⟩
  let candidates := s.powerset.image (fun I => normalFan (∑ y ∈ I, K y))
  apply candidates.finite_toSet.subset
  rintro C ⟨R, hR, rfl⟩
  obtain ⟨w, hw, hsum, hcomb⟩ := Finset.mem_convexHull.mp hR
  have hlinear : ∑ y ∈ s, w y • y = toSupport R := by
    simpa only [Finset.centerMass, hsum, inv_one, one_smul, id_eq] using hcomb
  have hsumK := Paper17.compact_nonempty_finset_sum s (fun y => w y • K y)
    (fun y hy => ⟨(hK y hy).1.smul _, (hK y hy).2.1.smul_set⟩)
  have hcar : R.carrier = ∑ y ∈ s, w y • K y := by
    apply carrier_eq_of_support_on_dualBall R.val.isCompact R.val.nonempty R.val.convex
      hsumK.1 hsumK.2 (convex_sum _ fun y hy => (hK y hy).2.2.smul _)
    intro u
    rw [Paper17.supportFunction_finset_sum s (fun y => w y • K y)
      (fun y hy => ⟨(hK y hy).1.smul _, (hK y hy).2.1.smul_set⟩)]
    have hh := congrArg (fun f : Paper17.SupportSpace n => f u) hlinear
    have hRvalue : toSupport R u = Paper17.supportFunction R.carrier u.val := by
      change Paper17.supportFunction (toProduction R).carrier u.val = _
      rw [toProduction_carrier]
    dsimp only at hh
    rw [hRvalue] at hh
    change Paper17.supportFunction R.carrier u.val = _
    rw [← hh]
    simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Paper17.supportFunction_smul (hK y hy).1 (hK y hy).2.1 (hw y hy)]
    congr 1
    have hyvalue := congrArg (fun f : Paper17.SupportSpace n => f u) (hP ⟨y, hy⟩)
    simpa only [K, dif_pos hy, Paper17.delzantSupport, Paper17.supportMap] using hyvalue.symm
  rw [hcar, normalFan_weighted_sum s K (fun y hy => (hK y hy).2.1) w hw]
  exact Finset.mem_image.mpr ⟨s.filter (fun y => 0 < w y),
    Finset.mem_powerset.mpr (Finset.filter_subset _ _), rfl⟩

/-- The main extension construction, including the original locally finite
canonical-normal-fan conclusion on the complement of the prescribed set. -/
theorem carrier_extension_controlled (n : ℕ)
    (X : Type) [MetricSpace X] (A : Set X) (hA : IsClosed A)
    (f : A → DelzantSpace n) (hf : Continuous f) :
    ∃ F : X → DelzantSpace n, Continuous F ∧
      (∀ a : A, F a = f a) ∧ LocallyFiniteFansOn F Aᶜ := by
  let e : DelzantSpace n ≃ₜ Set.range (@toSupport n) := isometry_toSupport.isEmbedding.toHomeomorph
  obtain ⟨F, hFc, hFY, hFeq, hcontrol⟩ :=
    Paper17.extension_by_barycentric_cover_controlled (Paper17.delzantSet_nonempty n)
      (Paper17.delzant_extensionHypotheses n) X A hA
      (toSupport ∘ f) (isometry_toSupport.continuous.comp hf)
      (fun a => ⟨toProduction (f a), rfl⟩)
  have hFrange : ∀ x, F x ∈ Set.range (@toSupport n) := by
    intro x
    obtain ⟨P, hP⟩ := hFY x
    exact ⟨ofProduction P, (toSupport_ofProduction P).trans hP⟩
  let F' : X → DelzantSpace n := fun x => e.symm ⟨F x, hFrange x⟩
  have hsupport : ∀ x, toSupport (F' x) = F x := by
    intro x
    exact (isometry_toSupport.isEmbedding.toHomeomorph_apply_coe (F' x)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply ⟨F x, hFrange x⟩))
  refine ⟨F', e.symm.continuous.comp (hFc.subtype_mk _), ?_, ?_⟩
  · intro a
    apply isometry_toSupport.injective
    rw [hsupport, hFeq]
    rfl
  · intro x hx
    obtain ⟨U, hU, s, hsY, hs⟩ := hcontrol x hx
    refine ⟨U, hU, (finite_normalFans_convexHull s hsY).subset ?_⟩
    rintro C ⟨y, hy, rfl⟩
    refine ⟨F' y, ?_, rfl⟩
    rw [hsupport]
    exact hs y hy

/-- Locally finite ranges of arbitrary tags have finite range on compact
subsets. No continuity of the tag function is needed. -/
theorem finite_image_of_locally_finite_range {X T : Type*} [TopologicalSpace X]
    (tag : X → T) {C D : Set X} (hC : IsCompact C) (hCD : C ⊆ D)
    (hlocal : ∀ x ∈ D, ∃ U ∈ 𝓝 x, (tag '' U).Finite) : (tag '' C).Finite := by
  apply hC.induction_on (p := fun S => (tag '' S).Finite)
  · simp
  · intro S T hST hT
    exact hT.subset (Set.image_mono hST)
  · intro S T hS hT
    rw [Set.image_union]
    exact hS.union hT
  · intro x hx
    obtain ⟨U, hU, hfin⟩ := hlocal x (hCD hx)
    exact ⟨U, nhdsWithin_le_nhds hU, hfin⟩

/-- Sphere filling, retaining finite canonical-fan range on each compact set
in the open ball. -/
theorem carrier_sphere_filling_controlled (n k : ℕ)
    (f : sphere k → DelzantSpace n) (hf : Continuous f) :
    ∃ F : ball k → DelzantSpace n, Continuous F ∧
      (∀ x : sphere k, F ⟨x.val, x.property.le⟩ = f x) ∧
      (∀ C : Set (ball k), IsCompact C →
        (∀ x ∈ C, ∑ i, x.val i ^ 2 < 1) →
        (normalFan ∘ DelzantPolytope.carrier ∘ F '' C).Finite) := by
  have hA : IsClosed (sphere k) := Paper17.isClosed_sphere k
  obtain ⟨G, hGc, hGeq, hGfans⟩ := carrier_extension_controlled n (V (k + 1))
    (sphere k) hA f hf
  let F : ball k → DelzantSpace n := fun x => G x.val
  refine ⟨F, hGc.comp continuous_subtype_val, ?_, ?_⟩
  · intro x
    exact hGeq x
  · intro C hC hinside
    have hsub : Subtype.val '' C ⊆ (sphere k)ᶜ := by
      rintro x ⟨y, hy, rfl⟩
      exact ne_of_lt (hinside y hy)
    have hfin := finite_image_of_locally_finite_range
      (normalFan ∘ DelzantPolytope.carrier ∘ G)
      (hC.image continuous_subtype_val) hsub hGfans
    simpa only [Set.image_image, Function.comp_def, F] using hfin

end P17Contract

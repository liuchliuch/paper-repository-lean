import Paper17.SupportCombination
import Paper17.CloseRefinement
import Paper17.Dugundji
import Paper17.Spheres

/-!
# The Delzant locus in support-function coordinates

The ambient space is the actual normed space `SupportSpace n`. Minkowski
addition of bodies is represented by addition of support functions. In
particular there is no additive-group or real-module instance on sets.
The pending geometric and nerve-construction proofs remain visible to the
whole-project axiom audit.
-/
noncomputable section
open scoped Topology BigOperators Pointwise
namespace Paper17

/-- A Delzant polytope as a point of the support-function space. -/
def delzantSupport {n : ℕ} (P : DelzantPolytope n) : SupportSpace n :=
  supportMap (P.val.toPosBody P.property.1)

/-- The actual Delzant locus in the normed ambient space. -/
def delzantSet (n : ℕ) : Set (SupportSpace n) := Set.range (@delzantSupport n)

theorem delzantSet_nonempty (n : ℕ) : (delzantSet n).Nonempty := by
  obtain ⟨P, _⟩ := DelzantPolytope.lemma_2_2 (n := n) (m := 0) Fin.elim0
  exact ⟨delzantSupport P, P, rfl⟩

theorem dist_delzantSupport {n : ℕ} (P Q : DelzantPolytope n) :
    dist (delzantSupport P) (delzantSupport Q) =
      Metric.hausdorffDist P.carrier Q.carrier :=
  dist_supportMap _ _

/-- Equality of support functions gives equality of the geometric carriers. -/
theorem carrier_eq_of_delzantSupport_eq {n : ℕ} {P Q : DelzantPolytope n}
    (h : delzantSupport P = delzantSupport Q) : P.carrier = Q.carrier := by
  have hh := supportMap_injective h
  exact congrArg PosBody.carrier hh

/-- Refinement order on support functions, witnessed by actual Delzant bodies. -/
def refinementLE {n : ℕ} (f g : SupportSpace n) : Prop :=
  ∃ P Q : DelzantPolytope n, delzantSupport P = f ∧ delzantSupport Q = g ∧
    DelzantPolytope.le P Q

theorem refinementLE_refl {n : ℕ} {f : SupportSpace n} (hf : f ∈ delzantSet n) :
    refinementLE f f := by
  obtain ⟨P, rfl⟩ := hf
  exact ⟨P, P, rfl, rfl, DelzantPolytope.le_refl P⟩

theorem refinementLE_trans {n : ℕ} {f g h : SupportSpace n}
    (hfg : refinementLE f g) (hgh : refinementLE g h) : refinementLE f h := by
  obtain ⟨P, Q, hp, hq, hpq⟩ := hfg
  obtain ⟨Q', R, hq', hr, hqr⟩ := hgh
  have heq := normalFan_equiv_of_carrier_eq
    (carrier_eq_of_delzantSupport_eq (hq'.trans hq.symm))
  exact ⟨P, R, hp, hr, Fan.refines_trans (Fan.refines_trans hqr heq.1) hpq⟩

/-- The geometric chain lemma, with the actual convex combination in its conclusion. -/
theorem convexComb_mem_delzantSet {n k : ℕ} {ys : Fin (k + 1) → SupportSpace n}
    (hys : ∀ i, ys i ∈ delzantSet n)
    (hchain : ∀ i j : Fin (k + 1), (i : ℕ) ≤ j → refinementLE (ys i) (ys j))
    (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    (∑ i, w i • ys i) ∈ delzantSet n := by
  classical
  choose Ps hPs using hys
  have hPchain : ∀ i j : Fin (k + 1), i.val ≤ j.val →
      DelzantPolytope.le (Ps i) (Ps j) := by
    intro i j hij
    obtain ⟨A, B, hA, hB, hAB⟩ := hchain i j hij
    have heqA := normalFan_equiv_of_carrier_eq
      (carrier_eq_of_delzantSupport_eq (hA.trans (hPs i).symm))
    have heqB := normalFan_equiv_of_carrier_eq
      (carrier_eq_of_delzantSupport_eq (hB.trans (hPs j).symm))
    exact Fan.refines_trans (Fan.refines_trans heqB.2 hAB) heqA.1
  obtain ⟨j, R, hj, hmax, hcar, hfan⟩ :=
    DelzantPolytope.lemma_2_1 Ps hPchain w hw hsum
  refine ⟨R, ?_⟩
  have heq := delzantSupport_eq_sum_of_carrier Ps R w hw hcar
  change delzantSupport R = ∑ i, w i • ys i
  rw [show delzantSupport R = ∑ i, w i • delzantSupport (Ps i) from heq]
  apply Finset.sum_congr rfl
  intro i _
  rw [hPs i]

/-- Finite convex-hull membership in an actual real normed vector space. -/
theorem mem_convexHull_iff_exists_comb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {ys : Fin (k + 1) → E} {x : E} :
    x ∈ convexHull ℝ (Set.range ys) ↔
      ∃ w : Fin (k + 1) → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
        x = ∑ i, w i • ys i := by
  classical
  constructor
  · intro hx
    rw [convexHull_range_eq_exists_affineCombination] at hx
    obtain ⟨s, w, hw, hsum, hx⟩ := hx
    let w' : Fin (k + 1) → ℝ := fun i => if i ∈ s then w i else 0
    have hsum' : ∑ i, w' i = 1 := by simpa [w'] using hsum
    refine ⟨w', fun i => by dsimp [w']; split_ifs with hi; exact hw i hi; exact le_rfl,
      hsum', ?_⟩
    rw [← hx, Finset.affineCombination_eq_linear_combination _ _ _ hsum]
    simp [w', Finset.sum_ite, Finset.filter_mem_eq_inter]
  · rintro ⟨w, hw, hsum, rfl⟩
    exact (convex_convexHull ℝ (Set.range ys)).sum_mem (fun i _ => hw i) hsum
      (fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩)

theorem delzant_upper_bounds (n : ℕ) :
    ∀ (m : ℕ) (ys : Fin m → SupportSpace n) (y : SupportSpace n) (η : ℝ),
      (∀ i, ys i ∈ delzantSet n) → y ∈ delzantSet n → 0 < η →
      ∃ z ∈ delzantSet n, (∀ i, refinementLE (ys i) z) ∧ dist z y < η := by
  intro m ys y η hys hy hη
  choose Ps hPs using hys
  obtain ⟨P, rfl⟩ := hy
  obtain ⟨Q, hdist, hQP, hQPs⟩ := DelzantPolytope.lemma_2_3 P Ps hη
  refine ⟨delzantSupport Q, ⟨Q, rfl⟩, ?_, ?_⟩
  · intro i
    exact ⟨Ps i, Q, hPs i, rfl, hQPs i⟩
  · rwa [dist_delzantSupport]

theorem delzant_extensionHypotheses (n : ℕ) :
    ExtensionHypotheses (delzantSet n) refinementLE where
  upper_bounds := delzant_upper_bounds n
  chain_convex := by
    intro k ys hys hchain x hx
    obtain ⟨w, hw, hsum, rfl⟩ := mem_convexHull_iff_exists_comb.mp hx
    exact convexComb_mem_delzantSet hys hchain w hw hsum
  refl := fun _ hy => refinementLE_refl hy
  trans := fun _ _ _ _ _ _ h₁ h₂ => refinementLE_trans h₁ h₂

/-- Theorem 1.2, extensor part in support-function coordinates. -/
theorem theorem_1_2 (n : ℕ) : IsAbsoluteExtensor (delzantSet n) :=
  theorem_3_1 (delzantSet_nonempty n) (delzant_extensionHypotheses n)

/-- Restriction of the chain criterion to an open convex subset of the ambient space. -/
theorem extensionHypotheses_inter_open {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Y W : Set E} {r : E → E → Prop} (h : ExtensionHypotheses Y r)
    (hW : IsOpen W) (hWc : Convex ℝ W) : ExtensionHypotheses (Y ∩ W) r where
  upper_bounds := by
    intro m ys y η hys hy hη
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hW y hy.2
    obtain ⟨z, hz, hupper, hdist⟩ := h.upper_bounds m ys y (min η δ)
      (fun i => (hys i).1) hy.1 (lt_min hη hδ)
    exact ⟨z, ⟨hz, hball (hdist.trans_le (min_le_right _ _))⟩, hupper,
      hdist.trans_le (min_le_left _ _)⟩
  chain_convex := by
    intro k ys hys hchain x hx
    exact ⟨h.chain_convex k ys (fun i => (hys i).1) hchain hx,
      convexHull_min (Set.range_subset_iff.mpr fun i => (hys i).2) hWc hx⟩
  refl := fun y hy => h.refl y hy.1
  trans := fun y z w hy hz hw => h.trans y z w hy.1 hz.1 hw.1

theorem theorem_1_2_open (n : ℕ) (W : Set (SupportSpace n))
    (hW : IsOpen W) (hWc : Convex ℝ W) (hne : (delzantSet n ∩ W).Nonempty) :
    IsAbsoluteExtensor (delzantSet n ∩ W) :=
  theorem_3_1 hne (extensionHypotheses_inter_open (delzant_extensionHypotheses n) hW hWc)

theorem delzant_absoluteRetract (n : ℕ) : IsAbsoluteRetract (delzantSet n) :=
  isAbsoluteRetract_of_isAbsoluteExtensor (theorem_1_2 n) (delzantSet_nonempty n)

/-- Corollary 1.3: a strong deformation retraction, with the correct domain subtype. -/
theorem corollary_1_3 (n : ℕ) (Pstar : SupportSpace n) (hP : Pstar ∈ delzantSet n) :
    ∃ H : ↥(delzantSet n) × ℝ → SupportSpace n,
      Continuous H ∧
      (∀ P : ↥(delzantSet n), H (P, 0) = P) ∧
      (∀ P, H (P, 1) = Pstar) ∧
      (∀ t, H (⟨Pstar, hP⟩, t) = Pstar) ∧
      (∀ P t, H (P, t) ∈ delzantSet n) :=
  sdr_of_absoluteExtensor (theorem_1_2 n) (delzantSet_nonempty n) Pstar hP

theorem delzant_pathConnected (n : ℕ) : IsPathConnected (delzantSet n) :=
  pathConnected_of_absoluteExtensor (theorem_1_2 n) (delzantSet_nonempty n)

theorem delzant_contractible (n : ℕ) : ContractibleSpace ↥(delzantSet n) :=
  contractible_of_absoluteExtensor (theorem_1_2 n) (delzantSet_nonempty n)

/-- Corollary 4.1: arbitrary continuous sphere data, not an already extended map. -/
theorem corollary_4_1 (n k : ℕ) (f : sphere k → SupportSpace n)
    (hf : Continuous f) (hmem : ∀ x, f x ∈ delzantSet n) :
    ∃ F : unitSphereBall k → SupportSpace n, Continuous F ∧
      (∀ x, F x ∈ delzantSet n) ∧
      (∀ x : sphere k, F ⟨x, sphere_subset_unitSphereBall k x.2⟩ = f x) :=
  fill_sphere_of_absoluteExtensor (theorem_1_2 n) k f hf hmem

end Paper17

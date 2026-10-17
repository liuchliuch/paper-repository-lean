import Paper17.StellarSupportGeometry

/-!
# Uniform positive size for a genuine face truncation

Finitely many strict slacks and continuous explicit vertex motions give one
actual positive cut size. It keeps the interior point, every unaffected old
vertex, and all formerly inactive inequalities at the new vertices strict.
-/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Paper17.IntegralConeComplex.FacetSupportData
variable {n : ℕ} {K : IntegralConeComplex n}

/-- A positive cut size with the concrete finite strict inequalities needed
for the explicit truncation vertices. Existence is proved below. -/
structure TruncationRadius (R : FacetSupportData K) (D : StellarData K) where
  value : ℝ
  positive : 0 < value
  interior : dot (fun j => (D.ray j : ℝ)) R.interiorPoint < R.faceHeight D - value
  unaffected : ∀ s : K.complex.facets, ¬ D.face ⊆ s.val →
    dot (fun j => (D.ray j : ℝ)) (R.vertex s) < R.faceHeight D - value
  inactive : ∀ (s : K.complex.facets) (k i : K.index),
    D.face ⊆ s.val → k ∈ D.face → i ∉ s.val →
      dot (realRays K.rays i) (R.truncationVertex D s k value) < R.heights i

theorem truncationRadius_nonempty (R : FacetSupportData K) (D : StellarData K) :
    Nonempty (TruncationRadius R D) := by
  classical
  have hinterior : ∀ᶠ ε : ℝ in 𝓝 0,
      dot (fun j => (D.ray j : ℝ)) R.interiorPoint < R.faceHeight D - ε := by
    have hz : dot (fun j => (D.ray j : ℝ)) R.interiorPoint < R.faceHeight D - (0 : ℝ) := by
      simpa only [sub_zero] using R.faceHeight_interior_lt D
    exact (isOpen_lt continuous_const (continuous_const.sub continuous_id)).mem_nhds hz
  have hunaffected : ∀ s : K.complex.facets, ∀ᶠ ε : ℝ in 𝓝 0,
      ¬ D.face ⊆ s.val → dot (fun j => (D.ray j : ℝ)) (R.vertex s) < R.faceHeight D - ε := by
    intro s
    by_cases hIs : D.face ⊆ s.val
    · exact Filter.Eventually.of_forall (fun _ hn => False.elim (hn hIs))
    · have hstrict : dot (fun j => (D.ray j : ℝ)) (R.vertex s) < R.faceHeight D :=
        lt_of_le_of_ne (R.faceHeight_bound D s) (fun heq => hIs ((R.faceHeight_eq_iff D s).mp heq))
      have hz : dot (fun j => (D.ray j : ℝ)) (R.vertex s) < R.faceHeight D - (0 : ℝ) := by
        simpa only [sub_zero] using hstrict
      have hevent : ∀ᶠ ε : ℝ in 𝓝 0,
          dot (fun j => (D.ray j : ℝ)) (R.vertex s) < R.faceHeight D - ε :=
        (isOpen_lt continuous_const (continuous_const.sub continuous_id)).mem_nhds hz
      exact hevent.mono (fun _ h _ => h)
  have hinactive : ∀ (s : K.complex.facets) (k i : K.index), ∀ᶠ ε : ℝ in 𝓝 0,
      D.face ⊆ s.val → k ∈ D.face → i ∉ s.val →
        dot (realRays K.rays i) (R.truncationVertex D s k ε) < R.heights i := by
    intro s k i
    by_cases hcond : D.face ⊆ s.val ∧ k ∈ D.face ∧ i ∉ s.val
    · have hstrict : dot (realRays K.rays i) (R.vertex s) < R.heights i :=
        lt_of_le_of_ne (R.feasible s i) (fun heq => hcond.2.2 ((R.active s i).mp heq))
      have hc : Continuous (fun ε : ℝ => dot (realRays K.rays i) (R.truncationVertex D s k ε)) :=
        (continuous_dot _).comp (R.continuous_truncationVertex D s k)
      have hz : dot (realRays K.rays i) (R.truncationVertex D s k 0) < R.heights i := by
        simpa only [truncationVertex_zero] using hstrict
      have hevent : ∀ᶠ ε : ℝ in 𝓝 0,
          dot (realRays K.rays i) (R.truncationVertex D s k ε) < R.heights i :=
        (isOpen_lt hc continuous_const).mem_nhds hz
      exact hevent.mono (fun _ h _ _ _ => h)
    · exact Filter.Eventually.of_forall (fun _ hIs hk hi => False.elim (hcond ⟨hIs, hk, hi⟩))
  have hunaffectedAll := Filter.eventually_all.mpr hunaffected
  have hinactiveAll := Filter.eventually_all.mpr (fun s =>
    Filter.eventually_all.mpr (fun k => Filter.eventually_all.mpr (hinactive s k)))
  have hgood := hunaffectedAll.and (hinactiveAll.and hinterior)
  obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff.mp hgood
  have hpos : 0 < δ / 2 := div_pos hδ (by norm_num)
  have hdist : dist (δ / 2) (0 : ℝ) < δ := by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hpos]
    linarith
  have hh := hbound hdist
  exact ⟨{
    value := δ / 2
    positive := hpos
    interior := hh.2.2
    unaffected := hh.1
    inactive := hh.2.1 }⟩

end Paper17.IntegralConeComplex.FacetSupportData

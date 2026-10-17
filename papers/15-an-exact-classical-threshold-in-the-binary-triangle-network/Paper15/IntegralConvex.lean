import Paper15.Barycentre
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Finite-dimensional barycentres without a closed-range assumption

Choose a subspace of least dimension containing the centered random variable
almost surely. In this subspace no proper linear hyperplane can have full
measure. A separating functional at a putative boundary mean would have
nonnegative values and zero integral, and hence would vanish almost surely.
This contradicts minimality. The resulting convex-integral theorem does not
require the convex set to be closed.
-/

noncomputable section
namespace Paper15
open Set MeasureTheory Module

/-- In a finite-dimensional real inner product space, the expectation belongs
to every convex set containing the random variable almost surely. The convex
set need not be closed. -/
theorem integral_mem_convex_finiteDimensional
    {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → E} {s : Set E}
    (hf : Integrable f μ) (hs : Convex ℝ s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) :
    (∫ x, f x ∂μ) ∈ s := by
  classical
  let m := ∫ x, f x ∂μ
  let f0 := fun x => f x - m
  have hf0 : Integrable f0 μ := hf.sub (integrable_const m)
  have hi0 : (∫ x, f0 x ∂μ) = 0 := by
    simp [f0, integral_sub hf (integrable_const m), m]
  have hex : ∃ n : ℕ, ∃ U : Submodule ℝ E,
      finrank ℝ U = n ∧ ∀ᵐ x ∂μ, f0 x ∈ U :=
    ⟨finrank ℝ E, ⊤, by simp, Filter.Eventually.of_forall (fun _ => Submodule.mem_top)⟩
  obtain ⟨U, hdim, hU⟩ := Nat.find_spec hex
  have hmin (V : Submodule ℝ E) (hV : ∀ᵐ x ∂μ, f0 x ∈ V) :
      finrank ℝ U ≤ finrank ℝ V := by
    rw [hdim]
    exact Nat.find_min' hex ⟨V, rfl, hV⟩
  let g : α → U := fun x => U.orthogonalProjection (f0 x)
  have hg : Integrable g μ := U.orthogonalProjection.integrable_comp hf0
  have hg0 : (∫ x, g x ∂μ) = 0 := by
    rw [show (∫ x, g x ∂μ) = U.orthogonalProjection (∫ x, f0 x ∂μ) from
      U.orthogonalProjection.integral_comp_comm hf0, hi0, map_zero]
  have hgeq : ∀ᵐ x ∂μ, (g x : E) = f0 x := by
    filter_upwards [hU] with x hx
    exact U.starProjection_eq_self_iff.mpr hx
  have hfull (V : Submodule ℝ U) (hV : ∀ᵐ x ∂μ, g x ∈ V) : V = ⊤ := by
    have hm := hmin (V.map U.subtype) (by
      filter_upwards [hV, hgeq] with x hx he
      exact ⟨g x, hx, he⟩)
    rw [Submodule.finrank_map_subtype_eq] at hm
    exact Submodule.eq_top_of_finrank_eq (le_antisymm V.finrank_le hm)
  let S : Set U := {u | (u : E) + m ∈ s}
  have hSc : Convex ℝ S := by
    intro u hu v hv a b ha hb hab
    change ((a • u + b • v : U) : E) + m ∈ s
    have he : ((a • u + b • v : U) : E) + m =
        a • ((u : E) + m) + b • ((v : E) + m) := by
      simp only [Submodule.coe_add, Submodule.coe_smul, smul_add]
      have hz : a • m + b • m = m := by rw [← add_smul, hab, one_smul]
      conv_lhs => rw [← hz]
      abel
    rw [he]
    exact hs hu hv ha hb hab
  have hgS : ∀ᵐ x ∂μ, g x ∈ S := by
    filter_upwards [hfs, hgeq] with x hx he
    change (g x : E) + m ∈ s
    rw [he]
    simpa [f0] using hx
  let A := affineSpan ℝ S
  have hA0 : (0 : U) ∈ A := by
    rw [← hg0]
    exact A.convex.integral_mem A.closed_of_finiteDimensional
      (hgS.mono (fun _ hx => subset_affineSpan ℝ S hx)) hg
  have hAdir : A.direction = ⊤ := by
    apply hfull
    filter_upwards [hgS] with x hx
    simpa using A.vsub_mem_direction (subset_affineSpan ℝ S hx) hA0
  have hAtop : A = ⊤ :=
    (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨0, hA0⟩).mp hAdir
  have hint : (interior S).Nonempty := hSc.interior_nonempty_iff_affineSpan_eq_top.mpr hAtop
  suffices (0 : U) ∈ S by simpa [S] using this
  by_contra hnot
  obtain ⟨l, hl⟩ := geometric_hahn_banach_point_open hSc.interior isOpen_interior
    (fun h => hnot (interior_subset h))
  have hlpos : ∀ u ∈ interior S, 0 < l u := by simpa using hl
  have hlne : l ≠ 0 := by
    intro he
    obtain ⟨u, hu⟩ := hint
    simpa [he] using hlpos u hu
  have hlnonneg : ∀ u ∈ S, 0 ≤ l u := by
    have hcl : closure (interior S) ⊆ {u | 0 ≤ l u} :=
      closure_minimal (fun u hu => (hlpos u hu).le)
        (isClosed_le continuous_const l.continuous)
    rw [hSc.closure_interior_eq_closure_of_nonempty_interior hint] at hcl
    intro u hu
    exact hcl (subset_closure hu)
  have hli : Integrable (fun x => l (g x)) μ := l.integrable_comp hg
  have hln : ∀ᵐ x ∂μ, 0 ≤ l (g x) := hgS.mono (fun _ hx => hlnonneg _ hx)
  have hlint : (∫ x, l (g x) ∂μ) = 0 := by
    rw [l.integral_comp_comm hg, hg0, map_zero]
  have hlzero : ∀ᵐ x ∂μ, l (g x) = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hln hli).mp hlint
  have hker : LinearMap.ker l.toLinearMap = ⊤ := hfull _ hlzero
  apply hlne
  ext u
  exact LinearMap.mem_ker.mp (hker ▸ Submodule.mem_top (x := u))

/-- The full measure-theoretic form of Lemma 3, including a prescribed
full-measure subset. Integrability is weaker than the paper's boundedness and
measurability assumptions on a probability space. -/
theorem lemma3_integrable_fullMeasure
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {d : ℕ} {f : α → EuclideanSpace ℝ (Fin d)} (hf : Integrable f μ)
    (t : Set α) (ht : ∀ᵐ x ∂μ, x ∈ t) :
    ∃ (n : ℕ) (_ : n ≤ d + 1) (pts : Fin n → α) (w : Fin n → ℝ),
      (∀ i, pts i ∈ t) ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      (∑ i, w i • f (pts i) = ∫ x, f x ∂μ) := by
  classical
  have hm : (∫ x, f x ∂μ) ∈ convexHull ℝ (f '' t) :=
    integral_mem_convex_finiteDimensional hf (convex_convexHull ℝ _) (ht.mono
      (fun x hx => subset_convexHull ℝ _ (mem_image_of_mem f hx)))
  obtain ⟨u, w, hw0, hw1, hwu, hcard, hcenter⟩ := finite_barycentre_caratheodory hm
  have hex : ∀ y : ↥u, ∃ x, x ∈ t ∧ f x = (y : EuclideanSpace ℝ (Fin d)) := by
    intro y
    obtain ⟨x, hx, he⟩ := hwu y
    exact ⟨x, hx, he⟩
  choose pts hpts hval using hex
  refine ⟨u.card, hcard, fun i => pts (u.equivFin.symm i),
    fun i => w (u.equivFin.symm i), fun i => hpts _, fun i => hw0 _, ?_, ?_⟩
  · exact (Equiv.sum_comp u.equivFin.symm w).trans hw1
  · simp_rw [hval]
    exact (Equiv.sum_comp u.equivFin.symm
      (fun y : ↥u => w y • (y : EuclideanSpace ℝ (Fin d)))).trans hcenter

/-- Lemma 3 with the paper's bounded measurable hypotheses. -/
theorem lemma3_bounded_measurable
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {d : ℕ} {f : α → EuclideanSpace ℝ (Fin d)}
    (hf : Measurable f) (hbounded : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (t : Set α) (ht : ∀ᵐ x ∂μ, x ∈ t) :
    ∃ (n : ℕ) (_ : n ≤ d + 1) (pts : Fin n → α) (w : Fin n → ℝ),
      (∀ i, pts i ∈ t) ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      (∑ i, w i • f (pts i) = ∫ x, f x ∂μ) := by
  obtain ⟨C, hC⟩ := hbounded
  exact lemma3_integrable_fullMeasure
    ⟨hf.aestronglyMeasurable, HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall hC)⟩ t ht

end Paper15

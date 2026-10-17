import Verification.EuclideanApplications
import Paper17.LabelledApproximation

/-! Quantitative source-metric chain interpolation over arbitrary open covers. -/
noncomputable section
open scoped Topology BigOperators
namespace P17Contract

/-- The radial restriction is globally Lipschitz, on all continuous functions,
with the explicit dimension bound used for label errors. -/
theorem sphericalRestriction_lipschitz (n : ℕ) :
    LipschitzWith (n : NNReal) (sphericalRestriction n) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [dist_eq_norm, ← map_sub, dist_eq_norm]
  apply (ContinuousMap.norm_le _ (mul_nonneg (Nat.cast_nonneg n) (norm_nonneg _))).mpr
  intro u
  change |directionL1 u * (f - g) (normalizeDirection u)| ≤ (n : ℝ) * ‖f - g‖
  rw [abs_mul, abs_of_pos (directionL1_pos u)]
  calc directionL1 u * |(f - g) (normalizeDirection u)| ≤ directionL1 u * ‖f - g‖ :=
      mul_le_mul_of_nonneg_left ((f - g).norm_coe_le_norm _) (directionL1_pos u).le
    _ ≤ (n : ℝ) * ‖f - g‖ :=
      mul_le_mul_of_nonneg_right (directionL1_le_dimension u) (norm_nonneg _)

@[simp] theorem sphericalRestriction_toSupport_euclidean {n : ℕ} (P : EuclideanDelzantSpace n) :
    sphericalRestriction n (toSupport ((euclideanDelzantHomeomorph n).symm P)) =
      bodySphericalSupport P.val.body := by
  ext u
  rw [sphericalRestriction_toSupport, bodySphericalSupport_apply]
  rfl

/-- Recover actual Euclidean Delzant carriers from a continuous support map,
retaining the finite-fan conclusion of its local finite convex labels. -/
theorem euclidean_delzant_map_of_support {X : Type} [MetricSpace X] {n : ℕ}
    (G : X → Paper17.SupportSpace n) (hGc : Continuous G)
    (hGY : ∀ x, G x ∈ Paper17.delzantSet n)
    (hlocal : Paper17.LocallyFiniteConvexLabels G Set.univ (Paper17.delzantSet n)) :
    ∃ F : X → EuclideanDelzantSpace n, Continuous F ∧
      (∀ x, bodySphericalSupport (F x).val.body = sphericalRestriction n (G x)) ∧
      (∀ x, ∃ U ∈ 𝓝 x, ((fun y => normalFan (F y).val.body.carrier) '' U).Finite) := by
  let e : DelzantSpace n ≃ₜ Set.range (@toSupport n) := isometry_toSupport.isEmbedding.toHomeomorph
  have hFrange : ∀ x, G x ∈ Set.range (@toSupport n) := by
    intro x
    obtain ⟨P, hP⟩ := hGY x
    exact ⟨ofProduction P, (toSupport_ofProduction P).trans hP⟩
  let F₀ : X → DelzantSpace n := fun x => e.symm ⟨G x, hFrange x⟩
  have hF₀ : Continuous F₀ := e.symm.continuous.comp (hGc.subtype_mk _)
  have hs : ∀ x, toSupport (F₀ x) = G x := by
    intro x
    exact (isometry_toSupport.isEmbedding.toHomeomorph_apply_coe (F₀ x)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply ⟨G x, hFrange x⟩))
  let F : X → EuclideanDelzantSpace n := fun x => euclideanDelzantHomeomorph n (F₀ x)
  refine ⟨F, (euclideanDelzantHomeomorph n).continuous.comp hF₀, ?_, ?_⟩
  · intro x
    calc
      bodySphericalSupport (F x).val.body = sphericalRestriction n (toSupport (F₀ x)) := by
        simpa only [F, Homeomorph.symm_apply_apply] using
          (sphericalRestriction_toSupport_euclidean (euclideanDelzantHomeomorph n (F₀ x))).symm
      _ = sphericalRestriction n (G x) := congrArg (sphericalRestriction n) (hs x)
  · intro x
    obtain ⟨U, hU, s, hsY, hlabel⟩ := hlocal x (Set.mem_univ _)
    refine ⟨U, hU, (finite_normalFans_convexHull s hsY).subset ?_⟩
    rintro C ⟨y, hy, rfl⟩
    refine ⟨F₀ y, ?_, ?_⟩
    · rw [hs]
      exact hlabel y hy
    · rfl

/-- Arbitrary cover labels can be interpolated continuously with exact
Euclidean error control and locally finite normal fans. The reference may be
discontinuous away from the controlled region. -/
theorem labelled_euclidean_delzant_approximation
    {X ι : Type} [MetricSpace X] {n : ℕ}
    (p : ι → EuclideanDelzantSpace n) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (U : ι → Set X) (hUopen : ∀ i, IsOpen (U i))
    (hUcover : (Set.univ : Set X) ⊆ ⋃ i, U i)
    (D : Set X) (R : X → EuclideanDelzantSpace n) (ε : X → ℝ)
    (hbudget : ∀ x ∈ D, ∀ i, x ∈ U i → (n : ℝ) * δ i + dist (p i) (R x) ≤ ε x) :
    ∃ F : X → EuclideanDelzantSpace n, Continuous F ∧
      (∀ x ∈ D, dist (F x) (R x) ≤ ε x) ∧
      (∀ x, ∃ V ∈ 𝓝 x, ((fun y => normalFan (F y).val.body.carrier) '' V).Finite) := by
  let p' : ι → ↥(Paper17.delzantSet n) := fun i =>
    ⟨toSupport ((euclideanDelzantHomeomorph n).symm (p i)),
      ⟨toProduction ((euclideanDelzantHomeomorph n).symm (p i)), rfl⟩⟩
  have hb : ∀ x ∈ D, ∀ i, x ∈ U i → (n : ℝ) * δ i +
      dist (sphericalRestriction n (p' i).val) (bodySphericalSupport (R x).val.body) ≤ ε x := by
    intro x hx i hi
    rw [show (p' i).val = toSupport ((euclideanDelzantHomeomorph n).symm (p i)) from rfl,
      sphericalRestriction_toSupport_euclidean]
    exact hbudget x hx i hi
  obtain ⟨G, hGc, hGY, herr, hlocal⟩ := Paper17.labelled_approximation_through_linear_map
    (Paper17.delzantSet_nonempty n) (Paper17.delzant_extensionHypotheses n) p' δ hδ U hUopen hUcover
    (sphericalRestriction n) (sphericalRestriction_lipschitz n) D
    (fun x => bodySphericalSupport (R x).val.body) ε hb
  obtain ⟨F, hFc, hs, hfin⟩ := euclidean_delzant_map_of_support G hGc hGY hlocal
  refine ⟨F, hFc, ?_, hfin⟩
  intro x hx
  change dist (bodySphericalSupport (F x).val.body) (bodySphericalSupport (R x).val.body) ≤ ε x
  rw [hs]
  exact herr x hx

end P17Contract

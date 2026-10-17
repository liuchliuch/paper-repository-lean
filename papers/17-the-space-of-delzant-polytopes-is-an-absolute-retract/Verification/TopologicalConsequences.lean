import Verification.Solution
import Paper17.HomotopyConsequences

/-! Source neighborhood consequences, retaining the actual finite-fan control. -/
noncomputable section
open scoped Topology BigOperators
namespace P17Contract

/-- The controlled extension also stays in any prescribed open convex subset
of the actual support-function space. -/
theorem carrier_extension_in_support_open_controlled {n : ℕ}
    (W : Set (Paper17.SupportSpace n)) (hW : IsOpen W) (hWc : Convex ℝ W)
    (hne : ∃ P : DelzantSpace n, toSupport P ∈ W)
    (X : Type) [MetricSpace X] (A : Set X) (hA : IsClosed A)
    (f : A → DelzantSpace n) (hf : Continuous f) (hfW : ∀ a, toSupport (f a) ∈ W) :
    ∃ F : X → DelzantSpace n, Continuous F ∧ (∀ a : A, F a = f a) ∧
      (∀ x, toSupport (F x) ∈ W) ∧ LocallyFiniteFansOn F Aᶜ := by
  obtain ⟨P, hP⟩ := hne
  have hY : (Paper17.delzantSet n ∩ W).Nonempty :=
    ⟨toSupport P, ⟨⟨toProduction P, rfl⟩, hP⟩⟩
  let e : DelzantSpace n ≃ₜ Set.range (@toSupport n) :=
    isometry_toSupport.isEmbedding.toHomeomorph
  obtain ⟨F, hFc, hFY, hFeq, hcontrol⟩ :=
    Paper17.extension_by_barycentric_cover_controlled hY
      (Paper17.extensionHypotheses_inter_open (Paper17.delzant_extensionHypotheses n) hW hWc)
      X A hA (toSupport ∘ f) (isometry_toSupport.continuous.comp hf)
      (fun a => ⟨⟨toProduction (f a), rfl⟩, hfW a⟩)
  have hFrange : ∀ x, F x ∈ Set.range (@toSupport n) := by
    intro x
    obtain ⟨Q, hQ⟩ := (hFY x).1
    exact ⟨ofProduction Q, (toSupport_ofProduction Q).trans hQ⟩
  let G : X → DelzantSpace n := fun x => e.symm ⟨F x, hFrange x⟩
  have hs : ∀ x, toSupport (G x) = F x := by
    intro x
    exact (isometry_toSupport.isEmbedding.toHomeomorph_apply_coe (G x)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply ⟨F x, hFrange x⟩))
  refine ⟨G, e.symm.continuous.comp (hFc.subtype_mk _), ?_, ?_, ?_⟩
  · intro a
    apply isometry_toSupport.injective
    rw [hs, hFeq]
    rfl
  · intro x
    rw [hs]
    exact (hFY x).2
  · intro x hx
    obtain ⟨U, hU, s, hsY, hlabel⟩ := hcontrol x hx
    refine ⟨U, hU, (finite_normalFans_convexHull s (fun y hy => (hsY hy).1)).subset ?_⟩
    rintro C ⟨y, hy, rfl⟩
    refine ⟨G y, ?_, rfl⟩
    rw [hs]
    exact hlabel y hy

/-- The source spherical-support open-convex restriction retains all the
locally finite normal-fan control of the main theorem. -/
theorem carrier_extension_in_spherical_open_controlled {n : ℕ}
    (W : Set (PaperSupportSpace n)) (hW : IsOpen W) (hWc : Convex ℝ W)
    (hne : ∃ P : DelzantSpace n, InSupportSet W P)
    (X : Type) [MetricSpace X] (A : Set X) (hA : IsClosed A)
    (f : A → DelzantSpace n) (hf : Continuous f) (hfW : ∀ a, InSupportSet W (f a)) :
    ∃ F : X → DelzantSpace n, Continuous F ∧ (∀ a : A, F a = f a) ∧
      (∀ x, InSupportSet W (F x)) ∧ LocallyFiniteFansOn F Aᶜ := by
  let U := (sphericalRestriction n) ⁻¹' W
  obtain ⟨P, hP⟩ := hne
  obtain ⟨F, hFc, hFeq, hFU, hfin⟩ := carrier_extension_in_support_open_controlled U
    (hW.preimage (continuous_sphericalRestriction n)) (hWc.linear_preimage _)
    ⟨P, (inSupportSet_iff W P).mp hP⟩ X A hA f hf
    (fun a => (inSupportSet_iff W (f a)).mp (hfW a))
  exact ⟨F, hFc, hFeq, fun x => (inSupportSet_iff W (F x)).mpr (hFU x), hfin⟩

/-- Every positive Hausdorff ball centered at a Delzant carrier admits
controlled extensions with values in that same ball. -/
theorem carrier_ball_extension_controlled {n : ℕ} (P : DelzantSpace n) {r : ℝ} (hr : 0 < r)
    (X : Type) [MetricSpace X] (A : Set X) (hA : IsClosed A)
    (f : A → DelzantSpace n) (hf : Continuous f) (hfr : ∀ a, dist (f a) P < r) :
    ∃ F : X → DelzantSpace n, Continuous F ∧ (∀ a : A, F a = f a) ∧
      (∀ x, dist (F x) P < r) ∧ LocallyFiniteFansOn F Aᶜ := by
  obtain ⟨F, hFc, hFeq, hFW, hfin⟩ := carrier_extension_in_support_open_controlled
    (Metric.ball (toSupport P) r) Metric.isOpen_ball (convex_ball _ _)
    ⟨P, by simpa using hr⟩ X A hA f hf
    (fun a => by simpa only [Metric.mem_ball, isometry_toSupport.dist_eq] using hfr a)
  exact ⟨F, hFc, hFeq,
    fun x => by simpa only [Metric.mem_ball, isometry_toSupport.dist_eq] using hFW x, hfin⟩

/-- The open Hausdorff balls are absolute extensors and absolute retracts. -/
theorem open_ball_absoluteExtensor_retract {n : ℕ} (P : DelzantSpace n)
    {r : ℝ} (hr : 0 < r) :
    IsAbsoluteExtensor (Metric.ball P r) ∧ IsAbsoluteRetract (Metric.ball P r) := by
  have hAE : IsAbsoluteExtensor (Metric.ball P r) := by
    intro X _ A hA f hf
    obtain ⟨F, hFc, hFeq, hFr, _⟩ := carrier_ball_extension_controlled P hr X A hA
      (fun a => (f a).val) (continuous_subtype_val.comp hf) (fun a => (f a).property)
    exact ⟨fun x => ⟨F x, hFr x⟩, hFc.subtype_mk _, fun a => Subtype.ext (hFeq a)⟩
  exact ⟨hAE, def_1_1 hAE ⟨⟨P, Metric.mem_ball_self hr⟩⟩⟩

/-- Local contractibility in the explicit neighborhood sense: an open
neighborhood contracts to the chosen point through the prescribed larger
neighborhood, fixing that point throughout. -/
theorem delzant_locally_contractible {n : ℕ} (P : DelzantSpace n)
    (U : Set (DelzantSpace n)) (hU : U ∈ 𝓝 P) :
    ∃ V : Set (DelzantSpace n), IsOpen V ∧ P ∈ V ∧ V ⊆ U ∧
      ∃ H : V × ℝ → DelzantSpace n, Continuous H ∧
        (∀ y : V, H (y, 0) = y.val) ∧ (∀ y : V, H (y, 1) = P) ∧
        (∀ y t, H (y, t) ∈ U) ∧ (∀ t, ∀ hp : P ∈ V, H (⟨P, hp⟩, t) = P) := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  have hAE := (open_ball_absoluteExtensor_retract P hr).1
  have hprod : Paper17.IsAbsoluteExtensor (Metric.ball P r) := by
    intro X _ A hA f hf hfV
    obtain ⟨F, hFc, hFeq⟩ := hAE X A hA (fun a => ⟨f a, hfV a⟩) (hf.subtype_mk _)
    exact ⟨fun x => (F x).val, continuous_subtype_val.comp hFc,
      fun x => (F x).property, fun a => congrArg Subtype.val (hFeq a)⟩
  obtain ⟨H, hHc, h0, h1, hfix, hmem⟩ := Paper17.sdr_of_absoluteExtensor hprod
    ⟨P, Metric.mem_ball_self hr⟩ P (Metric.mem_ball_self hr)
  exact ⟨Metric.ball P r, Metric.isOpen_ball, Metric.mem_ball_self hr, hrU,
    H, hHc, h0, h1, fun y t => hrU (hmem y t), fun t _ => hfix t⟩

/-- The literal Mathlib homotopy groups vanish at every prescribed basepoint. -/
theorem delzant_homotopyGroup_eq_one {n : ℕ} (hn : 1 ≤ n) (P : DelzantSpace n) (k : ℕ) :
    ∀ a : HomotopyGroup.Pi (k + 1) (DelzantSpace n) P, a = 1 := by
  obtain ⟨H, hHc, h0, h1, hfix⟩ := corollary_1_3 n hn P
  exact Paper17.homotopyGroup_eq_one_of_strong_contraction P H hHc h0 h1 hfix k

/-- A sphere map contained in an open Hausdorff ball has a filling in the
same ball, with only finitely many normal fans on compact interior subsets. -/
theorem sphere_filling_in_open_ball {n : ℕ} (P : DelzantSpace n) {r : ℝ} (hr : 0 < r)
    (k : ℕ) (f : sphere k → DelzantSpace n) (hf : Continuous f)
    (hfr : ∀ x, dist (f x) P < r) :
    ∃ F : ball k → DelzantSpace n, Continuous F ∧
      (∀ x : sphere k, F ⟨x.val, x.property.le⟩ = f x) ∧
      (∀ x, dist (F x) P < r) ∧
      (∀ C : Set (ball k), IsCompact C → (∀ x ∈ C, ∑ i, x.val i ^ 2 < 1) →
        (normalFan ∘ DelzantPolytope.carrier ∘ F '' C).Finite) := by
  obtain ⟨G, hGc, hGeq, hGr, hGfans⟩ := carrier_ball_extension_controlled P hr
    (V (k + 1)) (sphere k) (Paper17.isClosed_sphere k) f hf hfr
  let F : ball k → DelzantSpace n := fun x => G x.val
  refine ⟨F, hGc.comp continuous_subtype_val, ?_, fun x => hGr x.val, ?_⟩
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

import Verification.EuclideanConvergence
import Verification.TopologicalConsequences

/-! Main source statements with the exact Euclidean Hausdorff metric. -/
noncomputable section
open scoped Topology BigOperators
namespace P17Contract

/-- Rescaling the coordinate-metric error supplies the source Euclidean error. -/
theorem euclidean_error_lt_of_pi_error {n : ℕ} (K L : PosBody n) {δ : ℝ}
    (h : Metric.hausdorffDist K.carrier L.carrier < δ / (n + 1 : ℝ)) :
    euclideanHausdorffDist K.carrier L.carrier < δ := by
  have hc : (0 : ℝ) < n + 1 := by positivity
  calc euclideanHausdorffDist K.carrier L.carrier
      ≤ (n : ℝ) * Metric.hausdorffDist K.carrier L.carrier :=
        euclideanHausdorffDist_le_dimension_mul K L
    _ ≤ (n + 1 : ℝ) * Metric.hausdorffDist K.carrier L.carrier :=
      mul_le_mul_of_nonneg_right (by linarith) Metric.hausdorffDist_nonneg
    _ < (n + 1 : ℝ) * (δ / (n + 1 : ℝ)) := mul_lt_mul_of_pos_left h hc
    _ = δ := by field_simp

/-- Proposition 4.3 with the exact source metric, including locally finite
actual normal fans at every point. -/
theorem proposition_4_3_euclidean {X : Type} [MetricSpace X] {n : ℕ}
    (f : X → EuclideanBody n) (hf : Continuous f)
    (ε : X → ℝ) (hε : Continuous ε) (hpos : ∀ x, 0 < ε x) :
    ∃ g : X → EuclideanDelzantSpace n, Continuous g ∧
      (∀ x, dist (g x).val (f x) < ε x) ∧
      LocallyFiniteFansOn (fun x => (⟨(g x).val.body, (g x).property⟩ : DelzantSpace n)) Set.univ := by
  have hc : (0 : ℝ) < n + 1 := by positivity
  obtain ⟨g, hgc, herr, hfin⟩ := proposition_4_3
    (fun x => (f x).body) ((euclideanBodyHomeomorph n).symm.continuous.comp hf)
    (fun x => ε x / (n + 1 : ℝ)) (hε.div_const _) (fun x => div_pos (hpos x) hc)
  refine ⟨fun x => euclideanDelzantHomeomorph n (g x),
    (euclideanDelzantHomeomorph n).continuous.comp hgc, ?_, hfin⟩
  intro x
  rw [EuclideanBody.dist_eq]
  exact euclidean_error_lt_of_pi_error (g x).val (f x).body (herr x)

/-- Theorem 4.4 with the exact source metric and genuine joint continuity at
time zero. The homotopy is defined on all real times, hence restricts to I. -/
theorem theorem_4_4_euclidean (n : ℕ) :
    ∃ H : EuclideanBody n × ℝ → EuclideanBody n, Continuous H ∧
      (∀ K, H (K, 0) = K) ∧
      (∀ K t, 0 < t → t ≤ 1 →
        ∃ P : EuclideanDelzantSpace n, H (K, t) = P.val ∧ dist (H (K, t)) K < t) := by
  let X := EuclideanBody n × Set.Ioi (0 : ℝ)
  obtain ⟨g, hgc, herr, _⟩ := proposition_4_3_euclidean
    (fun p : X => p.1) continuous_fst (fun p => p.2.val)
    (continuous_subtype_val.comp continuous_snd) (fun p => p.2.property)
  let gb : X → EuclideanBody n := fun p => (g p).val
  have hgb : Continuous gb := continuous_subtype_val.comp hgc
  obtain ⟨H, hHc, hzero, hpos⟩ := Paper17.extend_positive_time gb hgb herr
  refine ⟨H, hHc, hzero, ?_⟩
  intro K t ht ht1
  refine ⟨g (K, ⟨t, ht⟩), ?_, ?_⟩
  · rw [hpos K t ht]
  · rw [hpos K t ht]
    exact herr (K, ⟨t, ht⟩)

/-- The prescribed-fan approximation lemma with the exact source error. -/
theorem lemma_4_2_euclidean {n m : ℕ} (K : EuclideanBody n)
    (Ps : Fin m → EuclideanDelzantSpace n) {η : ℝ} (hη : 0 < η) :
    ∃ Q : EuclideanDelzantSpace n, dist Q.val K < η ∧
      ∀ i, DelzantPolytope.le ((euclideanDelzantHomeomorph n).symm (Ps i))
        ((euclideanDelzantHomeomorph n).symm Q) := by
  obtain ⟨Q, hQ, hfan⟩ := lemma_4_2 K.body (fun i => (euclideanDelzantHomeomorph n).symm (Ps i))
    (div_pos hη (by positivity : (0 : ℝ) < n + 1))
  refine ⟨euclideanDelzantHomeomorph n Q, ?_, ?_⟩
  · rw [EuclideanBody.dist_eq]
    exact euclidean_error_lt_of_pi_error Q.val K.body hQ
  · intro i
    simpa only [Homeomorph.symm_apply_apply] using hfan i

/-- Corollary 1.3 as an actual based strong contraction in the source metric. -/
theorem corollary_1_3_euclidean {n : ℕ} (hn : 1 ≤ n) (P : EuclideanDelzantSpace n) :
    ∃ H : EuclideanDelzantSpace n × ℝ → EuclideanDelzantSpace n, Continuous H ∧
      (∀ Q, H (Q, 0) = Q) ∧ (∀ Q, H (Q, 1) = P) ∧ (∀ t, H (P, t) = P) := by
  let e := euclideanDelzantHomeomorph n
  obtain ⟨H, hHc, h0, h1, hfix⟩ := corollary_1_3 n hn (e.symm P)
  refine ⟨fun q => e (H (e.symm q.1, q.2)),
    e.continuous.comp (hHc.comp ((e.symm.continuous.comp continuous_fst).prodMk continuous_snd)),
    ?_, ?_, ?_⟩
  · intro Q
    dsimp only
    rw [h0, e.apply_symm_apply]
  · intro Q
    dsimp only
    rw [h1, e.apply_symm_apply]
  · intro t
    dsimp only
    rw [hfix, e.apply_symm_apply]

theorem euclidean_homotopyGroup_eq_one {n : ℕ} (hn : 1 ≤ n)
    (P : EuclideanDelzantSpace n) (k : ℕ) :
    ∀ a : HomotopyGroup.Pi (k + 1) (EuclideanDelzantSpace n) P, a = 1 := by
  obtain ⟨H, hHc, h0, h1, hfix⟩ := corollary_1_3_euclidean hn P
  exact Paper17.homotopyGroup_eq_one_of_strong_contraction P H hHc h0 h1 hfix k

theorem inSupportSet_bodySphericalSupport {n : ℕ} (W : Set (PaperSupportSpace n)) (P : DelzantSpace n) :
    InSupportSet W P ↔ bodySphericalSupport P.val ∈ W := by
  have heq : bodySphericalSupport P.val = sphericalRestriction n (toSupport P) := by
    ext u
    rw [bodySphericalSupport_apply, sphericalRestriction_toSupport]
    rfl
  rw [inSupportSet_iff, ← heq]

/-- The entire controlled extension stays in the source open convex support
set when carriers have their exact Euclidean metric. -/
theorem euclidean_extension_in_spherical_open_controlled {n : ℕ}
    (W : Set (PaperSupportSpace n)) (hW : IsOpen W) (hcW : Convex ℝ W)
    (hne : ∃ P : EuclideanDelzantSpace n, bodySphericalSupport P.val.body ∈ W)
    (X : Type) [MetricSpace X] (A : Set X) (hA : IsClosed A)
    (f : A → EuclideanDelzantSpace n) (hf : Continuous f)
    (hfW : ∀ a, bodySphericalSupport (f a).val.body ∈ W) :
    ∃ F : X → EuclideanDelzantSpace n, Continuous F ∧ (∀ a : A, F a = f a) ∧
      (∀ x, bodySphericalSupport (F x).val.body ∈ W) ∧
      LocallyFiniteFansOn (fun x => (euclideanDelzantHomeomorph n).symm (F x)) Aᶜ := by
  let e := euclideanDelzantHomeomorph n
  obtain ⟨P, hP⟩ := hne
  obtain ⟨G, hGc, hGeq, hGW, hfin⟩ := carrier_extension_in_spherical_open_controlled
    W hW hcW ⟨e.symm P, (inSupportSet_bodySphericalSupport W (e.symm P)).mpr hP⟩
    X A hA (e.symm ∘ f) (e.symm.continuous.comp hf)
    (fun a => (inSupportSet_bodySphericalSupport W (e.symm (f a))).mpr (hfW a))
  refine ⟨e ∘ G, e.continuous.comp hGc, ?_, ?_, ?_⟩
  · intro a
    rw [Function.comp_apply, hGeq, Function.comp_apply, e.apply_symm_apply]
  · intro x
    exact (inSupportSet_bodySphericalSupport W (G x)).mp (hGW x)
  · simpa only [Function.comp_apply, e.symm_apply_apply] using hfin

/-- The full open-convex source restriction is an AE and AR in the exact
Euclidean carrier metric. -/
theorem theorem_1_2_euclidean_open {n : ℕ} (W : Set (PaperSupportSpace n))
    (hW : IsOpen W) (hcW : Convex ℝ W)
    (hne : Nonempty {P : EuclideanDelzantSpace n // bodySphericalSupport P.val.body ∈ W}) :
    IsAbsoluteExtensor {P : EuclideanDelzantSpace n // bodySphericalSupport P.val.body ∈ W} ∧
      IsAbsoluteRetract {P : EuclideanDelzantSpace n // bodySphericalSupport P.val.body ∈ W} := by
  have hAE : IsAbsoluteExtensor {P : EuclideanDelzantSpace n // bodySphericalSupport P.val.body ∈ W} := by
    intro X _ A hA f hf
    obtain ⟨P⟩ := hne
    obtain ⟨F, hFc, hFeq, hFW, _⟩ := euclidean_extension_in_spherical_open_controlled W hW hcW
      ⟨P.val, P.property⟩ X A hA (fun a => (f a).val) (continuous_subtype_val.comp hf)
      (fun a => (f a).property)
    exact ⟨fun x => ⟨F x, hFW x⟩, hFc.subtype_mk _, fun a => Subtype.ext (hFeq a)⟩
  exact ⟨hAE, def_1_1 hAE hne⟩

/-- Every nonempty positive Euclidean Hausdorff ball is an AE and AR. -/
theorem euclidean_open_ball_absoluteExtensor_retract {n : ℕ} (P : EuclideanDelzantSpace n)
    {r : ℝ} (hr : 0 < r) :
    IsAbsoluteExtensor (Metric.ball P r) ∧ IsAbsoluteRetract (Metric.ball P r) := by
  have heq : {Q : EuclideanDelzantSpace n |
      bodySphericalSupport Q.val.body ∈ Metric.ball (bodySphericalSupport P.val.body) r} =
      Metric.ball P r := by
    ext Q
    rfl
  have hne : Nonempty {Q : EuclideanDelzantSpace n //
      bodySphericalSupport Q.val.body ∈ Metric.ball (bodySphericalSupport P.val.body) r} :=
    ⟨⟨P, Metric.mem_ball_self hr⟩⟩
  simpa only [heq] using theorem_1_2_euclidean_open
    (Metric.ball (bodySphericalSupport P.val.body) r) Metric.isOpen_ball (convex_ball _ _) hne

/-- Source sphere filling in an open convex support set, with exact Euclidean
carrier topology and finite normal-fan range on compact interior subsets. -/
theorem euclidean_sphere_filling_in_spherical_open {n : ℕ}
    (W : Set (PaperSupportSpace n)) (hW : IsOpen W) (hcW : Convex ℝ W)
    (hne : ∃ P : EuclideanDelzantSpace n, bodySphericalSupport P.val.body ∈ W)
    (k : ℕ) (f : sphere k → EuclideanDelzantSpace n) (hf : Continuous f)
    (hfW : ∀ x, bodySphericalSupport (f x).val.body ∈ W) :
    ∃ F : ball k → EuclideanDelzantSpace n, Continuous F ∧
      (∀ x : sphere k, F ⟨x.val, x.property.le⟩ = f x) ∧
      (∀ x, bodySphericalSupport (F x).val.body ∈ W) ∧
      (∀ C : Set (ball k), IsCompact C → (∀ x ∈ C, ∑ i, x.val i ^ 2 < 1) →
        ((fun x => normalFan (F x).val.body.carrier) '' C).Finite) := by
  obtain ⟨G, hGc, hGeq, hGW, hGfans⟩ := euclidean_extension_in_spherical_open_controlled
    W hW hcW hne (V (k + 1)) (sphere k) (Paper17.isClosed_sphere k) f hf hfW
  let F : ball k → EuclideanDelzantSpace n := fun x => G x.val
  refine ⟨F, hGc.comp continuous_subtype_val, fun x => hGeq x, fun x => hGW x.val, ?_⟩
  intro C hC hinside
  have hsub : Subtype.val '' C ⊆ (sphere k)ᶜ := by
    rintro x ⟨y, hy, rfl⟩
    exact ne_of_lt (hinside y hy)
  have hfin := finite_image_of_locally_finite_range
    (normalFan ∘ DelzantPolytope.carrier ∘ (fun x => (euclideanDelzantHomeomorph n).symm (G x)))
    (hC.image continuous_subtype_val) hsub hGfans
  change ((fun x => normalFan (G x).val.body.carrier) '' (Subtype.val '' C)).Finite at hfin
  simpa only [Set.image_image, Function.comp_def, F] using hfin

/-- The filling can be chosen in the very same open Euclidean Hausdorff ball. -/
theorem euclidean_sphere_filling_in_open_ball {n : ℕ} (P : EuclideanDelzantSpace n)
    {r : ℝ} (hr : 0 < r) (k : ℕ) (f : sphere k → EuclideanDelzantSpace n)
    (hf : Continuous f) (hfr : ∀ x, dist (f x) P < r) :
    ∃ F : ball k → EuclideanDelzantSpace n, Continuous F ∧
      (∀ x : sphere k, F ⟨x.val, x.property.le⟩ = f x) ∧ (∀ x, dist (F x) P < r) ∧
      (∀ C : Set (ball k), IsCompact C → (∀ x ∈ C, ∑ i, x.val i ^ 2 < 1) →
        ((fun x => normalFan (F x).val.body.carrier) '' C).Finite) := by
  obtain ⟨F, hFc, hFeq, hFW, hfin⟩ := euclidean_sphere_filling_in_spherical_open
    (Metric.ball (bodySphericalSupport P.val.body) r) Metric.isOpen_ball (convex_ball _ _)
    ⟨P, Metric.mem_ball_self hr⟩ k f hf hfr
  exact ⟨F, hFc, hFeq, hFW, hfin⟩

/-- The main AE/AR theorem with the exact source Euclidean Hausdorff metric. -/
theorem theorem_1_2_euclidean (n : ℕ) :
    IsAbsoluteExtensor (EuclideanDelzantSpace n) ∧ IsAbsoluteRetract (EuclideanDelzantSpace n) := by
  have hAE := absoluteExtensor_homeomorph (carrier_absoluteExtensor n) (euclideanDelzantHomeomorph n)
  obtain ⟨P⟩ := Paper17.delzant_nonempty n
  exact ⟨hAE, def_1_1 hAE ⟨euclideanDelzantHomeomorph n (ofProduction P)⟩⟩

end P17Contract

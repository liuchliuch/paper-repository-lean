import Verification.VolumeMetric

/-! Literal source topological consequences for both metrics, plus the
open-neighborhood clause of Lemma 2.3 in the exact source normalization. -/
noncomputable section
open scoped Topology BigOperators
namespace P17Contract

theorem lemma_2_3_euclidean_open {n m : ℕ} (P : EuclideanDelzantSpace n)
    (Ps : Fin m → EuclideanDelzantSpace n) {η : ℝ} (hη : 0 < η)
    (W : Set (PaperSupportSpace n)) (hW : IsOpen W)
    (hP : bodySphericalSupport P.val.body ∈ W) :
    ∃ Q : EuclideanDelzantSpace n, dist Q P < η ∧
      bodySphericalSupport Q.val.body ∈ W ∧
      DelzantPolytope.le ((euclideanDelzantHomeomorph n).symm P)
        ((euclideanDelzantHomeomorph n).symm Q) ∧
      ∀ i, DelzantPolytope.le ((euclideanDelzantHomeomorph n).symm (Ps i))
        ((euclideanDelzantHomeomorph n).symm Q) := by
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hW _ hP
  obtain ⟨Q, hQ, hfan⟩ := lemma_4_2_euclidean P.val (Fin.cons P Ps) (lt_min hη hr)
  refine ⟨Q, hQ.trans_le (min_le_left _ _), ?_, hfan 0, fun i => hfan i.succ⟩
  apply hrW
  exact hQ.trans_le (min_le_right _ _)

theorem euclidean_locally_contractible {n : ℕ} (P : EuclideanDelzantSpace n)
    (U : Set (EuclideanDelzantSpace n)) (hU : U ∈ 𝓝 P) :
    ∃ V : Set (EuclideanDelzantSpace n), IsOpen V ∧ P ∈ V ∧ V ⊆ U ∧
      ∃ H : V × ℝ → EuclideanDelzantSpace n, Continuous H ∧
        (∀ y : V, H (y, 0) = y.val) ∧ (∀ y : V, H (y, 1) = P) ∧
        (∀ y t, H (y, t) ∈ U) ∧ (∀ t, ∀ hp : P ∈ V, H (⟨P, hp⟩, t) = P) := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  have hAE := (euclidean_open_ball_absoluteExtensor_retract P hr).1
  have hprod : Paper17.IsAbsoluteExtensor (Metric.ball P r) := by
    intro X _ A hA f hf hfV
    obtain ⟨F, hFc, hFeq⟩ := hAE X A hA (fun a => ⟨f a, hfV a⟩) (hf.subtype_mk _)
    exact ⟨fun x => (F x).val, continuous_subtype_val.comp hFc,
      fun x => (F x).property, fun a => congrArg Subtype.val (hFeq a)⟩
  obtain ⟨H, hHc, h0, h1, hfix, hmem⟩ := Paper17.sdr_of_absoluteExtensor hprod
    ⟨P, Metric.mem_ball_self hr⟩ P (Metric.mem_ball_self hr)
  exact ⟨Metric.ball P r, Metric.isOpen_ball, Metric.mem_ball_self hr, hrU,
    H, hHc, h0, h1, fun y t => hrU (hmem y t), fun t _ => hfix t⟩

theorem euclidean_contractible {n : ℕ} (hn : 1 ≤ n) (P : EuclideanDelzantSpace n) :
    ContractibleSpace (EuclideanDelzantSpace n) := by
  obtain ⟨H, hHc, h0, h1, _⟩ := corollary_1_3_euclidean hn P
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨P, ⟨{
    toFun := fun p => H (p.2, (p.1 : ℝ))
    continuous_toFun := hHc.comp (continuous_snd.prodMk
      (continuous_subtype_val.comp continuous_fst))
    map_zero_left := h0
    map_one_left := h1 }⟩⟩

theorem euclidean_pathConnected {n : ℕ} (hn : 1 ≤ n) (P : EuclideanDelzantSpace n) :
    PathConnectedSpace (EuclideanDelzantSpace n) := by
  letI := euclidean_contractible hn P
  infer_instance

theorem corollary_1_3_volume {n : ℕ} (hn : 1 ≤ n) (P : VolumeDelzantSpace n) :
    ∃ H : VolumeDelzantSpace n × ℝ → VolumeDelzantSpace n, Continuous H ∧
      (∀ Q, H (Q, 0) = Q) ∧ (∀ Q, H (Q, 1) = P) ∧ (∀ t, H (P, t) = P) := by
  let e := volumeDelzantHomeomorph n
  obtain ⟨H, hHc, h0, h1, hfix⟩ := corollary_1_3_euclidean hn (e.symm P)
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

theorem volume_homotopyGroup_eq_one {n : ℕ} (hn : 1 ≤ n)
    (P : VolumeDelzantSpace n) (k : ℕ) :
    ∀ a : HomotopyGroup.Pi (k + 1) (VolumeDelzantSpace n) P, a = 1 := by
  obtain ⟨H, hHc, h0, h1, hfix⟩ := corollary_1_3_volume hn P
  exact Paper17.homotopyGroup_eq_one_of_strong_contraction P H hHc h0 h1 hfix k

theorem volume_contractible {n : ℕ} (hn : 1 ≤ n) (P : VolumeDelzantSpace n) :
    ContractibleSpace (VolumeDelzantSpace n) := by
  obtain ⟨H, hHc, h0, h1, _⟩ := corollary_1_3_volume hn P
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨P, ⟨{
    toFun := fun p => H (p.2, (p.1 : ℝ))
    continuous_toFun := hHc.comp (continuous_snd.prodMk
      (continuous_subtype_val.comp continuous_fst))
    map_zero_left := h0
    map_one_left := h1 }⟩⟩

theorem volume_pathConnected {n : ℕ} (hn : 1 ≤ n) (P : VolumeDelzantSpace n) :
    PathConnectedSpace (VolumeDelzantSpace n) := by
  letI := volume_contractible hn P
  infer_instance

/-- Local contraction transported by the actual identity homeomorphism. -/
theorem volume_locally_contractible {n : ℕ} (P : VolumeDelzantSpace n)
    (U : Set (VolumeDelzantSpace n)) (hU : U ∈ 𝓝 P) :
    ∃ V : Set (VolumeDelzantSpace n), IsOpen V ∧ P ∈ V ∧ V ⊆ U ∧
      ∃ H : V × ℝ → VolumeDelzantSpace n, Continuous H ∧
        (∀ y : V, H (y, 0) = y.val) ∧ (∀ y : V, H (y, 1) = P) ∧
        (∀ y t, H (y, t) ∈ U) ∧ (∀ t, ∀ hp : P ∈ V, H (⟨P, hp⟩, t) = P) := by
  let e := volumeDelzantHomeomorph n
  have hpre : e ⁻¹' U ∈ 𝓝 (e.symm P) := by
    exact e.continuous.continuousAt.preimage_mem_nhds (by simpa only [e.apply_symm_apply] using hU)
  obtain ⟨V, hVo, hPV, hVU, H, hHc, h0, h1, hmem, hfix⟩ :=
    euclidean_locally_contractible (e.symm P) (e ⁻¹' U) hpre
  let W : Set (VolumeDelzantSpace n) := e.symm ⁻¹' V
  have hWU : W ⊆ U := by
    intro y hy
    simpa only [Set.mem_preimage, e.apply_symm_apply] using hVU hy
  let j : W → V := fun y => ⟨e.symm y.val, y.property⟩
  have hj : Continuous j := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _
  refine ⟨W, hVo.preimage e.symm.continuous, hPV, hWU,
    fun q => e (H (j q.1, q.2)),
    e.continuous.comp (hHc.comp ((hj.comp continuous_fst).prodMk continuous_snd)), ?_, ?_, ?_, ?_⟩
  · intro y
    dsimp only
    rw [h0]
    exact e.apply_symm_apply y.val
  · intro y
    dsimp only
    rw [h1, e.apply_symm_apply]
  · intro y t
    exact hmem (j y) t
  · intro t hp
    change e (H (⟨e.symm P, hp⟩, t)) = P
    rw [hfix t hp, e.apply_symm_apply]

/-- The source spherical-open filling also uses the literal volume metric. -/
theorem volume_sphere_filling_in_spherical_open {n : ℕ}
    (W : Set (PaperSupportSpace n)) (hW : IsOpen W) (hcW : Convex ℝ W)
    (hne : ∃ P : VolumeDelzantSpace n, bodySphericalSupport P.val.body.body ∈ W)
    (k : ℕ) (f : sphere k → VolumeDelzantSpace n) (hf : Continuous f)
    (hfW : ∀ x, bodySphericalSupport (f x).val.body.body ∈ W) :
    ∃ F : ball k → VolumeDelzantSpace n, Continuous F ∧
      (∀ x : sphere k, F ⟨x.val, x.property.le⟩ = f x) ∧
      (∀ x, bodySphericalSupport (F x).val.body.body ∈ W) ∧
      (∀ C : Set (ball k), IsCompact C → (∀ x ∈ C, ∑ i, x.val i ^ 2 < 1) →
        ((fun x => normalFan (F x).val.body.body.carrier) '' C).Finite) := by
  let e := volumeDelzantHomeomorph n
  obtain ⟨P, hP⟩ := hne
  obtain ⟨G, hGc, hGeq, hGW, hfin⟩ := euclidean_sphere_filling_in_spherical_open W hW hcW
    ⟨e.symm P, hP⟩ k (e.symm ∘ f) (e.symm.continuous.comp hf) hfW
  refine ⟨e ∘ G, e.continuous.comp hGc, ?_, hGW, hfin⟩
  intro x
  rw [Function.comp_apply, hGeq, Function.comp_apply, e.apply_symm_apply]


end P17Contract

import Verification.QuantitativeDiskInterior

/-! Gluing the actual interior filling to the prescribed loop, with its
uniform modulus estimate and compact-interior finite normal-fan range. -/
noncomputable section
open scoped Topology
namespace P17Contract.QuantitativeDisk
variable {n : ℕ}

theorem extend_interior_filling_with_modulus (f : Angle → EuclideanDelzantSpace n)
    (hf : Continuous f) (G : OpenDisk → EuclideanDelzantSpace n) (hGc : Continuous G)
    (herr : ∀ x : OpenDisk, 1 / 2 ≤ ‖x.val‖ →
      dist (G x) (f (totalAngle x.val)) ≤ depth x / 4 + Paper17.loopModulus f (depth x / 16))
    (hfin : ∀ x, ∃ U ∈ 𝓝 x, ((fun y => normalFan (G y).val.body.carrier) '' U).Finite) :
    ∃ F : ClosedDisk → EuclideanDelzantSpace n, Continuous F ∧
      (∀ θ, F (boundaryPoint θ) = f θ) ∧
      (∀ θ s (hs : 0 < s) (hsHalf : s ≤ 1 / 2),
        dist (F (polarClosed θ s hs.le (by linarith))) (f θ) ≤
          s / 4 + Paper17.loopModulus f (s / 16)) ∧
      (∀ C : Set ClosedDisk, IsCompact C → (∀ x ∈ C, ‖x.val‖ < 1) →
        ((fun x => normalFan (F x).val.body.carrier) '' C).Finite) := by
  classical
  let F : ClosedDisk → EuclideanDelzantSpace n := fun x =>
    if hx : ‖x.val‖ < 1 then G ⟨x.val, hx⟩ else f (totalAngle x.val)
  let R : ClosedDisk → EuclideanDelzantSpace n := fun x => f (totalAngle x.val)
  have hclosedBound : ∀ x : ClosedDisk, 1 / 2 ≤ ‖x.val‖ →
      dist (F x) (R x) ≤ (1 - ‖x.val‖) / 4 + Paper17.loopModulus f ((1 - ‖x.val‖) / 16) := by
    intro x hx
    by_cases hi : ‖x.val‖ < 1
    · simpa only [F, dif_pos hi, R, depth] using herr ⟨x.val, hi⟩ hx
    · change dist (F x) (f (totalAngle x.val)) ≤ _
      rw [show F x = f (totalAngle x.val) from dif_neg hi, dist_self]
      exact add_nonneg (div_nonneg (sub_nonneg.mpr x.property) (by norm_num))
        (Paper17.loopModulus_nonneg hf (div_nonneg (sub_nonneg.mpr x.property) (by norm_num)))
  have hcontIn : ContinuousOn F {x : ClosedDisk | ‖x.val‖ < 1} := by
    rw [continuousOn_iff_continuous_restrict]
    let e : {x : ClosedDisk | ‖x.val‖ < 1} → OpenDisk := fun x => ⟨x.val.val, x.property⟩
    have he : Continuous e := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    change Continuous (fun x : {x : ClosedDisk | ‖x.val‖ < 1} => F x.val)
    convert hGc.comp he using 1
    funext x
    exact dif_pos x.property
  have hFc : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : ‖x.val‖ < 1
    · exact hcontIn.continuousAt ((isOpen_lt continuous_subtype_val.norm continuous_const).mem_nhds hx)
    have hxeq : ‖x.val‖ = 1 := le_antisymm x.property (le_of_not_gt hx)
    have hRx : ContinuousAt R x := hf.continuousAt.comp
      ((continuousAt_totalAngle (by rw [hxeq]; norm_num)).comp continuous_subtype_val.continuousAt)
    have hFx : F x = R x := dif_neg hx
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δR, hδR, hRbound⟩ := Metric.continuousAt_iff.mp hRx (ε / 2) (by linarith)
    obtain ⟨η, hη, hω⟩ := Paper17.loopModulus_small hf (by linarith : (0 : ℝ) < ε / 4)
    let δ : ℝ := min δR (min (1 / 4) (min (ε / 16) η))
    have hδ : 0 < δ := lt_min hδR (lt_min (by norm_num) (lt_min (by positivity) hη))
    refine ⟨δ, hδ, ?_⟩
    intro y hy
    have hyR : dist y x < δR := hy.trans_le (min_le_left _ _)
    have hyquarter : dist y x < 1 / 4 :=
      hy.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hyε : dist y x < ε / 16 :=
      hy.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hyη : dist y x < η :=
      hy.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hs0 : 0 ≤ 1 - ‖y.val‖ := sub_nonneg.mpr y.property
    have hsd : 1 - ‖y.val‖ ≤ dist y x := by
      calc 1 - ‖y.val‖ = ‖x.val‖ - ‖y.val‖ := by rw [hxeq]
        _ ≤ ‖x.val - y.val‖ := norm_sub_norm_le _ _
        _ = dist y x := by rw [← dist_eq_norm]; exact dist_comm _ _
    have hyouter : 1 / 2 ≤ ‖y.val‖ := by linarith
    have harg0 : 0 ≤ (1 - ‖y.val‖) / 16 := div_nonneg hs0 (by norm_num)
    have hargη : (1 - ‖y.val‖) / 16 < η := by linarith
    have hωbound := hω _ harg0 hargη
    have hRef := hRbound hyR
    rw [hFx]
    calc dist (F y) (R x) ≤ dist (F y) (R y) + dist (R y) (R x) := dist_triangle _ _ _
      _ ≤ (1 - ‖y.val‖) / 4 + Paper17.loopModulus f ((1 - ‖y.val‖) / 16) + dist (R y) (R x) :=
        add_le_add_right (hclosedBound y hyouter) _
      _ < ε := by linarith
  refine ⟨F, hFc, ?_, ?_, ?_⟩
  · intro θ
    have hn : ‖(angleCircle θ : ℂ)‖ = 1 := Circle.norm_coe _
    simp [F, boundaryPoint, hn]
  · intro θ s hs hsHalf
    have hs1 : s < 1 := by linarith
    have hn := norm_polarPoint θ hs1.le
    have hi : ‖polarPoint θ s‖ < 1 := by rw [hn]; linarith
    let x : OpenDisk := ⟨polarPoint θ s, hi⟩
    have ho : 1 / 2 ≤ ‖x.val‖ := by change 1 / 2 ≤ ‖polarPoint θ s‖; rw [hn]; linarith
    have hd : depth x = s := by dsimp only [depth, x]; rw [hn]; ring
    have hh := herr x ho
    change dist (G x) (f (totalAngle (polarPoint θ s))) ≤ _ at hh
    rw [totalAngle_polarPoint θ hs1, hd] at hh
    change dist (F (polarClosed θ s hs.le _)) (f θ) ≤ _
    rw [show F (polarClosed θ s hs.le _) = G x from dif_pos hi]
    exact hh
  · intro C hC hinside
    let e : OpenDisk → ClosedDisk := fun x => ⟨x.val, x.property.le⟩
    have he : Isometry e := isometry_iff_dist_eq.mpr (fun _ _ => rfl)
    have hsub : C ⊆ Set.range e := by
      intro x hx
      exact ⟨⟨x.val, hinside x hx⟩, Subtype.ext rfl⟩
    let B : Set OpenDisk := e ⁻¹' C
    have heq : e '' B = C := Set.image_preimage_eq_of_subset hsub
    have hB : IsCompact B := he.isEmbedding.isCompact_iff.mpr (by rw [heq]; exact hC)
    have hfinite := finite_image_of_locally_finite_range
      (fun y => normalFan (G y).val.body.carrier) hB (fun _ _ => Set.mem_univ _)
      (fun y _ => hfin y)
    apply hfinite.subset
    rintro tag ⟨x, hx, rfl⟩
    let y : OpenDisk := ⟨x.val, hinside x hx⟩
    refine ⟨y, ?_, ?_⟩
    · change e y ∈ C
      have hex : e y = x := Subtype.ext rfl
      rw [hex]
      exact hx
    · change normalFan (G y).val.body.carrier = normalFan (F x).val.body.carrier
      rw [show F x = G y from dif_pos (hinside x hx)]

end P17Contract.QuantitativeDisk

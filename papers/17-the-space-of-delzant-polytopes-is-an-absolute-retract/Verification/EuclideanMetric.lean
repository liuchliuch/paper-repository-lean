import Verification.EuclideanNormalization

/-! Exact Euclidean carrier metrics and transport of the topological results. -/
noncomputable section
open scoped Topology BigOperators
namespace P17Contract

theorem norm_euclideanCoordinates_le_l1 {n : ℕ} (x : V n) :
    ‖euclideanCoordinates n x‖ ≤ ∑ i, |x i| := by
  have hh := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i : Fin n => |x i|) (fun i _ => abs_nonneg (x i))
  simp only [sq_abs] at hh
  rw [← norm_euclideanCoordinates_sq] at hh
  have hn := norm_nonneg (euclideanCoordinates n x)
  have hs : 0 ≤ ∑ i, |x i| := Finset.sum_nonneg (fun i _ => abs_nonneg (x i))
  nlinarith

theorem directionL1_le_dimension {n : ℕ} (u : UnitDirections n) : directionL1 u ≤ n := by
  have hcoord : ∀ i, |u.val i| ≤ 1 := by
    intro i
    have hi : u.val i ^ 2 ≤ 1 := (Finset.single_le_sum
      (fun j _ => sq_nonneg (u.val j)) (Finset.mem_univ i)).trans_eq u.property
    rw [abs_le]
    constructor <;> nlinarith
  calc directionL1 u = ∑ i, |u.val i| := rfl
    _ ≤ ∑ _ : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hcoord i)
    _ = n := by simp

theorem norm_bodySupport_sub {n : ℕ} (K L : PosBody n) :
    ‖bodySupport K - bodySupport L‖ = Metric.hausdorffDist K.carrier L.carrier := by
  rw [← dist_eq_norm, isometry_bodySupport.dist_eq]
  rfl

/-- Quantitative equivalence of the exact Euclidean and coordinate sup
Hausdorff metrics; hence all previously constructed maps retain continuity. -/
theorem euclideanHausdorffDist_le_dimension_mul {n : ℕ} (K L : PosBody n) :
    euclideanHausdorffDist K.carrier L.carrier ≤
      (n : ℝ) * Metric.hausdorffDist K.carrier L.carrier := by
  rw [euclideanHausdorffDist_eq_norm_sphericalSupport]
  apply (ContinuousMap.norm_le _ (mul_nonneg (Nat.cast_nonneg n) Metric.hausdorffDist_nonneg)).mpr
  intro u
  change |directionL1 u * bodySupport K (normalizeDirection u) -
    directionL1 u * bodySupport L (normalizeDirection u)| ≤ _
  rw [← mul_sub, abs_mul, abs_of_pos (directionL1_pos u)]
  have hh := (bodySupport K - bodySupport L).norm_coe_le_norm (normalizeDirection u)
  rw [norm_bodySupport_sub] at hh
  calc directionL1 u * |bodySupport K (normalizeDirection u) - bodySupport L (normalizeDirection u)|
      ≤ directionL1 u * Metric.hausdorffDist K.carrier L.carrier :=
        mul_le_mul_of_nonneg_left hh (directionL1_pos u).le
    _ ≤ (n : ℝ) * Metric.hausdorffDist K.carrier L.carrier :=
      mul_le_mul_of_nonneg_right (directionL1_le_dimension u) Metric.hausdorffDist_nonneg

theorem hausdorffDist_le_euclideanHausdorffDist {n : ℕ} (K L : PosBody n) :
    Metric.hausdorffDist K.carrier L.carrier ≤ euclideanHausdorffDist K.carrier L.carrier := by
  rw [← norm_bodySupport_sub]
  apply (ContinuousMap.norm_le _ Metric.hausdorffDist_nonneg).mpr
  intro u
  change |Paper17.supportFunction K.carrier u.val - Paper17.supportFunction L.carrier u.val| ≤ _
  let e := euclideanCoordinates n
  have hK := K.isCompact.image e.continuous
  have hL := L.isCompact.image e.continuous
  have hplus := Paper17.EuclideanSupport.support_sub_le_hausdorff_mul hK
    (K.nonempty.image e) hL (L.nonempty.image e) (e u.val)
  have hminus := Paper17.EuclideanSupport.support_sub_le_hausdorff_mul hL
    (L.nonempty.image e) hK (K.nonempty.image e) (e u.val)
  rw [Metric.hausdorffDist_comm] at hminus
  dsimp only [e] at hplus hminus
  rw [euclidean_support_image, euclidean_support_image] at hplus hminus
  change Paper17.supportFunction K.carrier u.val - Paper17.supportFunction L.carrier u.val ≤
    euclideanHausdorffDist K.carrier L.carrier * ‖e u.val‖ at hplus
  change Paper17.supportFunction L.carrier u.val - Paper17.supportFunction K.carrier u.val ≤
    euclideanHausdorffDist K.carrier L.carrier * ‖e u.val‖ at hminus
  have hun : ‖e u.val‖ ≤ 1 := (norm_euclideanCoordinates_le_l1 u.val).trans u.property
  have hb : euclideanHausdorffDist K.carrier L.carrier * ‖e u.val‖ ≤
      euclideanHausdorffDist K.carrier L.carrier :=
    mul_le_of_le_one_right Metric.hausdorffDist_nonneg hun
  exact abs_le.mpr ⟨by
    change -euclideanHausdorffDist K.carrier L.carrier ≤
      Paper17.supportFunction K.carrier u.val - Paper17.supportFunction L.carrier u.val
    linarith, hplus.trans hb⟩

theorem bodySphericalSupport_injective {n : ℕ} : Function.Injective (@bodySphericalSupport n) := by
  intro K L h
  have he : euclideanHausdorffDist K.carrier L.carrier = 0 := by
    rw [euclideanHausdorffDist_eq_norm_sphericalSupport, h, sub_self, norm_zero]
  have hh := hausdorffDist_le_euclideanHausdorffDist K L
  rw [he] at hh
  exact dist_eq_zero.mp (le_antisymm hh dist_nonneg)

/-- The same positive carriers equipped with the exact source Euclidean
Hausdorff metric, as distinct from their coordinate sup-metric presentation. -/
structure EuclideanBody (n : ℕ) where
  body : PosBody n

instance (n : ℕ) : MetricSpace (EuclideanBody n) :=
  MetricSpace.induced (fun K => bodySphericalSupport K.body)
    (by intro K L h; cases K; cases L; congr; exact bodySphericalSupport_injective h) inferInstance

@[simp] theorem EuclideanBody.dist_eq {n : ℕ} (K L : EuclideanBody n) :
    dist K L = euclideanHausdorffDist K.body.carrier L.body.carrier := by
  change dist (bodySphericalSupport K.body) (bodySphericalSupport L.body) = _
  rw [dist_eq_norm, euclideanHausdorffDist_eq_norm_sphericalSupport]

/-- Quantitative metric comparison gives the actual identity homeomorphism. -/
def euclideanBodyHomeomorph (n : ℕ) : PosBody n ≃ₜ EuclideanBody n where
  toFun K := ⟨K⟩
  invFun := EuclideanBody.body
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (LipschitzWith.of_dist_le_mul (K := (n : NNReal)) (fun K L => by
    simpa only [EuclideanBody.dist_eq, NNReal.coe_natCast] using
      euclideanHausdorffDist_le_dimension_mul K L)).continuous
  continuous_invFun := (LipschitzWith.of_dist_le_mul (K := 1) (fun K L => by
    simpa only [EuclideanBody.dist_eq, NNReal.coe_one, one_mul] using
      hausdorffDist_le_euclideanHausdorffDist K.body L.body)).continuous

/-- Delzant carriers with the exact Euclidean Hausdorff metric. -/
abbrev EuclideanDelzantSpace (n : ℕ) := {K : EuclideanBody n // IsDelzant K.body}

def euclideanDelzantHomeomorph (n : ℕ) : DelzantSpace n ≃ₜ EuclideanDelzantSpace n where
  toFun P := ⟨⟨P.val⟩, P.property⟩
  invFun P := ⟨P.val.body, P.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (LipschitzWith.of_dist_le_mul (K := (n : NNReal))
    (f := fun P : DelzantSpace n => (⟨⟨P.val⟩, P.property⟩ : EuclideanDelzantSpace n)) (by
      intro P Q
      change dist (⟨P.val⟩ : EuclideanBody n) ⟨Q.val⟩ ≤
        (n : ℝ) * Metric.hausdorffDist P.carrier Q.carrier
      rw [EuclideanBody.dist_eq]
      exact euclideanHausdorffDist_le_dimension_mul P.val Q.val)).continuous
  continuous_invFun := by
    let j : DelzantSpace n → PosBody n := fun P => P.val
    have hj : Isometry j := isometry_iff_dist_eq.mpr (fun _ _ => rfl)
    apply hj.isEmbedding.continuous_iff.mpr
    exact (euclideanBodyHomeomorph n).symm.continuous.comp continuous_subtype_val

theorem absoluteExtensor_homeomorph {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    (hY : IsAbsoluteExtensor Y) (e : Y ≃ₜ Z) : IsAbsoluteExtensor Z := by
  intro X _ A hA f hf
  obtain ⟨F, hFc, hFeq⟩ := hY X A hA (e.symm ∘ f) (e.symm.continuous.comp hf)
  exact ⟨e ∘ F, e.continuous.comp hFc, fun a => by rw [Function.comp_apply, hFeq]; simp⟩


end P17Contract

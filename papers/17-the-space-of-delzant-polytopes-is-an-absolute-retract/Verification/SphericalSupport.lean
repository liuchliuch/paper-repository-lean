import Verification.Bridge
import Mathlib.Topology.CompactOpen

/-!
# The paper's spherical support-function coordinates

The source uses the Euclidean unit sphere. The production extension proof uses
the L1 dual ball of the Pi norm. A continuous linear rescaling map relates these
actual spaces of continuous functions; pulling an open convex set back along
this map gives exactly the source's open-convex restriction.
-/
noncomputable section
open scoped BigOperators Topology
namespace P17Contract

/-- The source's Euclidean unit sphere is compact in the coordinate topology. -/
instance unitDirections_compact (n : ℕ) : CompactSpace (UnitDirections n) := by
  apply isCompact_iff_compactSpace.mp
  have hc : IsClosed {u : V n | ∑ i, u i ^ 2 = 1} := isClosed_eq
    (continuous_finset_sum _ fun i _ => (continuous_apply i).pow 2) continuous_const
  apply (isCompact_closedBall (0 : V n) 1).of_isClosed_subset hc
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  rw [Real.norm_eq_abs, abs_le]
  have hi : u i ^ 2 ≤ 1 := (Finset.single_le_sum
    (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)).trans_eq hu
  constructor <;> nlinarith

/-- L1 length of a Euclidean unit direction. -/
def directionL1 {n : ℕ} (u : UnitDirections n) : ℝ := ∑ i, |u.val i|

theorem continuous_directionL1 {n : ℕ} : Continuous (@directionL1 n) :=
  continuous_finset_sum _ fun i _ => ((continuous_apply i).comp continuous_subtype_val).abs

theorem directionL1_pos {n : ℕ} (u : UnitDirections n) : 0 < directionL1 u := by
  have hn : 0 ≤ directionL1 u := Finset.sum_nonneg fun i _ => abs_nonneg _
  by_contra h
  have hz : directionL1 u = 0 := le_antisymm (le_of_not_gt h) hn
  have hi : ∀ i, u.val i = 0 := by
    intro i
    have hh : |u.val i| ≤ directionL1 u := Finset.single_le_sum
      (fun j _ => abs_nonneg (u.val j)) (Finset.mem_univ i)
    exact abs_nonpos_iff.mp (hz ▸ hh)
  have heq := u.property
  simp [hi] at heq

/-- Radial normalization from the Euclidean unit sphere to the L1 unit sphere. -/
def normalizeDirection {n : ℕ} (u : UnitDirections n) : Paper17.dualUnitBall n :=
  ⟨(directionL1 u)⁻¹ • u.val, by
    change ∑ i, |(directionL1 u)⁻¹ * u.val i| ≤ 1
    simp_rw [abs_mul, abs_of_pos (inv_pos.mpr (directionL1_pos u))]
    rw [← Finset.mul_sum]
    change (directionL1 u)⁻¹ * directionL1 u ≤ 1
    rw [inv_mul_cancel₀ (directionL1_pos u).ne']⟩

theorem continuous_normalizeDirection {n : ℕ} : Continuous (@normalizeDirection n) := by
  apply Continuous.subtype_mk
  exact (continuous_directionL1.inv₀ (fun u => (directionL1_pos u).ne')).smul
    continuous_subtype_val

/-- Continuous linear radial rescaling of support-function coordinates. -/
def sphericalRestriction (n : ℕ) : Paper17.SupportSpace n →ₗ[ℝ] PaperSupportSpace n where
  toFun f := ⟨fun u => directionL1 u * f (normalizeDirection u),
    continuous_directionL1.mul (f.continuous.comp continuous_normalizeDirection)⟩
  map_add' f g := by ext u; exact mul_add _ _ _
  map_smul' c f := by ext u; change _ * (c * _) = c * (_ * _); ring

theorem continuous_sphericalRestriction (n : ℕ) : Continuous (sphericalRestriction n) := by
  let w : C(UnitDirections n, ℝ) := ⟨directionL1, continuous_directionL1⟩
  let q : C(UnitDirections n, Paper17.dualUnitBall n) :=
    ⟨normalizeDirection, continuous_normalizeDirection⟩
  change Continuous (fun f : Paper17.SupportSpace n => w * f.comp q)
  exact continuous_const.mul (ContinuousMap.continuous_precomp q)

@[simp] theorem sphericalRestriction_toSupport {n : ℕ} (P : DelzantSpace n)
    (u : UnitDirections n) :
    sphericalRestriction n (toSupport P) u = supportFunction P.carrier u.val := by
  change directionL1 u * Paper17.supportFunction (toProduction P).carrier
    ((directionL1 u)⁻¹ • u.val) = _
  rw [toProduction_carrier]
  rw [Paper17.supportFunction_direction_smul (K := P.carrier)
    P.val.isCompact P.val.nonempty u.val (inv_nonneg.mpr (directionL1_pos u).le)]
  rw [← mul_assoc, mul_inv_cancel₀ (directionL1_pos u).ne', one_mul]
  rfl

/-- The graph-based statement predicate is exactly membership of the actual
spherical support function, without an arbitrary choice of its values. -/
theorem inSupportSet_iff {n : ℕ} (W : Set (PaperSupportSpace n)) (P : DelzantSpace n) :
    InSupportSet W P ↔ sphericalRestriction n (toSupport P) ∈ W := by
  constructor
  · rintro ⟨h, hh, heq⟩
    have he : h = sphericalRestriction n (toSupport P) := by
      ext u
      exact (heq u).trans (sphericalRestriction_toSupport P u).symm
    exact he ▸ hh
  · intro h
    exact ⟨_, h, sphericalRestriction_toSupport P⟩

/-- Transfer the open convex restriction to the paper's spherical coordinates.
This uses the production main theorem, with its original smooth-resolution
obligation; it does not introduce a new extension assumption. -/
theorem carrier_open_absoluteExtensor (n : ℕ)
    (W : Set (PaperSupportSpace n)) (hW : IsOpen W) (hWc : Convex ℝ W)
    (hne : Nonempty {P : DelzantSpace n // InSupportSet W P}) :
    IsAbsoluteExtensor {P : DelzantSpace n // InSupportSet W P} := by
  let W' := (sphericalRestriction n) ⁻¹' W
  have hW' : IsOpen W' := hW.preimage (continuous_sphericalRestriction n)
  have hW'c : Convex ℝ W' := hWc.linear_preimage (sphericalRestriction n)
  have hne' : (Paper17.delzantSet n ∩ W').Nonempty := by
    obtain ⟨P⟩ := hne
    exact ⟨toSupport P.val, ⟨⟨toProduction P.val, rfl⟩,
      (inSupportSet_iff W P.val).mp P.property⟩⟩
  intro X _ A hA f hf
  let emb : {P : DelzantSpace n // InSupportSet W P} → Paper17.SupportSpace n :=
    fun P => toSupport P.val
  have hi : Isometry emb := isometry_toSupport.comp isometry_subtype_coe
  let e := hi.isEmbedding.toHomeomorph
  obtain ⟨F, hFc, hFY, hFeq⟩ := Paper17.theorem_1_2_open n W' hW' hW'c hne'
    X A hA (emb ∘ f) (hi.continuous.comp hf) (fun a =>
      ⟨⟨toProduction (f a).val, rfl⟩, (inSupportSet_iff W (f a).val).mp (f a).property⟩)
  have hFrange : ∀ x, F x ∈ Set.range emb := by
    intro x
    obtain ⟨P, hP⟩ := (hFY x).1
    have hsupport : toSupport (ofProduction P) = F x := (toSupport_ofProduction P).trans hP
    refine ⟨⟨ofProduction P, (inSupportSet_iff W _).mpr ?_⟩, hsupport⟩
    change sphericalRestriction n (toSupport (ofProduction P)) ∈ W
    rw [hsupport]
    exact (hFY x).2
  refine ⟨fun x => e.symm ⟨F x, hFrange x⟩,
    e.symm.continuous.comp (hFc.subtype_mk _), ?_⟩
  intro a
  apply e.injective
  simp only [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  change F a = (e (f a)).val
  rw [hFeq a]
  exact (hi.isEmbedding.toHomeomorph_apply_coe (f a)).symm

end P17Contract

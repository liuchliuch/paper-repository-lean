import Paper28.L2CoordinateProjections
import Paper28.NormFoldings
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! Actual countable-coordinate branch norm foldings. These definitions
use native lp vectors, and the norm and contraction laws follow directly
from summation over fibers and the reverse triangle inequality. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {ι κ : Type*}

theorem coordinateHilbert_norm_sq (u : CoordinateHilbert ι) : ‖u‖^2 = ∑' i, (u i)^2 := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using
    lp.norm_rpow_eq_tsum (p := 2) (by norm_num) u

theorem coordinateHilbert_summable_sq (u : CoordinateHilbert ι) : Summable (fun i => (u i)^2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using
    (lp.memℓp u).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)

def hilbertFiberRestriction (π : ι → κ) (j : κ) (u : CoordinateHilbert ι) :
    CoordinateHilbert {i : ι // π i = j} :=
  ⟨fun i => u i.val,memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using
      (coordinateHilbert_summable_sq u).subtype (fun i => π i = j))⟩

theorem hilbertFiberRestriction_norm_sq (π : ι → κ) (j : κ) (u : CoordinateHilbert ι) :
    ‖hilbertFiberRestriction π j u‖^2 = ∑' i : {i : ι // π i = j}, (u i.val)^2 :=
  coordinateHilbert_norm_sq _

theorem hilbertFiberRestriction_norms_summable (π : ι → κ) (u : CoordinateHilbert ι) :
    Summable (fun j => ‖hilbertFiberRestriction π j u‖^2) := by
  simp_rw [hilbertFiberRestriction_norm_sq]
  exact ((summable_partition (fun i => sq_nonneg (u i))
    (s := fun j => {i | π i = j}) (fun i => ⟨π i,rfl,fun j hj => hj.symm⟩)).mp
      (coordinateHilbert_summable_sq u)).2

def hilbertPartitionFold (π : ι → κ) (u : CoordinateHilbert ι) : CoordinateHilbert κ :=
  ⟨fun j => ‖hilbertFiberRestriction π j u‖,memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,abs_norm] using
      hilbertFiberRestriction_norms_summable π u)⟩

theorem hilbertPartitionFold_formula (π : ι → κ) (u : CoordinateHilbert ι) (j : κ) :
    hilbertPartitionFold π u j = Real.sqrt (∑' i : {i : ι // π i = j}, (u i.val)^2) := by
  rw [← hilbertFiberRestriction_norm_sq]
  exact (Real.sqrt_sq (norm_nonneg _)).symm

theorem hilbertPartitionFold_norm (π : ι → κ) (u : CoordinateHilbert ι) :
    ‖hilbertPartitionFold π u‖ = ‖u‖ := by
  have hs := (coordinateHilbert_summable_sq u).hasSum.tsum_fiberwise π
  have he : ‖hilbertPartitionFold π u‖^2 = ‖u‖^2 := by
    rw [coordinateHilbert_norm_sq,coordinateHilbert_norm_sq]
    change (∑' j, ‖hilbertFiberRestriction π j u‖^2) = ∑' i, (u i)^2
    simp_rw [hilbertFiberRestriction_norm_sq]
    exact hs.tsum_eq
  nlinarith [norm_nonneg (hilbertPartitionFold π u),norm_nonneg u]

theorem hilbertPartitionFold_dist (π : ι → κ) (u v : CoordinateHilbert ι) :
    ‖hilbertPartitionFold π u-hilbertPartitionFold π v‖ ≤ ‖u-v‖ := by
  have hPoint : ∀ j, ((hilbertPartitionFold π u-hilbertPartitionFold π v) j)^2 ≤
      (hilbertPartitionFold π (u-v) j)^2 := by
    intro j
    have he : hilbertFiberRestriction π j (u-v) =
        hilbertFiberRestriction π j u-hilbertFiberRestriction π j v := by ext i; rfl
    have hn := abs_norm_sub_norm_le (hilbertFiberRestriction π j u) (hilbertFiberRestriction π j v)
    rw [← he] at hn
    change (‖hilbertFiberRestriction π j u‖-‖hilbertFiberRestriction π j v‖)^2 ≤
      ‖hilbertFiberRestriction π j (u-v)‖^2
    exact sq_le_sq.mpr (by simpa only [abs_norm] using hn)
  have hSq : ‖hilbertPartitionFold π u-hilbertPartitionFold π v‖^2 ≤ ‖u-v‖^2 := by
    rw [coordinateHilbert_norm_sq,← hilbertPartitionFold_norm π (u-v),coordinateHilbert_norm_sq]
    exact (coordinateHilbert_summable_sq _).tsum_le_tsum hPoint (coordinateHilbert_summable_sq _)
  nlinarith [norm_nonneg (hilbertPartitionFold π u-hilbertPartitionFold π v),norm_nonneg (u-v)]

theorem hilbertPartitionFold_inner (π : ι → κ) (u v : CoordinateHilbert ι) :
    inner ℝ u v ≤ inner ℝ (hilbertPartitionFold π u) (hilbertPartitionFold π v) := by
  have hn := hilbertPartitionFold_dist π u v
  have h₁ := norm_sub_sq_real u v
  have h₂ := norm_sub_sq_real (hilbertPartitionFold π u) (hilbertPartitionFold π v)
  rw [hilbertPartitionFold_norm,hilbertPartitionFold_norm] at h₂
  nlinarith [norm_nonneg (hilbertPartitionFold π u-hilbertPartitionFold π v),norm_nonneg (u-v)]

theorem hilbertPartitionFold_angular (π : ι → κ) (u v : CoordinateHilbert ι) :
    angular (hilbertPartitionFold π u) (hilbertPartitionFold π v) ≤ angular u v :=
  Real.arccos_le_arccos (hilbertPartitionFold_inner π u v)

theorem hilbertPartitionFold_constant_on_support [DecidableEq ι] [DecidableEq κ]
    (π : ι → κ) (F : Finset ι) (c : κ) (u : CoordinateHilbert ι)
    (hu : ∀ i ∉ F, u i = 0) (hπ : ∀ i ∈ F, π i = c) :
    hilbertPartitionFold π u = lp.single 2 c ‖u‖ := by
  have hz : ∀ j, j ≠ c → hilbertPartitionFold π u j = 0 := by
    intro j hj
    change ‖hilbertFiberRestriction π j u‖ = 0
    apply norm_eq_zero.mpr
    ext i
    change u i.val = 0
    by_cases hi : i.val ∈ F
    · exact False.elim (hj (i.property.symm.trans (hπ i.val hi)))
    · exact hu i.val hi
  have he : hilbertPartitionFold π u = lp.single 2 c (hilbertPartitionFold π u c) := by
    ext j
    by_cases hj : j = c
    · subst j; rw [lp.single_apply_self]
    · rw [hz j hj,lp.single_apply_ne _ _ _ hj]
  have hc : hilbertPartitionFold π u c = ‖u‖ := by
    have hn := hilbertPartitionFold_norm π u
    rw [he,lp.norm_single (by norm_num : (0 : ENNReal) < 2),Real.norm_eq_abs] at hn
    change |‖hilbertFiberRestriction π c u‖| = ‖u‖ at hn
    rw [abs_of_nonneg (norm_nonneg _)] at hn
    exact hn
  rw [he,hc]

theorem hilbertPartitionFold_reindex (π π' : ι → κ) (e : ι ≃ ι) (d : κ ≃ κ)
    (hπ : ∀ i, π' (e i) = d (π i)) (u v : CoordinateHilbert ι)
    (huv : ∀ i, v (e i) = u i) (j : κ) :
    hilbertPartitionFold π' v (d j) = hilbertPartitionFold π u j := by
  let ef : {i : ι // π i = j} ≃ {i : ι // π' i = d j} :=
    { toFun := fun i => ⟨e i.val,by rw [hπ,i.property]⟩
      invFun := fun i => ⟨e.symm i.val,by
        apply d.injective
        rw [← hπ,e.apply_symm_apply]
        exact i.property⟩
      left_inv := fun i => Subtype.ext (e.symm_apply_apply i.val)
      right_inv := fun i => Subtype.ext (e.apply_symm_apply i.val) }
  have hsq : ‖hilbertFiberRestriction π' (d j) v‖^2 = ‖hilbertFiberRestriction π j u‖^2 := by
    rw [hilbertFiberRestriction_norm_sq,hilbertFiberRestriction_norm_sq]
    calc
      _ = ∑' i : {i : ι // π i = j}, (v (e i.val))^2 := (ef.tsum_eq _).symm
      _ = _ := tsum_congr (fun i => by rw [huv])
  change ‖hilbertFiberRestriction π' (d j) v‖ = ‖hilbertFiberRestriction π j u‖
  nlinarith [norm_nonneg (hilbertFiberRestriction π' (d j) v),norm_nonneg (hilbertFiberRestriction π j u)]

end Paper28

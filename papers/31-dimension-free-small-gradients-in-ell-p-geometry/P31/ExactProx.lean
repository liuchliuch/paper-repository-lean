import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Data.Fintype.Option
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Real.Sign
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

/-! Exact-real coordinate roots in (5.2) and quadratic history compression (5.3)--(5.4). -/
namespace P31
noncomputable section
open scoped BigOperators

/-- The scalar atom occurring in the paper's p-duality map. -/
def scalarDuality (p t : ℝ) : ℝ := Real.sign t * |t| ^ (p - 1)

lemma scalarDuality_eq_piecewise {p : ℝ} (hp : 1 < p) (t : ℝ) :
    scalarDuality p t = if t ≤ 0 then -(-t) ^ (p - 1) else t ^ (p - 1) := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · simp [scalarDuality, Real.sign_of_neg ht, abs_of_neg ht, ht.le]
  · simp [scalarDuality, Real.zero_rpow (by linarith : p - 1 ≠ 0)]
  · simp [scalarDuality, Real.sign_of_pos ht, abs_of_pos ht, not_le.mpr ht]

lemma continuous_scalarDuality {p : ℝ} (hp : 1 < p) : Continuous (scalarDuality p) := by
  have hr : 0 ≤ p - 1 := by linarith
  change Continuous (fun t => scalarDuality p t)
  simp_rw [scalarDuality_eq_piecewise hp]
  apply Continuous.if_le
    (((Real.continuous_rpow_const hr).comp continuous_neg).neg)
    (Real.continuous_rpow_const hr) continuous_id continuous_const
  intro x hx
  simp only [id_eq] at hx
  simp [hx, Real.zero_rpow (by linarith : p - 1 ≠ 0)]

lemma scalarDuality_of_nonneg {p t : ℝ} (hp : 1 < p) (ht : 0 ≤ t) :
    scalarDuality p t = t ^ (p - 1) := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp [scalarDuality, Real.zero_rpow (by linarith : p - 1 ≠ 0)]
  · simp [scalarDuality, Real.sign_of_pos ht, abs_of_pos ht]

lemma scalarDuality_neg (p t : ℝ) : scalarDuality p (-t) = -scalarDuality p t := by
  simp [scalarDuality, Real.sign_neg]

lemma strictMono_scalarDuality {p : ℝ} (hp : 1 < p) : StrictMono (scalarDuality p) := by
  intro x y hxy
  have hr : 0 < p - 1 := by linarith
  by_cases hx : 0 ≤ x
  · rw [scalarDuality_of_nonneg hp hx, scalarDuality_of_nonneg hp (hx.trans hxy.le)]
    exact Real.rpow_lt_rpow hx hxy hr
  · have hx' : x < 0 := lt_of_not_ge hx
    by_cases hy : y ≤ 0
    · have hnx : 0 ≤ -x := by linarith
      have hny : 0 ≤ -y := by linarith
      have he : scalarDuality p x = -scalarDuality p (-x) := by
        rw [scalarDuality_neg, neg_neg]
      rw [he, scalarDuality_eq_piecewise hp y, if_pos hy,
        scalarDuality_of_nonneg hp hnx]
      exact neg_lt_neg (Real.rpow_lt_rpow hny (by linarith) hr)
    · have hy' : 0 < y := lt_of_not_ge hy
      rw [scalarDuality_eq_piecewise hp x, if_pos hx'.le,
        scalarDuality_of_nonneg hp hy'.le]
      have hpx := Real.rpow_pos_of_pos (neg_pos.mpr hx') (p - 1)
      have hpy := Real.rpow_pos_of_pos hy' (p - 1)
      linarith

/-- The left hand side of equation (5.2), with all centers and coefficients known. -/
def coordinateEquation {ι : Type*} [Fintype ι]
    (p a g : ℝ) (w c : ι → ℝ) (t : ℝ) : ℝ :=
  g + a * ∑ i, w i * scalarDuality p (t - c i)

lemma continuous_coordinateEquation {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 1 < p) (a g : ℝ) (w c : ι → ℝ) :
    Continuous (coordinateEquation p a g w c) := by
  unfold coordinateEquation
  exact continuous_const.add (continuous_const.mul
    (continuous_finset_sum _ (fun i _ => continuous_const.mul
      ((continuous_scalarDuality hp).comp (continuous_id.sub continuous_const)))))

lemma strictMono_coordinateEquation {ι : Type*} [Fintype ι]
    {p a g : ℝ} {w c : ι → ℝ} (hp : 1 < p) (ha : 0 < a)
    (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i, w i) :
    StrictMono (coordinateEquation p a g w c) := by
  intro x y hxy
  obtain ⟨j, _, hj⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hw i)).mp hW
  have hsum : (∑ i, w i * scalarDuality p (x - c i)) <
      ∑ i, w i * scalarDuality p (y - c i) := by
    apply Finset.sum_lt_sum
    · intro i _
      exact mul_le_mul_of_nonneg_left ((strictMono_scalarDuality hp).monotone (by linarith)) (hw i)
    · exact ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left
        (strictMono_scalarDuality hp (by linarith)) hj⟩
  exact add_lt_add_left (mul_lt_mul_of_pos_left hsum ha) g

lemma le_scalarDuality_of_one_le {p t : ℝ} (hp : 2 ≤ p) (ht : 1 ≤ t) :
    t ≤ scalarDuality p t := by
  rw [scalarDuality_of_nonneg (by linarith) (by linarith)]
  simpa only [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_le ht (show (1 : ℝ) ≤ p - 1 by linarith))

lemma scalarDuality_le_of_le_neg_one {p t : ℝ} (hp : 2 ≤ p) (ht : t ≤ -1) :
    scalarDuality p t ≤ t := by
  have h := le_scalarDuality_of_one_le hp (t := -t) (by linarith)
  rw [scalarDuality_neg] at h
  linarith

/-- Finite weighted coordinate equations admit explicit brackets. -/
lemma coordinateEquation_bracket {ι : Type*} [Fintype ι]
    {p a g : ℝ} {w c : ι → ℝ} (hp : 2 ≤ p) (ha : 0 < a)
    (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i, w i) :
    ∃ B : ℝ, 0 ≤ B ∧ coordinateEquation p a g w c (-B) < 0 ∧
      0 < coordinateEquation p a g w c B := by
  classical
  let W := ∑ i, w i
  let C := ∑ i, |c i|
  let L := 1 + |g| / (a * W)
  have hW' : 0 < W := hW
  have haW : 0 < a * W := mul_pos ha hW'
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hL : 1 ≤ L := by
    dsimp [L]
    exact le_add_of_nonneg_right (div_nonneg (abs_nonneg g) haW.le)
  have hc (i : ι) : |c i| ≤ C := by
    exact Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i)
  have hprod : a * W * L = a * W + |g| := by
    dsimp [L]
    rw [mul_add, mul_one, mul_div_cancel₀ _ (ne_of_gt haW)]
  refine ⟨C + L, by linarith, ?_, ?_⟩
  · have hs : (∑ i, w i * scalarDuality p (-(C + L) - c i)) ≤ W * (-L) := by
      calc
        (∑ i, w i * scalarDuality p (-(C + L) - c i)) ≤ ∑ i, w i * (-L) := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_left _ (hw i)
          have hi : -(C + L) - c i ≤ -L := by
            have hi' := neg_abs_le (c i)
            have hi'' := hc i
            linarith
          exact (scalarDuality_le_of_le_neg_one hp (hi.trans (by linarith))).trans hi
        _ = W * (-L) := (Finset.sum_mul ..).symm
    have hs' := mul_le_mul_of_nonneg_left hs ha.le
    dsimp [coordinateEquation]
    nlinarith [le_abs_self g]
  · have hs : W * L ≤ ∑ i, w i * scalarDuality p (C + L - c i) := by
      calc
        W * L = ∑ i, w i * L := Finset.sum_mul ..
        _ ≤ ∑ i, w i * scalarDuality p (C + L - c i) := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_left _ (hw i)
          have hi : L ≤ C + L - c i := by
            have hi' := le_abs_self (c i)
            have hi'' := hc i
            linarith
          exact hi.trans (le_scalarDuality_of_one_le hp (hL.trans hi))
    have hs' := mul_le_mul_of_nonneg_left hs ha.le
    dsimp [coordinateEquation]
    nlinarith [neg_abs_le g]

/-- Equation (5.2): every legal finite coordinate problem has exactly one root. -/
theorem coordinateEquation_existsUnique_zero {ι : Type*} [Fintype ι]
    {p a g : ℝ} {w c : ι → ℝ} (hp : 2 ≤ p) (ha : 0 < a)
    (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i, w i) :
    ∃! t : ℝ, coordinateEquation p a g w c t = 0 := by
  obtain ⟨B, hB, hneg, hpos⟩ := coordinateEquation_bracket hp ha hw hW
  have hcont := continuous_coordinateEquation (by linarith : 1 < p) a g w c
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc (by linarith : -B ≤ B)
    hcont.continuousOn ⟨hneg.le, hpos.le⟩
  refine ⟨t, ht, ?_⟩
  intro y hy
  exact (strictMono_coordinateEquation (by linarith) ha hw hW).injective (hy.trans ht.symm)

/-- The scalar left-hand side is onto the real line, as asserted in Section 5.1. -/
theorem coordinateEquation_surjective {ι : Type*} [Fintype ι]
    {p a g : ℝ} {w c : ι → ℝ} (hp : 2 ≤ p) (ha : 0 < a)
    (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i, w i) :
    Function.Surjective (coordinateEquation p a g w c) := by
  intro y
  obtain ⟨t, ht, _⟩ := coordinateEquation_existsUnique_zero (g := g - y) hp ha hw hW
  refine ⟨t, ?_⟩
  dsimp [coordinateEquation] at ht ⊢
  linarith

lemma scalarDuality_eq_mul_abs {p : ℝ} (_hp : 2 ≤ p) (t : ℝ) :
    scalarDuality p t = |t| ^ (p - 2) * t := by
  by_cases ht : t = 0
  · simp [ht, scalarDuality]
  have hpow : |t| ^ (p - 1) = |t| ^ (p - 2) * |t| := by
    calc
      |t| ^ (p - 1) = |t| ^ ((p - 2) + 1) := by congr 1; ring
      _ = |t| ^ (p - 2) * |t| := by
        rw [Real.rpow_add (abs_pos.mpr ht), Real.rpow_one]
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · rw [scalarDuality, Real.sign_of_neg hneg, hpow, abs_of_neg hneg]
    ring
  · rw [scalarDuality, Real.sign_of_pos hpos, hpow, abs_of_pos hpos]
    ring

/-- The known scalar objective whose stationarity equation is (5.2). -/
def coordinateObjective {ι : Type*} [Fintype ι]
    (p a g : ℝ) (w c : ι → ℝ) (t : ℝ) : ℝ :=
  g * t + (a / p) * ∑ i, w i * |t - c i| ^ p

lemma coordinateObjective_hasDerivAt {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 2 ≤ p) (a g : ℝ) (w c : ι → ℝ) (t : ℝ) :
    HasDerivAt (coordinateObjective p a g w c)
      (coordinateEquation p a g w c t) t := by
  have hi (i : ι) : HasDerivAt (fun x : ℝ => w i * |x - c i| ^ p)
      (w i * (p * scalarDuality p (t - c i))) t := by
    have h := ((hasDerivAt_abs_rpow (t - c i) (by linarith : 1 < p)).comp t
      ((hasDerivAt_id t).sub_const (c i))).const_mul (w i)
    convert h using 1
    rw [scalarDuality_eq_mul_abs hp]
    ring
  have hs := HasDerivAt.sum (u := Finset.univ) (fun i _ => hi i)
  have h := ((hasDerivAt_id t).const_mul g).add (hs.const_mul (a / p))
  simp only [mul_one] at h
  convert h using 1
  · ext x
    simp [coordinateObjective]
  · dsimp [coordinateEquation]
    have hp0 : p ≠ 0 := by linarith
    calc
      g + a * ∑ i, w i * scalarDuality p (t - c i) =
          g + (a / p) * (p * ∑ i, w i * scalarDuality p (t - c i)) := by field_simp
      _ = _ := by
        congr 1
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring

/-- A root of (5.2) is the unique global minimum of the actual scalar p-power objective. -/
theorem coordinate_root_unique_minimizer {ι : Type*} [Fintype ι]
    {p a g z : ℝ} {w c : ι → ℝ} (hp : 2 ≤ p) (ha : 0 < a)
    (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i, w i)
    (hz : coordinateEquation p a g w c z = 0) :
    ∀ x : ℝ, x ≠ z → coordinateObjective p a g w c z <
      coordinateObjective p a g w c x := by
  have hdiff : Differentiable ℝ (coordinateObjective p a g w c) :=
    fun x => (coordinateObjective_hasDerivAt hp a g w c x).differentiableAt
  have hcont := hdiff.continuous
  have hmono := strictMono_coordinateEquation (p := p) (g := g) (c := c) (by linarith) ha hw hW
  have hright : StrictMonoOn (coordinateObjective p a g w c) (Set.Ici z) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici z) hcont.continuousOn
    intro x hx
    rw [interior_Ici] at hx
    rw [(coordinateObjective_hasDerivAt hp a g w c x).deriv]
    rw [← hz]
    exact hmono hx
  have hleft : StrictAntiOn (coordinateObjective p a g w c) (Set.Iic z) := by
    apply strictAntiOn_of_deriv_neg (convex_Iic z) hcont.continuousOn
    intro x hx
    rw [interior_Iic] at hx
    rw [(coordinateObjective_hasDerivAt hp a g w c x).deriv]
    rw [← hz]
    exact hmono hx
  intro x hx
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · exact hleft hlt.le (Set.mem_Iic.mpr le_rfl) hlt
  · exact hright (Set.mem_Ici.mpr le_rfl) hgt.le hgt

/-- The exact-real scalar composite minimization exists and is unique. -/
theorem coordinateObjective_existsUnique_minimizer {ι : Type*} [Fintype ι]
    {p a g : ℝ} {w c : ι → ℝ} (hp : 2 ≤ p) (ha : 0 < a)
    (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i, w i) :
    ∃! z : ℝ, ∀ x : ℝ, coordinateObjective p a g w c z ≤
      coordinateObjective p a g w c x := by
  obtain ⟨z, hz, _⟩ := coordinateEquation_existsUnique_zero hp ha hw hW
  have hstrict := coordinate_root_unique_minimizer hp ha hw hW hz
  refine ⟨z, ?_, ?_⟩
  · intro x
    by_cases hx : x = z
    · exact hx ▸ le_rfl
    · exact (hstrict x hx).le
  · intro y hy
    by_contra hne
    exact (not_lt_of_ge (hy z)) (hstrict y hne)

/-- Deterministic exact-real root map from the known scalar transcript. -/
def coordinateRoot {ι : Type*} [Fintype ι]
    (p a g : ℝ) (w c : ι → ℝ) (hp : 2 ≤ p) (ha : 0 < a)
    (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i, w i) : ℝ :=
  Classical.choose (coordinateEquation_existsUnique_zero (g := g) (c := c) hp ha hw hW)

lemma coordinateRoot_equation {ι : Type*} [Fintype ι]
    (p a g : ℝ) (w c : ι → ℝ) (hp : 2 ≤ p) (ha : 0 < a)
    (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i, w i) :
    coordinateEquation p a g w c (coordinateRoot p a g w c hp ha hw hW) = 0 :=
  (Classical.choose_spec (coordinateEquation_existsUnique_zero (g := g) (c := c) hp ha hw hW)).1

/-- The vector objective is the sum of its actual coordinate objectives. -/
def vectorCompositeObjective {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p a : ℝ) (g : κ → ℝ) (w : ι → ℝ) (c : ι → κ → ℝ) (x : κ → ℝ) : ℝ :=
  ∑ j, coordinateObjective p a (g j) w (fun i => c i j) (x j)

lemma vectorCompositeObjective_expansion {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p a : ℝ) (g : κ → ℝ) (w : ι → ℝ) (c : ι → κ → ℝ) (x : κ → ℝ) :
    vectorCompositeObjective p a g w c x =
      (∑ j, g j * x j) + (a / p) * ∑ i, w i * ∑ j, |x j - c i j| ^ p := by
  simp only [vectorCompositeObjective, coordinateObjective, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  congr 2
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

/-- The exact finite vector prox, obtained from its unique coordinate roots. -/
def vectorProx {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p a : ℝ) (g : κ → ℝ) (w : ι → ℝ) (c : ι → κ → ℝ)
    (hp : 2 ≤ p) (ha : 0 < a) (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i, w i) : κ → ℝ :=
  fun j => coordinateRoot p a (g j) w (fun i => c i j) hp ha hw hW

lemma vectorProx_strict_minimizer {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p a : ℝ) (g : κ → ℝ) (w : ι → ℝ) (c : ι → κ → ℝ)
    (hp : 2 ≤ p) (ha : 0 < a) (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i, w i)
    (x : κ → ℝ) (hx : x ≠ vectorProx p a g w c hp ha hw hW) :
    vectorCompositeObjective p a g w c (vectorProx p a g w c hp ha hw hW) <
      vectorCompositeObjective p a g w c x := by
  have hstrict (j : κ) : x j ≠ vectorProx p a g w c hp ha hw hW j →
      coordinateObjective p a (g j) w (fun i => c i j)
        (vectorProx p a g w c hp ha hw hW j) <
      coordinateObjective p a (g j) w (fun i => c i j) (x j) :=
    coordinate_root_unique_minimizer hp ha hw hW
      (coordinateRoot_equation p a (g j) w (fun i => c i j) hp ha hw hW) (x j)
  have hle (j : κ) : coordinateObjective p a (g j) w (fun i => c i j)
      (vectorProx p a g w c hp ha hw hW j) ≤
      coordinateObjective p a (g j) w (fun i => c i j) (x j) := by
    by_cases he : x j = vectorProx p a g w c hp ha hw hW j
    · rw [he]
    · exact (hstrict j he).le
  have hex : ∃ j, x j ≠ vectorProx p a g w c hp ha hw hW j :=
    not_forall.mp (fun h => hx (funext h))
  obtain ⟨j, hj⟩ := hex
  exact Finset.sum_lt_sum (fun j _ => hle j) ⟨j, Finset.mem_univ j, hstrict j hj⟩

/-- Equation (5.1) in finite vector coordinates has exactly the explicit root map as minimizer. -/
theorem vectorProx_minimizer_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p a : ℝ) (g : κ → ℝ) (w : ι → ℝ) (c : ι → κ → ℝ)
    (hp : 2 ≤ p) (ha : 0 < a) (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i, w i)
    (z : κ → ℝ) :
    (∀ x, vectorCompositeObjective p a g w c z ≤ vectorCompositeObjective p a g w c x) ↔
      z = vectorProx p a g w c hp ha hw hW := by
  constructor
  · intro hz
    by_contra hne
    exact (not_lt_of_ge (hz _)) (vectorProx_strict_minimizer p a g w c hp ha hw hW z hne)
  · rintro rfl x
    by_cases he : x = vectorProx p a g w c hp ha hw hW
    · rw [he]
    · exact (vectorProx_strict_minimizer p a g w c hp ha hw hW x he).le

/-- Unique existence for the finite vector internal minimization. -/
theorem vectorComposite_existsUnique_minimizer {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p a : ℝ) (g : κ → ℝ) (w : ι → ℝ) (c : ι → κ → ℝ)
    (hp : 2 ≤ p) (ha : 0 < a) (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i, w i) :
    ∃! z : κ → ℝ, ∀ x, vectorCompositeObjective p a g w c z ≤
      vectorCompositeObjective p a g w c x := by
  refine ⟨vectorProx p a g w c hp ha hw hW, ?_, ?_⟩
  · exact (vectorProx_minimizer_iff p a g w c hp ha hw hW _).mpr rfl
  · intro z hz
    exact (vectorProx_minimizer_iff p a g w c hp ha hw hW z).mp hz

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The finite history's total weight. -/
def historyWeight {ι : Type*} [Fintype ι] (w : ι → ℝ) : ℝ := ∑ i, w i

/-- Weighted first moment; no dimension-specific coordinates are used. -/
def historyMoment {ι : Type*} [Fintype ι] (w : ι → ℝ) (c : ι → E) : E := ∑ i, w i • c i

/-- The barycenter stored by the Hilbert implementation. -/
def historyCenter {ι : Type*} [Fintype ι] (w : ι → ℝ) (c : ι → E) : E :=
  (historyWeight w)⁻¹ • historyMoment w c

lemma historyCenter_moment {ι : Type*} [Fintype ι] (w : ι → ℝ) (c : ι → E)
    (hW : historyWeight w ≠ 0) :
    historyWeight w • historyCenter w c = historyMoment w c := by
  simp [historyCenter, smul_smul, hW]

lemma weighted_norm_sub_expansion {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → E) (x : E) :
    (∑ i, w i * ‖x - c i‖ ^ 2) =
      historyWeight w * ‖x‖ ^ 2 - 2 * inner ℝ x (historyMoment w c) +
        ∑ i, w i * ‖c i‖ ^ 2 := by
  calc
    (∑ i, w i * ‖x - c i‖ ^ 2) =
        ∑ i, (w i * ‖x‖ ^ 2 - 2 * (w i * inner ℝ x (c i)) + w i * ‖c i‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_sub_sq_real]
      ring
    _ = _ := by
      simp only [historyWeight, historyMoment, inner_sum, inner_smul_right,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]

/-- Exact history compression, equation (5.3), including the x-independent constant. -/
theorem quadratic_history_compression {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → E) (hW : historyWeight w ≠ 0) (x : E) :
    (1 / 2 : ℝ) * (∑ i, w i * ‖x - c i‖ ^ 2) =
      (historyWeight w / 2) * ‖x - historyCenter w c‖ ^ 2 +
      ((1 / 2 : ℝ) * (∑ i, w i * ‖c i‖ ^ 2) -
        (historyWeight w / 2) * ‖historyCenter w c‖ ^ 2) := by
  rw [weighted_norm_sub_expansion]
  rw [← historyCenter_moment w c hW, inner_smul_right, norm_sub_sq_real]
  ring

/-- Streaming update of the weighted center in equation (5.3). -/
theorem history_center_update (W α : ℝ) (center next : E) (h : W + α ≠ 0) :
    (W + α) • ((W + α)⁻¹ • (W • center + α • next)) =
      W • center + α • next := by
  simp [smul_smul, h]

/-- Appending one history atom gives precisely the streaming barycenter recurrence of (5.3). -/
theorem historyCenter_append {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → E) (α : ℝ) (next : E) (hW : historyWeight w ≠ 0) :
    historyCenter (fun i : Option ι => i.elim α w) (fun i => i.elim next c) =
      (historyWeight w + α)⁻¹ • (historyWeight w • historyCenter w c + α • next) := by
  have hweight : historyWeight (fun i : Option ι => i.elim α w) = historyWeight w + α := by
    simp [historyWeight, univ_option, Finset.sum_insertNone, add_comm]
  have hmoment : historyMoment (fun i : Option ι => i.elim α w) (fun i => i.elim next c) =
      historyMoment w c + α • next := by
    simp [historyMoment, univ_option, Finset.sum_insertNone, add_comm]
  change (historyWeight (fun i : Option ι => i.elim α w))⁻¹ •
    historyMoment (fun i : Option ι => i.elim α w) (fun i => i.elim next c) = _
  rw [hweight, hmoment, historyCenter_moment w c hW]

/-- The known quadratic objective at the Hilbert endpoint of (5.1). -/
def hilbertObjective (g : E) (b m : ℝ) (u v x : E) : ℝ :=
  inner ℝ g x + (b / 2) * ‖x - u‖ ^ 2 + (m / 2) * ‖x - v‖ ^ 2

/-- Closed-form point in equation (5.4), with b = A σ. -/
def hilbertProx (g : E) (b m : ℝ) (u v : E) : E :=
  (b + m)⁻¹ • (b • u + m • v - g)

lemma hilbertProx_stationary (g : E) (b m : ℝ) (u v : E) (h : b + m ≠ 0) :
    (b + m) • hilbertProx g b m u v = b • u + m • v - g := by
  simp [hilbertProx, smul_smul, h]

lemma hilbert_quadratic_completion (g : E) (b m : ℝ) (u v z : E)
    (hz : (b + m) • z = b • u + m • v - g) (x : E) :
    hilbertObjective g b m u v x = hilbertObjective g b m u v z +
      ((b + m) / 2) * ‖x - z‖ ^ 2 := by
  have hx := congrArg (fun y : E => inner ℝ y x) hz
  have hzz := congrArg (fun y : E => inner ℝ y z) hz
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at hx hzz
  simp only [hilbertObjective, norm_sub_sq_real]
  rw [real_inner_comm u x, real_inner_comm v x, real_inner_comm z x,
    real_inner_comm u z, real_inner_comm v z]
  nlinarith

/-- The point displayed in (5.4) is the unique global minimizer. -/
theorem hilbertProx_unique_minimizer (g : E) (b m : ℝ) (u v : E)
    (h : 0 < b + m) :
    (∀ x, hilbertObjective g b m u v (hilbertProx g b m u v) ≤
      hilbertObjective g b m u v x) ∧
    (∀ x, hilbertObjective g b m u v x =
      hilbertObjective g b m u v (hilbertProx g b m u v) →
      x = hilbertProx g b m u v) := by
  have hz := hilbertProx_stationary g b m u v (ne_of_gt h)
  constructor
  · intro x
    rw [hilbert_quadratic_completion g b m u v _ hz x]
    exact le_add_of_nonneg_right (mul_nonneg (by linarith) (sq_nonneg _))
  · intro x hx
    rw [hilbert_quadratic_completion g b m u v _ hz x] at hx
    have hn : ‖x - hilbertProx g b m u v‖ ^ 2 = 0 := by nlinarith
    have he : x - hilbertProx g b m u v = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    exact sub_eq_zero.mp he

end Hilbert
end
end P31

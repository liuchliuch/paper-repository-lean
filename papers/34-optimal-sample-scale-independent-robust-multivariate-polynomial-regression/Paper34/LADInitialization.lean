import Paper34.LAD
import Paper34.NormingInterface
import Paper34.GridGeometry
import Paper34.NativeNorms
import Mathlib.Tactic.Module

/-! The good-grid LAD argument. The norming interface is an internal dependency
produced by the arbitrary-representative proof, not an external theorem input. -/
namespace Paper34
open BigOperators
noncomputable section

theorem l1Norm_nonneg {n d : ℕ} (q : PolynomialSpace n d) : 0 ≤ l1Norm q :=
  MeasureTheory.integral_nonneg (fun _ => abs_nonneg _)

def locationMultiset {ι : Type*} {n : ℕ} (T : Finset ι) (X : ι → Point n) : Multiset (Point n) :=
  T.val.map X

theorem locationMultiset_average {ι : Type*} {n : ℕ} (T : Finset ι)
    (X : ι → Point n) (f : Point n → ℝ) :
    multisetAverage (locationMultiset T X) f = (∑ i ∈ T, f (X i))/(T.card : ℝ) := by
  simp only [multisetAverage, locationMultiset, Multiset.map_map, Multiset.card_map]
  rfl

theorem fraction_times_average {ι : Type*} (T : Finset ι) (f : ι → ℝ) (N : ℝ) :
    N⁻¹ * (∑ i ∈ T, f i) = ((T.card : ℝ)/N)*((∑ i ∈ T, f i)/(T.card : ℝ)) := by
  by_cases hT : T.card = 0
  · have h := Finset.card_eq_zero.mp hT
    simp [h]
  · have hT' : (T.card : ℝ) ≠ 0 := by exact_mod_cast hT
    simp only [div_eq_mul_inv]
    field_simp

/-- A finite sample grid with actual observed locations and global good indices. -/
structure GoodSampleGrid (n m : ℕ) (ι : Type*) where
  samples : CellIndex n m → Finset ι
  location : ι → Point n
  inlier : ι → Prop
  inlier_decidable : DecidablePred inlier
  nonempty : ∀ j, (samples j).Nonempty
  inside : ∀ j, ∀ i ∈ samples j, location i ∈ closedCell j

instance {n m : ℕ} {ι : Type*} (D : GoodSampleGrid n m ι) : DecidablePred D.inlier :=
  D.inlier_decidable

def GoodSampleGrid.good {n m : ℕ} {ι : Type*} (D : GoodSampleGrid n m ι)
    (j : CellIndex n m) : Finset ι := (D.samples j).filter D.inlier

def GoodSampleGrid.bad {n m : ℕ} {ι : Type*} (D : GoodSampleGrid n m ι)
    (j : CellIndex n m) : Finset ι := (D.samples j).filter (fun i => ¬D.inlier i)

def GoodSampleGrid.GoodAt {n m : ℕ} {ι : Type*} (D : GoodSampleGrid n m ι)
    (rho : ℝ) : Prop :=
  ∀ j, ((D.bad j).card : ℝ)/((D.samples j).card : ℝ) ≤ alpha rho

theorem GoodSampleGrid.fraction_sum {n m : ℕ} {ι : Type*} (D : GoodSampleGrid n m ι)
    (j : CellIndex n m) :
    ((D.good j).card : ℝ)/((D.samples j).card : ℝ) +
      ((D.bad j).card : ℝ)/((D.samples j).card : ℝ) = 1 := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card (s := D.samples j) D.inlier
  have hN : ((D.samples j).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (D.nonempty j)
  rw [← add_div]
  have hr : ((D.good j).card : ℝ)+((D.bad j).card : ℝ) = ((D.samples j).card : ℝ) := by
    exact_mod_cast h
  rw [hr, div_self hN]

theorem GoodSampleGrid.good_nonempty {n m : ℕ} {ι : Type*}
    (D : GoodSampleGrid n m ι) {rho : ℝ} (hr : rho < 1/2) (hgood : D.GoodAt rho)
    (j : CellIndex n m) : (D.good j).Nonempty := by
  have ha : alpha rho < 1 := by unfold alpha; linarith
  have hh := D.fraction_sum j
  have hb := hgood j
  have hc : (D.good j).card ≠ 0 := by
    intro hz
    simp only [hz, Nat.cast_zero, zero_div, zero_add] at hh
    linarith
  exact Finset.card_ne_zero.mp hc

theorem GoodSampleGrid.good_strict_majority {n m : ℕ} {ι : Type*}
    (D : GoodSampleGrid n m ι) {rho : ℝ} (hr : rho < 1/2) (hgood : D.GoodAt rho)
    (j : CellIndex n m) : (D.samples j).card < 2*(D.good j).card := by
  have hN : (0 : ℝ) < (D.samples j).card := by exact_mod_cast Finset.card_pos.mpr (D.nonempty j)
  have hb := (div_le_iff₀ hN).mp (hgood j)
  have hh := Finset.filter_card_add_filter_neg_card_eq_card (s := D.samples j) D.inlier
  have hh' : ((D.good j).card : ℝ)+((D.bad j).card : ℝ) = (D.samples j).card := by exact_mod_cast hh
  have ha : alpha rho < 1/2 := by unfold alpha; linarith
  have hmul := mul_lt_mul_of_pos_right ha hN
  have hx : ((D.samples j).card : ℝ) < 2*((D.good j).card : ℝ) := by linarith
  exact_mod_cast hx

def GoodSampleGrid.goodFamily {n m : ℕ} {ι : Type*} (D : GoodSampleGrid n m ι)
    (j : CellIndex n m) : Multiset (Point n) := locationMultiset (D.good j) D.location

def GoodSampleGrid.dummyPoint {n m : ℕ} {ι : Type*} (D : GoodSampleGrid n m ι)
    (j : CellIndex n m) : Point n := D.location (D.nonempty j).choose

def GoodSampleGrid.badFamily {n m : ℕ} {ι : Type*} (D : GoodSampleGrid n m ι)
    (j : CellIndex n m) : Multiset (Point n) :=
  if (D.bad j).Nonempty then locationMultiset (D.bad j) D.location else {D.dummyPoint j}

theorem GoodSampleGrid.goodFamily_nonempty {n m : ℕ} {ι : Type*}
    (D : GoodSampleGrid n m ι) {rho : ℝ} (hr : rho < 1/2) (hgood : D.GoodAt rho)
    (j : CellIndex n m) : D.goodFamily j ≠ 0 := by
  intro hz
  have hc := congrArg Multiset.card hz
  have hT := Finset.card_ne_zero.mpr (D.good_nonempty hr hgood j)
  apply hT
  simpa [goodFamily, locationMultiset] using hc

theorem GoodSampleGrid.goodFamily_inside {n m : ℕ} {ι : Type*}
    (D : GoodSampleGrid n m ι) (j : CellIndex n m) (x : Point n)
    (hx : x ∈ D.goodFamily j) : x ∈ closedCell j := by
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
  exact D.inside j i (Finset.mem_filter.mp hi).1

theorem GoodSampleGrid.badFamily_nonempty {n m : ℕ} {ι : Type*}
    (D : GoodSampleGrid n m ι) (j : CellIndex n m) : D.badFamily j ≠ 0 := by
  unfold badFamily
  split_ifs with h
  · intro hz
    have hc := congrArg Multiset.card hz
    apply Finset.card_ne_zero.mpr h
    simpa [locationMultiset] using hc
  · simp

theorem GoodSampleGrid.badFamily_inside {n m : ℕ} {ι : Type*}
    (D : GoodSampleGrid n m ι) (j : CellIndex n m) (x : Point n)
    (hx : x ∈ D.badFamily j) : x ∈ closedCell j := by
  unfold badFamily at hx
  split_ifs at hx with h
  · obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
    exact D.inside j i (Finset.mem_filter.mp hi).1
  · have heq : x = D.dummyPoint j := by simpa using hx
    rw [heq]
    exact D.inside j _ (D.nonempty j).choose_spec

theorem multisetAverage_abs_nonneg {E : Type*} (A : Multiset E) (f : E → ℝ) :
    0 ≤ multisetAverage A (fun x => |f x|) := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Multiset.sum_nonneg
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
  exact abs_nonneg _

def GoodSampleGrid.subsetMass {n m d : ℕ} {ι : Type*} (D : GoodSampleGrid n m ι)
    (T : CellIndex n m → Finset ι) (q : PolynomialSpace n d) : ℝ :=
  ((m : ℝ)^n)⁻¹ * ∑ j, ((D.samples j).card : ℝ)⁻¹ *
    ∑ i ∈ T j, |polyEval q (D.location i)|

theorem GoodSampleGrid.goodMass_lower {n m d : ℕ} {ι : Type*}
    (D : GoodSampleGrid n m ι) (q : PolynomialSpace n d) {rho : ℝ}
    (hgood : D.GoodAt rho) :
    (1-alpha rho)*multisetPhi D.goodFamily q ≤ D.subsetMass D.good q := by
  unfold multisetPhi subsetMass
  rw [← mul_assoc, mul_comm (1-alpha rho), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hfrac : 1-alpha rho ≤ ((D.good j).card : ℝ)/((D.samples j).card : ℝ) := by
    have hs := D.fraction_sum j
    have hb := hgood j
    linarith
  have hmean := multisetAverage_abs_nonneg (D.goodFamily j) (polyEval q)
  have hmul := mul_le_mul_of_nonneg_right hfrac hmean
  rw [goodFamily, locationMultiset_average] at hmul
  rw [fraction_times_average]
  simpa only [goodFamily, locationMultiset_average] using hmul

theorem GoodSampleGrid.badMass_upper {n m d : ℕ} {ι : Type*}
    (D : GoodSampleGrid n m ι) (q : PolynomialSpace n d) {rho : ℝ}
    (ha : 0 ≤ alpha rho) (hgood : D.GoodAt rho) :
    D.subsetMass D.bad q ≤ alpha rho*multisetPhi D.badFamily q := by
  unfold multisetPhi subsetMass
  rw [← mul_assoc, mul_comm (alpha rho), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hT : (D.bad j).Nonempty
  · have hmean := multisetAverage_abs_nonneg (D.badFamily j) (polyEval q)
    have hmul := mul_le_mul_of_nonneg_right (hgood j) hmean
    rw [badFamily, if_pos hT, locationMultiset_average] at hmul
    rw [fraction_times_average]
    simpa only [badFamily, if_pos hT, locationMultiset_average] using hmul
  · have he : D.bad j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    simp only [he, Finset.sum_empty, mul_zero]
    exact mul_nonneg ha (multisetAverage_abs_nonneg (D.badFamily j) (polyEval q))

theorem GoodSampleGrid.signedMass_eq {n m d : ℕ} {ι : Type*}
    (D : GoodSampleGrid n m ι) (q : PolynomialSpace n d) :
    weightedAverage D.samples (fun _ i =>
      if D.inlier i then |polyEval q (D.location i)| else -|polyEval q (D.location i)|) =
      D.subsetMass D.good q-D.subsetMass D.bad q := by
  have hg : D.subsetMass D.good q = weightedAverage D.samples
      (fun _ i => if D.inlier i then |polyEval q (D.location i)| else 0) := by
    simp [subsetMass, weightedAverage, good, CellIndex, Finset.sum_filter]
  have hb : D.subsetMass D.bad q = weightedAverage D.samples
      (fun _ i => if ¬D.inlier i then |polyEval q (D.location i)| else 0) := by
    simp [subsetMass, weightedAverage, bad, CellIndex, Finset.sum_filter]
  rw [hg, hb, ← weightedAverage_sub]
  congr 1
  funext j i
  by_cases hi : D.inlier i <;> simp [hi]

/-- The full source LAD lower bound, using the internally proved norming
module and real cellwise inlier/outlier fractions, for every error polynomial. -/
theorem coercive_lad_lower {n m d : ℕ} [NeZero m] {ι : Type*}
    (D : GoodSampleGrid n m ι) (Y : ι → ℝ) (p e : PolynomialSpace n d)
    {rho sigma : ℝ} (hr0 : 0 ≤ rho) (hr : rho < 1/2) (hs : 0 ≤ sigma)
    (hgood : D.GoodAt rho)
    (hnoise : ∀ j, ∀ i ∈ D.samples j, D.inlier i → |polyEval p (D.location i)-Y i| ≤ sigma)
    (hnorm : MultisetNorming n d m (zeta rho)) :
    gap rho/2*l1Norm e-2*sigma ≤
      weightedLAD D.samples D.location Y (p+e)-weightedLAD D.samples D.location Y p := by
  have ha0 : 0 ≤ alpha rho := by unfold alpha; linarith
  have ha1 : 0 ≤ 1-alpha rho := by unfold alpha; linarith
  have hgn := (hnorm e D.goodFamily (D.goodFamily_nonempty hr hgood) D.goodFamily_inside).1
  have hbn := (hnorm e D.badFamily D.badFamily_nonempty D.badFamily_inside).2
  have hG := (mul_le_mul_of_nonneg_left hgn ha1).trans (D.goodMass_lower e hgood)
  have hB := (D.badMass_upper e ha0 hgood).trans (mul_le_mul_of_nonneg_left hbn ha0)
  have hraw := lad_signed_mass_lower D.samples D.nonempty D.location Y p e D.inlier hs hnoise
  rw [D.signedMass_eq e] at hraw
  exact lad_coefficient_lower_of_mass_bounds hraw (by simpa only [mul_assoc] using hG)
    (by simpa only [mul_assoc] using hB)

/-- The actual source objective tends to infinity away from compact sets. -/
theorem weightedLAD_coercive {n m d : ℕ} [NeZero m] {ι : Type*}
    (D : GoodSampleGrid n m ι) (Y : ι → ℝ) (p : PolynomialSpace n d)
    {rho sigma : ℝ} (hr0 : 0 ≤ rho) (hr : rho < 1/2) (hs : 0 ≤ sigma)
    (hgood : D.GoodAt rho)
    (hnoise : ∀ j, ∀ i ∈ D.samples j, D.inlier i → |polyEval p (D.location i)-Y i| ≤ sigma)
    (hnorm : MultisetNorming n d m (zeta rho)) (hnik : L1ToSup n d) :
    Filter.Tendsto (weightedLAD D.samples D.location Y)
      (Filter.cocompact (PolynomialSpace n d)) Filter.atTop := by
  let K : ℝ := (2*(d : ℝ)+1)^n
  let c : ℝ := gap rho/(2*K)
  have hK : 0 < K := by dsimp [K]; positivity
  have hg : 0 < gap rho := by unfold gap; linarith
  have hc : 0 < c := div_pos hg (mul_pos (by norm_num) hK)
  have hlower : ∀ q : PolynomialSpace n d,
      c*‖q-p‖-(2*sigma-weightedLAD D.samples D.location Y p) ≤
        weightedLAD D.samples D.location Y q := by
    intro q
    have hraw := coercive_lad_lower D Y p (q-p) hr0 hr hs hgood hnoise hnorm
    have heq : p+(q-p) = q := by module
    rw [heq] at hraw
    have hscaled := mul_le_mul_of_nonneg_left (hnik (q-p)) hc.le
    rw [← norm_eq_supNorm] at hscaled
    have hid : c*(K*l1Norm (q-p)) = gap rho/2*l1Norm (q-p) := by
      dsimp [c]
      field_simp
      <;> ring
    change c*‖q-p‖ ≤ c*(K*l1Norm (q-p)) at hscaled
    rw [hid] at hscaled
    linarith
  have hlower' : ∀ q : PolynomialSpace n d,
      c*‖q‖-((2*sigma-weightedLAD D.samples D.location Y p)+c*‖p‖) ≤
        weightedLAD D.samples D.location Y q := by
    intro q
    have htri : ‖q‖ ≤ ‖q-p‖+‖p‖ := by
      simpa only [sub_add_cancel] using norm_add_le (q-p) p
    have hh := mul_le_mul_of_nonneg_left htri hc.le
    linarith [hlower q]
  apply Filter.tendsto_atTop_mono hlower'
  simpa only [sub_eq_add_neg] using
    Filter.tendsto_atTop_add_const_right (Filter.cocompact (PolynomialSpace n d))
      (-((2*sigma-weightedLAD D.samples D.location Y p)+c*‖p‖))
      (Filter.Tendsto.const_mul_atTop hc tendsto_norm_cocompact_atTop)

/-- Proposition 4.1: genuine minimizer existence for the source weighted LAD. -/
theorem weightedLAD_attains_minimum {n m d : ℕ} [NeZero m] {ι : Type*}
    (D : GoodSampleGrid n m ι) (Y : ι → ℝ) (p : PolynomialSpace n d)
    {rho sigma : ℝ} (hr0 : 0 ≤ rho) (hr : rho < 1/2) (hs : 0 ≤ sigma)
    (hgood : D.GoodAt rho)
    (hnoise : ∀ j, ∀ i ∈ D.samples j, D.inlier i → |polyEval p (D.location i)-Y i| ≤ sigma)
    (hnorm : MultisetNorming n d m (zeta rho)) (hnik : L1ToSup n d) :
    ∃ q : PolynomialSpace n d, ∀ r : PolynomialSpace n d,
      weightedLAD D.samples D.location Y q ≤ weightedLAD D.samples D.location Y r :=
  (continuous_weightedLAD D.samples D.location Y).exists_forall_le
    (weightedLAD_coercive D Y p hr0 hr hs hgood hnoise hnorm hnik)

/-- Every minimizer satisfies both (4.2) and (4.3); zero noise is included. -/
theorem lad_initializer_error {n m d : ℕ} [NeZero m] {ι : Type*}
    (D : GoodSampleGrid n m ι) (Y : ι → ℝ) (p q : PolynomialSpace n d)
    {rho sigma : ℝ} (hr0 : 0 ≤ rho) (hr : rho < 1/2) (hs : 0 ≤ sigma)
    (hgood : D.GoodAt rho)
    (hnoise : ∀ j, ∀ i ∈ D.samples j, D.inlier i → |polyEval p (D.location i)-Y i| ≤ sigma)
    (hnorm : MultisetNorming n d m (zeta rho)) (hnik : L1ToSup n d)
    (hmin : ∀ r : PolynomialSpace n d,
      weightedLAD D.samples D.location Y q ≤ weightedLAD D.samples D.location Y r) :
    l1Norm (q-p) ≤ 4*sigma/gap rho ∧
      supNorm (q-p) ≤ initializationFactor n d rho*sigma := by
  have hg : 0 < gap rho := by unfold gap; linarith
  have hraw := coercive_lad_lower D Y p (q-p) hr0 hr hs hgood hnoise hnorm
  have heq : p+(q-p) = q := by module
  rw [heq] at hraw
  have hL := initializer_l1_of_lad_lower D.samples D.location Y p q hg hraw hmin
  refine ⟨hL, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hL
    (by positivity : 0 ≤ (2*(d : ℝ)+1)^n)
  calc
    supNorm (q-p) ≤ (2*(d : ℝ)+1)^n*l1Norm (q-p) := hnik (q-p)
    _ ≤ (2*(d : ℝ)+1)^n*(4*sigma/gap rho) := hmul
    _ = initializationFactor n d rho*sigma := by unfold initializationFactor; ring

/-- At zero noise every minimizer equals the original polynomial identically. -/
theorem lad_initializer_exact {n m d : ℕ} [NeZero m] {ι : Type*}
    (D : GoodSampleGrid n m ι) (Y : ι → ℝ) (p q : PolynomialSpace n d)
    {rho : ℝ} (hr0 : 0 ≤ rho) (hr : rho < 1/2) (hgood : D.GoodAt rho)
    (hnoise : ∀ j, ∀ i ∈ D.samples j, D.inlier i → polyEval p (D.location i) = Y i)
    (hnorm : MultisetNorming n d m (zeta rho)) (hnik : L1ToSup n d)
    (hmin : ∀ r : PolynomialSpace n d,
      weightedLAD D.samples D.location Y q ≤ weightedLAD D.samples D.location Y r) : q = p := by
  have he := (lad_initializer_error D Y p q hr0 hr (le_refl 0) hgood
    (fun j i hi hg => by simp [hnoise j i hi hg]) hnorm hnik hmin).2
  simp only [mul_zero] at he
  rw [← norm_eq_supNorm] at he
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm he (norm_nonneg _)))

end
end Paper34

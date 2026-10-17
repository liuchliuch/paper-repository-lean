import Paper37.KnownSupportLaw
import Paper37.BackwardRender

/-! The bounded-support add-one hazard predictor as an actual function of the
observed binary word, with exact recovery on the standard cycle construction. -/
noncomputable section
namespace Paper37.KnownSupportWord
open scoped BigOperators
open Paper37.Renewal Paper37.Prediction Paper37.Compression Paper37.Compression.Distribution
open Paper37.IIDAddOne Paper37.KnownSupport Paper37.KnownSupportRisk Paper37.BackwardRender

/-- Newest-first gap indices for the finite iid product sample. -/
def sampleIndices {B : ℕ} : (k : ℕ) → Sample (Fin B) k → List ℕ
  | 0,_ => []
  | k+1,(s,a) => a.val::sampleIndices k s

@[simp] lemma sampleIndices_length {B : ℕ} (k : ℕ) (s : Sample (Fin B) k) :
    (sampleIndices k s).length=k := by
  induction k with
  | zero => rfl
  | succ k ih => rcases s with ⟨s,a⟩; simp [sampleIndices,ih]

lemma sampleIndices_lt {B : ℕ} (k : ℕ) (s : Sample (Fin B) k) :
    ∀ d ∈ sampleIndices k s, d < B := by
  induction k with
  | zero => simp [sampleIndices]
  | succ k ih =>
    rcases s with ⟨s,a⟩
    intro d hd
    simp only [sampleIndices,List.mem_cons] at hd
    rcases hd with rfl|hd
    · exact a.isLt
    · exact ih s d hd

lemma sampleIndices_count {B : ℕ} (k : ℕ) (s : Sample (Fin B) k) (a : Fin B) :
    (sampleIndices k s).count a.val = count a k s := by
  induction k with
  | zero => simp [sampleIndices,count]
  | succ k ih =>
    rcases s with ⟨s,b⟩
    simp only [sampleIndices,List.count_cons,count,ih]
    by_cases hb : b=a
    · simp [hb]
    · have hv : b.val ≠ a.val := fun h => hb (Fin.ext h)
      simp only [beq_iff_eq,hv,hb,if_false,Nat.add_zero]

/-- Direct hazard from the recovered latest k complete gaps. A harmless fair
prediction is specified for input ages outside the known support bound. -/
def wordHazard (B k : ℕ) (x : List Bool) : ℝ :=
  let a := ageFrom 0 x
  if a < B then
    (((extract k x).count a:ℝ)+1) /
      ∑ j : Fin B, if a ≤ j.val then (((extract k x).count j.val:ℝ)+1) else 0
  else 1/2

lemma wordHazard_mem (B k : ℕ) (x : List Bool) :
    0 ≤ wordHazard B k x ∧ wordHazard B k x ≤ 1 := by
  unfold wordHazard
  dsimp only
  split_ifs with ha
  · let a : Fin B := ⟨ageFrom 0 x,ha⟩
    have hnum : 0 < (((extract k x).count (ageFrom 0 x):ℝ)+1) := by positivity
    have hbound : (((extract k x).count (ageFrom 0 x):ℝ)+1) ≤
        ∑ j : Fin B, if ageFrom 0 x ≤ j.val then (((extract k x).count j.val:ℝ)+1) else 0 := by
      have h := Finset.single_le_sum (s:=Finset.univ)
        (f:=fun j : Fin B => if ageFrom 0 x ≤ j.val then (((extract k x).count j.val:ℝ)+1) else 0)
        (fun j hj => by dsimp; split_ifs <;> positivity) (Finset.mem_univ a)
      simpa only [a,le_refl,if_true] using h
    have hden : 0 < ∑ j : Fin B,
        if ageFrom 0 x ≤ j.val then (((extract k x).count j.val:ℝ)+1) else 0 := hnum.trans_le hbound
    exact ⟨div_nonneg hnum.le hden.le,(div_le_one hden).mpr hbound⟩
  · norm_num

/-- An admissible deterministic source prediction kernel on every input word. -/
def predictor (B k : ℕ) : RandomizedPredictor := fun x =>
  ⟨MeasureTheory.Measure.dirac ⟨wordHazard B k x,wordHazard_mem B k x⟩,
    MeasureTheory.Measure.dirac.isProbabilityMeasure⟩

lemma estimatedHazard_formula {B : ℕ} [Nonempty (Fin B)] (k : ℕ)
    (s : Sample (Fin B) k) (a : Fin B) :
    estimatedHazard k s a = ((count a k s:ℝ)+1)/
      (∑ j : Fin B, if a.val ≤ j.val then ((count j k s:ℝ)+1) else 0) := by
  unfold estimatedHazard
  dsimp only
  rw [survival_eq_sum]
  change (((count a k s:ℝ)+1)/((k:ℝ)+Fintype.card (Fin B))) /
      (∑ j : Fin B, if a.val ≤ j.val then ((count j k s:ℝ)+1)/((k:ℝ)+Fintype.card (Fin B)) else 0) = _
  have hsum : (∑ j : Fin B, if a.val ≤ j.val then
        ((count j k s:ℝ)+1)/((k:ℝ)+Fintype.card (Fin B)) else 0) =
      (∑ j : Fin B, if a.val ≤ j.val then ((count j k s:ℝ)+1) else 0)/((k:ℝ)+Fintype.card (Fin B)) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  rw [hsum]
  exact div_div_div_cancel_right₀ (by positivity) _ _

lemma render_age {n age : ℕ} {ds : List ℕ} (ha : age < n) :
    ageFrom 0 (render n age ds)=age := by
  obtain ⟨j,x,hx,hage,hprefix⟩ := render_parse (ds:=ds) ha
  rw [hx,Paper37.BackwardRender.ageFrom_append]
  exact hage

/-- The word predictor equals the exact iid add-one hazard on each rendered
cycle path; the sample extractor is proved, rather than postulated. -/
theorem wordHazard_on_render {n B : ℕ} [Nonempty (Fin B)]
    (hB : 1 ≤ B) (hBn : 2*B ≤ n) (a : Fin B)
    (s : Sample (Fin B) (n/B-1)) (t : Sample (Fin B) (n-(n/B-1))) :
    wordHazard B (n/B-1) (render n a.val (sampleIndices _ s ++ sampleIndices _ t)) =
      estimatedHazard (n/B-1) s a := by
  let k := n/B-1
  have hk : k ≤ n := by dsimp [k]; have := Nat.div_le_self n B; omega
  have hlen : n ≤ (sampleIndices k s ++ sampleIndices (n-k) t).length := by
    simp only [List.length_append,sampleIndices_length]
    omega
  have hg : ∀ d ∈ sampleIndices k s ++ sampleIndices (n-k) t, d < B := by
    intro d hd
    rcases List.mem_append.mp hd with h|h
    · exact sampleIndices_lt k s d h
    · exact sampleIndices_lt (n-k) t d h
  have hex := render_extract_bounded hB hBn hlen a.isLt hg
  have htake : (sampleIndices k s ++ sampleIndices (n-k) t).take k = sampleIndices k s := by
    rw [List.take_append]
    simp
  rw [htake] at hex
  have ha : a.val < n := by have := a.isLt; omega
  have hage := render_age (ds:=sampleIndices k s ++ sampleIndices (n-k) t) ha
  unfold wordHazard
  rw [hage,if_pos a.isLt,hex,estimatedHazard_formula]
  simp_rw [sampleIndices_count]
  rfl

end Paper37.KnownSupportWord

import MEJF.ActualAsymptotic

/-! The exact positive-level Pareto boundary in (3.16), and the two
unnumbered allocation consequences immediately following it. -/
namespace MEJF.LimitingFrontier
open MEJF.RankFrontier
noncomputable section

def Valid (alpha delta : ℝ) (a b : ℝ) : Prop :=
  0 < a ∧ 0 < b ∧ limitingRate a b alpha ≤ delta

def Pareto (alpha delta a b : ℝ) : Prop :=
  Valid alpha delta a b ∧
    ∀ a' b', Valid alpha delta a' b' → a ≤ a' → b ≤ b' → a'=a ∧ b'=b

lemma budget_product (alpha delta a b : ℝ) (ha : 0 < alpha) (hd : 0 < delta) :
    a/alpha+2*b/delta ≤ 1 ↔ delta*a+2*alpha*b ≤ alpha*delta := by
  have h : a/alpha+2*b/delta = (delta*a+2*alpha*b)/(alpha*delta) := by
    field_simp
    <;> ring
  rw [h,div_le_iff₀ (mul_pos ha hd)]
  simp

lemma valid_iff (alpha delta a b : ℝ) (ha : 0 < alpha) (hd : 0 < delta)
    (hd1 : delta < 1) :
    Valid alpha delta a b ↔ 0<a ∧ 0<b ∧ delta*a+2*alpha*b ≤ alpha*delta := by
  unfold Valid
  constructor
  · rintro ⟨hpa,hpb,h⟩
    exact ⟨hpa,hpb,(budget_product alpha delta a b ha hd).mp
      ((limiting_budget_iff hpa hpb ha hd hd1).mp h)⟩
  · rintro ⟨hpa,hpb,h⟩
    exact ⟨hpa,hpb,(limiting_budget_iff hpa hpb ha hd hd1).mpr
      ((budget_product alpha delta a b ha hd).mpr h)⟩

/-- Every and only maximal positive valid level lies on the source straight
line. This is a maximality statement about the actual limiting law, not just
an algebraic rewriting of its value. -/
theorem pareto_iff (alpha delta a b : ℝ) (ha : 0 < alpha) (hd : 0 < delta)
    (hd1 : delta < 1) (hpa : 0 < a) (hpb : 0 < b) :
    Pareto alpha delta a b ↔ a/alpha+2*b/delta=1 := by
  have heq : a/alpha+2*b/delta=1 ↔ delta*a+2*alpha*b=alpha*delta := by
    have h : a/alpha+2*b/delta = (delta*a+2*alpha*b)/(alpha*delta) := by
      field_simp
      <;> ring
    rw [h,div_eq_one_iff_eq (ne_of_gt (mul_pos ha hd))]
  rw [heq]
  constructor
  · rintro ⟨hv,hm⟩
    have hle := ((valid_iff alpha delta a b ha hd hd1).mp hv).2.2
    by_contra hh
    have hslack : 0 < alpha*delta-(delta*a+2*alpha*b) := by
      rcases lt_or_eq_of_le hle with hlt | he
      · linarith
      · exact (hh he).elim
    let e := (alpha*delta-(delta*a+2*alpha*b))/(2*delta)
    have hep : 0 < e := div_pos hslack (by positivity)
    have he : delta*e = (alpha*delta-(delta*a+2*alpha*b))/2 := by
      dsimp [e]
      field_simp
      <;> ring
    have hv' : Valid alpha delta (a+e) b :=
      (valid_iff alpha delta (a+e) b ha hd hd1).mpr ⟨by linarith,hpb,by nlinarith⟩
    have hx := (hm (a+e) b hv' (by linarith) le_rfl).1
    linarith
  · intro he
    refine ⟨(valid_iff alpha delta a b ha hd hd1).mpr ⟨hpa,hpb,he.le⟩,?_⟩
    intro a' b' hv' haa hbb
    have hv := ((valid_iff alpha delta a' b' ha hd hd1).mp hv').2.2
    have hda : 0 ≤ delta*(a'-a) := mul_nonneg hd.le (sub_nonneg.mpr haa)
    have hdb : 0 ≤ 2*alpha*(b'-b) := mul_nonneg (by positivity) (sub_nonneg.mpr hbb)
    constructor <;> nlinarith

/-- The ordinary factor-two allocation exhausts the limiting budget. -/
theorem factor_two_invalid (alpha delta a : ℝ) (ha : 0 < alpha)
    (hd : 0 < delta) (hd1 : delta < 1) (hpa : 0 < a) :
    delta < limitingRate a (delta/2) alpha := by
  apply lt_of_not_ge
  intro h
  have hb : 0 < delta/2 := by positivity
  have hbudget := (limiting_budget_iff hpa hb ha hd hd1).mp h
  have hdiv : 0 < a/alpha := div_pos hpa ha
  have htwo : 2*(delta/2)/delta = 1 := by field_simp
  rw [htwo] at hbudget
  linarith

/-- At the equality inner level, every positive outer level has limiting
failure one, retaining the rounding handled by ActualAsymptotic. -/
theorem equality_inner_limit (alpha b : ℝ) : limitingRate alpha b alpha=1 := by
  simp [limitingRate]

end
end MEJF.LimitingFrontier

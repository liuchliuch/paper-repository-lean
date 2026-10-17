import Paper14.AppendixFirstMoment
import Paper14.AppendixSecondMoment

open MeasureTheory Set Finset Filter
open scoped ENNReal
namespace Paper14
noncomputable section

lemma ZCount_double_mono {n : ℕ} (α : ℝ) (x : ℝ × ℝ) :
    ZCount n α x ≤ ZCount (2*n) (2*α) x := by
  classical
  have heq : (2*α)/(2*n : ℕ) = α/(n : ℝ) := by push_cast; field_simp
  unfold ZCount
  apply Finset.card_le_card
  intro pr hpr
  obtain ⟨hbox,hrect⟩ := Finset.mem_filter.mp hpr
  apply Finset.mem_filter.mpr
  refine ⟨?_,?_⟩
  · simp only [Finset.mem_product,Finset.mem_Icc] at hbox ⊢
    push_cast at *
    constructor <;> constructor <;> omega
  · rw [heq]
    change 0 < pr.2 ∧ (pr.2 : ℝ) ≤ 2*(2*n : ℕ) ∧
      1-α/(n : ℝ) < (pr.2 : ℝ)*x.2-(pr.1 : ℝ)*x.1 ∧
      (pr.2 : ℝ)*x.2-(pr.1 : ℝ)*x.1 ≤ 1 ∧
      0 < (pr.2 : ℝ)/x.1 ∧ (pr.2 : ℝ)/x.1 ≤ 2*(2*n : ℕ) ∧ IsCoprime pr.1 pr.2
    refine ⟨hrect.1,?_,hrect.2.2.1,hrect.2.2.2.1,hrect.2.2.2.2.1,?_,hrect.2.2.2.2.2.2⟩ <;>
      push_cast <;> nlinarith [hrect.2.1,hrect.2.2.2.2.2.1,(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

lemma first_count_le_one_event_factorial {k l : ℕ} (hkl : k ≤ l) :
    (k : ℝ) ≤ (if k=1 ∧ l=1 then (1 : ℝ) else 0)+(l : ℝ)*((l : ℝ)-1) := by
  have hR : (k : ℝ) ≤ l := by exact_mod_cast hkl
  rcases Nat.eq_zero_or_pos l with hl | hl
  · have hk : k=0 := by omega
    simp [hl,hk]
  · by_cases hl1 : l=1
    · by_cases hk1 : k=1
      · simp [hk1,hl1]
      · have hk0 : k=0 := by omega
        simp [hk0,hl1]
    · have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast (by omega : 2 ≤ l)
      simp only [if_neg (by omega : ¬ (k=1 ∧ l=1)),zero_add]
      have hh := mul_nonneg (Nat.cast_nonneg l : (0 : ℝ) ≤ l) (by linarith : (0 : ℝ) ≤ (l : ℝ)-2)
      nlinarith

def appendixOneEvent (n : ℕ) (α : ℝ) : Set (ℝ × ℝ) :=
  appendixAr (1-α/(n : ℝ)) ∩ {x | ZCount n α x=1 ∧ ZCount (2*n) (2*α) x=1}

lemma measurableSet_ZCount_eq_one (n : ℕ) (α : ℝ) :
    MeasurableSet {x : ℝ × ℝ | ZCount n α x=1} := by
  have heq : {x : ℝ × ℝ | ZCount n α x=1} = {x | (ZCount n α x : ℝ)=1} := by
    ext x
    norm_cast
  rw [heq]
  exact measurableSet_eq_fun (measurable_ZCount_real n α) measurable_const

lemma measurableSet_appendixOneEvent (n : ℕ) (α : ℝ) : MeasurableSet (appendixOneEvent n α) :=
  (measurableSet_appendixAr _).inter ((measurableSet_ZCount_eq_one n α).inter (measurableSet_ZCount_eq_one (2*n) (2*α)))

/-- Source (58), with both actual primitive-point counts. -/
theorem appendix_oneEvent_lower (α : ℝ) (hα : 0 < α) (hαs : α < 1/32) :
    ∀ᶠ n : ℕ in atTop, α/80-320*α^2 ≤ (m (appendixOneEvent n α)).toReal := by
  classical
  filter_upwards [appendix_firstMoment α hα hαs,eventually_ge_atTop 1] with n hfirst hn
  let r := 1-α/(n : ℝ)
  let E := {x : ℝ × ℝ | ZCount n α x=1 ∧ ZCount (2*n) (2*α) x=1}
  have hE : MeasurableSet E := (measurableSet_ZCount_eq_one n α).inter (measurableSet_ZCount_eq_one (2*n) (2*α))
  have hi : Integrable (E.indicator (fun _ => (1 : ℝ))) (m.restrict (appendixAr r)) :=
    (integrable_const _).indicator hE
  have hf := integrable_ZCount_factorial (2*n) (2*α) (m.restrict (appendixAr r))
  have hmono := integral_mono (integrable_ZCount n α (m.restrict (appendixAr r))) (hi.add hf) (fun x => by
    simpa only [Pi.add_apply,Set.indicator_apply,mem_setOf_eq,E] using first_count_le_one_event_factorial (ZCount_double_mono (n := n) α x))
  rw [integral_add' hi hf,setIntegral_indicator hE,setIntegral_const] at hmono
  simp only [smul_eq_mul,mul_one] at hmono
  have hsecond := appendix_secondMoment (by omega : 0<n) hα hαs
  change (∫ x in appendixAr r,(ZCount n α x : ℝ) ∂m) ≤
    (m (appendixOneEvent n α)).toReal+
      (∫ x in appendixAr r,(ZCount (2*n) (2*α) x : ℝ)*((ZCount (2*n) (2*α) x : ℝ)-1) ∂m) at hmono
  linarith

/-- Explicit positive-proportion exactly-one-vector event, before imposing the roof window. -/
theorem appendix_oneEvent_positive :
    ∀ᶠ n : ℕ in atTop, (1 : ℝ)/51200/160 ≤ (m (appendixOneEvent n (1/51200))).toReal := by
  have hh := appendix_oneEvent_lower (1/51200) (by norm_num) (by norm_num)
  filter_upwards [hh] with n hn
  linarith

end
end Paper14

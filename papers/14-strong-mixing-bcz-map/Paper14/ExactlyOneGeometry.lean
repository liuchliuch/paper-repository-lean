import Paper14.AppendixOneEvent
import Paper14.ReturnVisitCount
import Paper14.OrdinaryPrimitiveVectors

open Set Function Finset
open Classical
namespace Paper14
noncomputable section

/-- The two actual primitive-point counts and the actual roof window force exactly one extra return. -/
theorem exactly_one_extra_of_counts_roof {n : ℕ} (hn : 0<n) {α : ℝ}
    (hr : (2 : ℝ)/3 < 1-α/(n : ℝ)) (hr1 : 1-α/(n : ℝ) < 1)
    {x : ℝ × ℝ} (hx : x ∈ appendixOneEvent n α)
    (hroof0 : 3*(n : ℝ) < Hr (1-α/(n : ℝ)) n x)
    (hroof1 : Hr (1-α/(n : ℝ)) n x < 4*(n : ℝ)) :
    x ∈ Yr (1-α/(n : ℝ)) ∧ Rn B (Yr (1-α/(n : ℝ))) n x=n+1 := by
  let r := 1-α/(n : ℝ)
  have hr0 : 0<r := by dsimp [r]; linarith
  have hε : α/(n : ℝ)<1 := by dsimp [r] at hr0; linarith
  have hxY : x ∈ Yr r := ⟨hx.1.1,hx.1.2.2⟩
  let S := (Finset.Ioc 0 (Rn B (Yr r) n x)).filter (fun j => B^[j] x ∉ Yr r)
  have hS : S.card≤1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    obtain ⟨hiN,hiOut⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjN,hjOut⟩ := Finset.mem_filter.mp hj
    obtain ⟨pi,hpi,hHi⟩ := ordinary_outside_F2_pair hxY (Finset.mem_Ioc.mp hiN).1
      (Finset.mem_Ioc.mp hiN).2 hiOut hroof1 hr0 rfl hε
    obtain ⟨pj,hpj,hHj⟩ := ordinary_outside_F2_pair hxY (Finset.mem_Ioc.mp hjN).1
      (Finset.mem_Ioc.mp hjN).2 hjOut hroof1 hr0 rfl hε
    have hcard : ((Finset.Icc (-(4*(2*n) : ℤ)) (4*(2*n)) ×ˢ Finset.Icc (1 : ℤ) (2*(2*n))).filter
        (fun pr => inZRect (2*n) ((2*α)/(2*n : ℕ)) x pr.1 pr.2)).card≤1 := by
      change ZCount (2*n) (2*α) x≤1
      exact hx.2.2.le
    have hpij : pi=pj := Finset.card_le_one.mp hcard pi hpi pj hpj
    apply (H_strictMono hx.1.1).injective
    change H i x=H j x
    rw [hHi,hHj,hpij]
  have hret : ∀ i, ∃ k, 0<k ∧ B^[k] ((inducedMap B (Yr r))^[i] x) ∈ Yr r := by
    intro i
    apply bcz_Yr_return_exists hr0 hr1
    induction i with
    | zero => exact hxY
    | succ i ih =>
      simpa only [iterate_succ_apply',inducedMap] using
        (firstReturn_spec (bcz_Yr_return_exists hr0 hr1 ih)).2
  have hc := ordinary_outside_count B (Yr r) x hret n
  have hnonzero : Rn B (Yr r) n x ≠ n := by
    intro hz
    have hbad := zero_excess_subset_void_or_short_roof hn hε hr hr1 ⟨hxY,hz⟩
    rcases hbad with hvoid | hshort
    · have hh := hx.2.1
      change ZCount n α x=0 at hvoid
      omega
    · exact not_le_of_gt hroof0 hshort
  refine ⟨hxY,?_⟩
  change S.card+n=Rn B (Yr r) n x at hc
  change Rn B (Yr r) n x=n+1
  omega

end
end Paper14

import Paper14.BCZSectionCover
import Paper14.BCZSuspensionMeasure

open MeasureTheory Measure Filter Set Topology Function
open scoped Pointwise ENNReal Matrix
namespace Paper14
noncomputable section
open Background

lemma slBczSuspensionOver_rep {A : Set (ℝ × ℝ)} {g : SL2R}
    (hg : g∈slBczSuspensionOver A) :
    ∃ x∈Omega, x∈A ∧ ∃ s : ℝ,0≤s ∧ s<tau x ∧ g=slChart ![x.1,x.2,s] := by
  change (g 0 0,g 0 1)∈Omega ∩ A ∧ 0≤ -g 1 0/g 0 0 ∧
    -g 1 0/g 0 0<tau (g 0 0,g 0 1) at hg
  refine ⟨(g 0 0,g 0 1),hg.1.1,hg.1.2,-g 1 0/g 0 0,hg.2.1,hg.2.2,?_⟩
  exact (slChart_coordinates hg.1.1.1.ne').symm

lemma slChart_mem_bczSuspensionOver {A : Set (ℝ × ℝ)} {x : ℝ × ℝ} (hx : x∈Omega) (hA : x∈A)
    {s : ℝ} (hs : 0≤s) (hsτ : s<tau x) : slChart ![x.1,x.2,s]∈slBczSuspensionOver A := by
  change suspensionCoordinates (slCoordinates (slChart ![x.1,x.2,s]))∈bczSuspensionOver A
  rw [slCoordinates_chart (by simpa using hx.1.ne')]
  exact ⟨⟨hx,hA⟩,hs,hsτ⟩

lemma slBczSuspensionOver_subset {A : Set (ℝ × ℝ)} :
    slBczSuspensionOver A⊆slBczSuspensionOver univ := by
  intro g hg
  obtain ⟨x,hx,hA,s,hs,hsτ,rfl⟩ := slBczSuspensionOver_rep hg
  exact slChart_mem_bczSuspensionOver hx (mem_univ _) hs hsτ

lemma slBczFundamental_quotient_injOn :
    InjOn (QuotientGroup.mk : SL2R → SL2R ⧸ slIntegerSubgroup) (slBczSuspensionOver univ) := by
  intro g hg h hh hq
  obtain ⟨x,hx,_,s,hs,hsτ,hgx⟩ := slBczSuspensionOver_rep hg
  obtain ⟨y,hy,_,t,ht,htτ,hhy⟩ := slBczSuspensionOver_rep hh
  rw [hgx,hhy] at hq ⊢
  obtain ⟨hxy,hst⟩ := bcz_suspension_quotient_injective hx hy hs hsτ ht htτ hq
  rw [hxy,hst]

/-- The actual BCZ roof domain is a measurable fundamental domain for SL₂(ℤ). -/
theorem bcz_suspension_fundamentalDomain :
    IsFundamentalDomain slIntegerSubgroup.op (slBczSuspensionOver univ) slFlatMeasure := by
  apply IsFundamentalDomain.mk'' (measurableSet_slBczSuspensionOver MeasurableSet.univ).nullMeasurableSet
  · filter_upwards [ae_sl_quotient_roof_representative] with g hg
    obtain ⟨x,hx,s,hs,hsτ,hq⟩ := hg
    let h := slChart ![x.1,x.2,s]
    have hh : h∈slBczSuspensionOver univ := slChart_mem_bczSuspensionOver hx (mem_univ _) hs hsτ
    have hγ : g⁻¹*h∈slIntegerSubgroup := QuotientGroup.eq.mp hq
    refine ⟨⟨MulOpposite.op (g⁻¹*h),hγ⟩,?_⟩
    change g*(g⁻¹*h)∈slBczSuspensionOver univ
    simpa only [mul_inv_cancel_left] using hh
  · intro γ hγ
    apply Disjoint.aedisjoint
    apply disjoint_left.mpr
    intro h hγF hh
    obtain ⟨g,hg,rfl⟩ := hγF
    have hq : (QuotientGroup.mk (γ • g) : SL2R ⧸ slIntegerSubgroup)=QuotientGroup.mk g := by
      exact QuotientGroup.mk_mul_of_mem g γ.2
    have heq : γ • g=g := slBczFundamental_quotient_injOn hh hg hq
    apply hγ
    apply Subtype.ext
    apply MulOpposite.unop_injective
    change MulOpposite.unop (γ : SL2Rᵐᵒᵖ)=1
    apply mul_left_cancel (a := g)
    change g*MulOpposite.unop (γ : SL2Rᵐᵒᵖ)=g at heq
    simpa using heq
  · intro γ
    exact (measurePreserving_smul γ slFlatMeasure).quasiMeasurePreserving

end
end Paper14

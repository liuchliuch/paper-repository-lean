import Paper15.CertifiedGap
import Paper15.ExceptionalBound
import Paper15.GeneralReduction
import Paper15.OutputNecessity

noncomputable section
namespace Paper15

/-- Theorem 1, full upper bound for arbitrary measurable classical triangle
models and stochastic binary response kernels. -/
theorem theorem1_sharp_bound (M : TriangleModel)
    (h1 : M.aggregate.M1=0) (h3 : M.aggregate.M3=0) : M.aggregate.M2 ≤ tStar := by
  obtain ⟨T,qx,qy,qz,ht1,ht3,ht2⟩:=M.exists_ternary_dominating
  exact ht2.trans (theorem1_finite_of_gap_only certifiedGapHypothesis T qx qy qz
    (ht1.trans h1) (ht3.trans h3))

/-- Corollary 2, both directions for the actual eight-outcome output law. -/
theorem corollary2_iff (t : ℝ) (ht0 : 0≤t) (_ht1 : t≤1) :
    IsTriangleLocal t ↔ t≤tStar := by
  constructor
  · intro h
    obtain ⟨M,h1,h2,h3⟩:=triangleLocal_implies_aggregate h
    exact h2 ▸ theorem1_sharp_bound M h1 h3
  · exact corollary2_sufficiency t ht0

end Paper15

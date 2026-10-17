import Paper15.ModelQuadrature

noncomputable section
namespace Paper15

/-- Lemma 4 in its full measure-theoretic scope. A single deterministic
ternary model attains the constrained maximum over all classical triangle
models with arbitrary measurable source spaces and stochastic kernels. -/
theorem lemma4_general_reduction :
    ∃ (T : DetTriangle) (qx qy qz : Simplex2),
      (detMoments' T qx qy qz).M1=0 ∧
      (detMoments' T qx qy qz).M3=0 ∧
      ∀M : TriangleModel,M.aggregate.M1=0 → M.aggregate.M3=0 →
        M.aggregate.M2 ≤ (detMoments' T qx qy qz).M2 := by
  obtain ⟨T,qx,qy,qz,h1,h3,hmax⟩ := lemma4_ternary_reduction'
  refine ⟨T,qx,qy,qz,h1,h3,?_⟩
  intro M hm1 hm3
  obtain ⟨S,sx,sy,sz,hs1,hs3,hs2⟩ := M.exists_ternary_dominating
  exact hs2.trans (hmax S sx sy sz (hs1.trans hm1) (hs3.trans hm3))

end Paper15

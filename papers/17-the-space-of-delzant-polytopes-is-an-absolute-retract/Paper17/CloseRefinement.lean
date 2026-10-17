import Paper17.ChainCombination
import Paper17.SmoothRefinement

/-! Controlled common refinements, from smooth resolution and the proved chain geometry. -/
noncomputable section
open scoped Pointwise
namespace Paper17
namespace DelzantPolytope

/-- **Lemma 2.3**. The perturbation is an actual Minkowski sum of polytopes. -/
theorem lemma_2_3 {n m : ℕ} (P : DelzantPolytope n) (Ps : Fin m → DelzantPolytope n)
    {η : ℝ} (hη : 0 < η) :
    ∃ Q : DelzantPolytope n,
      Metric.hausdorffDist Q.carrier P.carrier < η ∧
      (NormalFan Q.val).refines (NormalFan P.val) ∧
      ∀ i, (NormalFan Q.val).refines (NormalFan (Ps i).val) := by
  obtain ⟨S, hS⟩ := lemma_2_2 (Fin.cons P Ps)
  have hSP : le P S := hS 0
  have hSPs : ∀ i, le (Ps i) S := fun i => hS i.succ
  obtain ⟨t, ht, hdist⟩ := lemma_2_3_perturbation P.val S.val hη
  obtain ⟨hfan, hdel⟩ := lemma_2_1_pair hSP (by norm_num : (0:ℝ) < 1) ht
  refine ⟨⟨(P.val.smul 1).add (S.val.smul t), hdel⟩, ?_,
    Fan.refines_trans hfan.1 hSP, fun i => Fan.refines_trans hfan.1 (hSPs i)⟩
  change Metric.hausdorffDist (((P.val.smul 1).add (S.val.smul t)).carrier) P.carrier < η
  rw [carrier_add_eq, carrier_smul_eq, one_smul]
  rwa [carrier_add_eq] at hdist

end DelzantPolytope
end Paper17

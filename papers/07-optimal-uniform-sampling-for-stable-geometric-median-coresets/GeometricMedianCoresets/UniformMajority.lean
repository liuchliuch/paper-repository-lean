import GeometricMedianCoresets.LabelLaw

/-! The actual `2/5` lower bound for a uniform subset's cluster-majority event. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace GeometricMedianCoresets
open FiniteLaw

/-- A nearly balanced marked cluster wins a uniform sample with probability at least `2/5`.
The event is counted on exactly the `m`-subsets of the population indices. -/
theorem uniform_majority_2_5 {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (mark : Fin n → Bool) {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (hp : ((((Finset.univ : Finset (Fin n)).filter (fun i => mark i = true)).card : ℝ) / n) =
      (1 - θ) / 2)
    (hmθ : (m:ℝ) * θ ^ 2 ≤ 1/200) (hlarge : 20 * (m:ℝ)^2 ≤ n) :
    ((((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => m ≤ 2 * (I.filter (fun i => mark i = true)).card)).card : ℝ) /
      (n.choose m : ℝ) ≥ 2/5 := by
  have hAE : ∀ f : Fin m → Fin n, Function.Injective f →
      (majority (LabelLaw.labels mark f) ↔
        m ≤ 2 * ((TupleSampling.image f).filter (fun i => mark i = true)).card) := by
    intro f hf
    unfold majority
    rw [LabelLaw.trueCount_image mark f hf]
  have hcompare := TupleSampling.withoutReplacement_ge_independent_sub hn hm hmn hlarge
    (fun I => m ≤ 2 * (I.filter (fun i => mark i = true)).card)
    (fun f => majority (LabelLaw.labels mark f)) hAE
  rw [LabelLaw.event_probability hn mark majority, hp] at hcompare
  have hbin : (9/20:ℝ) ≤ event (bernProduct m ((1 - θ) / 2)) majority :=
    biased_majority (m := m) hθ hθ' hmθ
  have hh := (sub_le_sub_right hbin (1/20:ℝ)).trans hcompare
  norm_num at hh ⊢
  convert hh using 1 <;> congr 3 <;> ext I <;> simp

end GeometricMedianCoresets

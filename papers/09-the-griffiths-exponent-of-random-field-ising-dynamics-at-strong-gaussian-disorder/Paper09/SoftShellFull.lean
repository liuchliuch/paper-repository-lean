import Paper09.Disintegration

open Finset BigOperators Classical Real
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) softShellSumDecidableEq {I O : Type*} : DecidableEq (I ⊕ O) :=
  Classical.decEq _
namespace Paper09

/-- The actual Ising version of (2.6), combining the evolving-shell spectral
comparison with the dependent equilibrium defect estimates. -/
theorem gibbs_soft_shell_defect_gap {I O : Type*} [Fintype I] [Fintype O] [Nonempty I]
    (Λ : Lattice (I ⊕ O)) (h : I ⊕ O → ℝ) (β H d : ℝ) (hβ : 0 ≤ β)
    (hdeg : (Λ.maxDegree : ℝ) ≤ 2 * d)
    (S : Finset O) (hS : ∀ i o, Λ.adj (Sum.inl i) (Sum.inr o) → o ∈ S)
    (ζ : O → Spin) (hh : ∀ o ∈ S, H ≤ spinVal (ζ o) * h (Sum.inr o)) :
    let p := gibbs Λ h β univ ∅ (fun _ => 0)
    let ν := sumInteriorGibbs Λ (fun _ => 0) β ζ
    let b := 4 * β * (shellDegree Λ Lattice.leftSites (Lattice.rightShell S) : ℝ)
    spectralGap (V := I ⊕ O) p ≤ spectralGap (V := I) ν *
      exp (4 * fieldMass h Lattice.leftSites + (S.card : ℝ) * qH H d β *
        (exp b - 1 + b)) := by
  let p := gibbs Λ h β univ ∅ (fun _ => 0)
  let ν := sumInteriorGibbs Λ (fun _ => 0) β ζ
  let b := 4 * β * (shellDegree Λ Lattice.leftSites (Lattice.rightShell S) : ℝ)
  let ζfull : I ⊕ O → Spin := Sum.elim (fun _ => 0) ζ
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hcount : ∀ η : I ⊕ O → Spin,
      defectCount (Lattice.rightShell S) ζfull η =
        defectCount S ζ (fun o => η (Sum.inr o)) := by
    intro η
    simp [defectCount, Lattice.rightShell, ζfull, Finset.filter_map, Function.comp_def]
  have hm := lemma_2_3_gibbs Λ h β H d b univ ∅ (Lattice.rightShell S)
    (by simp) (subset_univ _) (fun _ => 0) ζfull hβ hb hdeg (by
      intro x hx
      obtain ⟨o, ho, rfl⟩ := Finset.mem_map.mp hx
      exact hh o ho)
  simp only [hcount] at hm
  have hneg : 0 < p.expect
      (fun η => exp (-b * (defectCount S ζ (fun o => η (Sum.inr o)) : ℝ))) :=
    FinProb.expect_pos_of_pos p (fun _ => exp_pos _)
  have hsoft := gibbs_soft_shell_sum Λ h β hβ S hS ζ
  have hcard : (Lattice.rightShell (I := I) S).card = S.card := by simp [Lattice.rightShell]
  rw [hcard] at hm
  exact lemma_2_3_gap_bound S.card (qH H d β) b (fieldMass h Lattice.leftSites)
    (spectralGap p) (spectralGap ν) _ _ (qH_pos H d β).le hb
    (fieldMass_nonneg _ _) (spectralGap_nonneg _) hm.1 hm.2 hneg hsoft

end Paper09

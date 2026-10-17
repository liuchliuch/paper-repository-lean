import Verification.QuantitativeDiskBoundary

/-! Appendix A: an actual closed-disk filling and the full source dyadic
modulus estimate, in every dimension and with exact Euclidean Hausdorff error.
The compatible-cover construction yields a stronger intermediate bound. -/
noncomputable section
open scoped Topology
namespace P17Contract.QuantitativeDisk
variable {n : ℕ}

/-- Full quantitative disk filling (A.1), with the actual quotient-metric
loop modulus and finite normal-fan range on every compact interior subset. -/
theorem quantitative_disk_filling (f : Angle → EuclideanDelzantSpace n) (hf : Continuous f) :
    ∃ F : ClosedDisk → EuclideanDelzantSpace n, Continuous F ∧
      (∀ θ, F (boundaryPoint θ) = f θ) ∧
      (∀ θ s (hs : 0 < s) (hsHalf : s ≤ 1 / 2),
        dist (F (polarClosed θ s hs.le (by linarith))) (f θ) ≤
          2 * s + Paper17.loopModulus f (s / 2)) ∧
      (∀ θ k s (hk : 1 ≤ k) (hlo : dyadicDepth (k + 1) ≤ s) (hhi : s ≤ dyadicDepth k),
        dist (F (annulusPoint θ k s hk hlo hhi)) (f θ) ≤
          dyadicDepth k + Paper17.loopModulus f (1 / (dyadicCount k : ℝ)) ∧
        dyadicDepth k + Paper17.loopModulus f (1 / (dyadicCount k : ℝ)) ≤
          2 * s + Paper17.loopModulus f (s / 2)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ θ s (hs : 0 < s) (hsHalf : s ≤ 1 / 2), s < δ →
          dist (F (polarClosed θ s hs.le (by linarith))) (f θ) < ε) ∧
      (∀ C : Set ClosedDisk, IsCompact C → (∀ x ∈ C, ‖x.val‖ < 1) →
        ((fun x => normalFan (F x).val.body.carrier) '' C).Finite) := by
  obtain ⟨G, hGc, herr, hfin⟩ := exists_interior_filling_with_modulus f hf
  obtain ⟨F, hFc, hboundary, hstrong, hfinite⟩ :=
    extend_interior_filling_with_modulus f hf G hGc herr hfin
  refine ⟨F, hFc, hboundary, ?_, ?_, ?_, hfinite⟩
  · intro θ s hs hsHalf
    have hm := Paper17.loopModulus_mono hf (by linarith : (0 : ℝ) ≤ s / 16)
      (by linarith : s / 16 ≤ s / 2)
    linarith [hstrong θ s hs hsHalf]
  · intro θ k s hk hlo hhi
    have hsp : 0 < s := (dyadicDepth_pos (k + 1)).trans_le hlo
    have hsHalf : s ≤ 1 / 2 := hhi.trans (dyadicDepth_le_half hk)
    have hsk := dyadicDepth_pos k
    have hhalf : dyadicDepth k / 2 ≤ s := by rwa [dyadicDepth_succ] at hlo
    have hmod1 : Paper17.loopModulus f (s / 16) ≤
        Paper17.loopModulus f (1 / (dyadicCount k : ℝ)) := by
      apply Paper17.loopModulus_mono hf (by linarith)
      rw [reciprocal_dyadicCount]
      linarith
    have hmod2 : Paper17.loopModulus f (1 / (dyadicCount k : ℝ)) ≤
        Paper17.loopModulus f (s / 2) := by
      apply Paper17.loopModulus_mono hf
      · rw [reciprocal_dyadicCount]
        positivity
      · rw [reciprocal_dyadicCount]
        linarith
    constructor
    · have hh := hstrong θ s hsp hsHalf
      change dist (F (polarClosed θ s _ _)) (f θ) ≤ _
      linarith
    · linarith
  · intro ε hε
    obtain ⟨η, hη, hω⟩ := Paper17.loopModulus_small hf (by linarith : (0 : ℝ) < ε / 4)
    let δ : ℝ := min (ε / 2) η
    refine ⟨δ, lt_min (by positivity) hη, ?_⟩
    intro θ s hs hsHalf hsδ
    have hsε : s < ε / 2 := hsδ.trans_le (min_le_left _ _)
    have hsη : s < η := hsδ.trans_le (min_le_right _ _)
    have hωbound := hω (s / 16) (by linarith) (by linarith)
    linarith [hstrong θ s hs hsHalf]

end P17Contract.QuantitativeDisk

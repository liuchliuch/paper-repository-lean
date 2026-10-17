import Paper06.MatchingMarginals

open Real Set BigOperators
open scoped Classical

namespace Paper06.Matching

attribute [local instance] sitesDecidableEq

variable {R : Type*} [Fintype R] [Field R]

/-- The selected sites can occupy different canonical edges. -/
def falseSites (m k : ℕ) (hk : k ≤ m) : Fin k → Sites m :=
  fun i => (⟨i.val, lt_of_lt_of_le i.isLt hk⟩, false)

theorem falseSites_injective (m k : ℕ) (hk : k ≤ m) :
    Function.Injective (falseSites m k hk) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Sites m => x.1.val) h

/-- Complete arbitrary observed endpoints by a winning unobserved
partner on each edge. -/
noncomputable def canonicalCompletion (m k : ℕ) (sample : Fin k → R × R) :
    Sites m → R × R := fun i =>
  if h : i.1.val < k then
    if i.2 then (0, -(sample ⟨i.1.val, h⟩).2) else sample ⟨i.1.val, h⟩
  else (0, 0)

theorem canonicalCompletion_false (m k : ℕ) (hk : k ≤ m)
    (sample : Fin k → R × R) (i : Fin k) :
    canonicalCompletion m k sample (falseSites m k hk i) = sample i := by
  simp [canonicalCompletion, falseSites, i.isLt]

theorem canonicalCompletion_pos (m k : ℕ) (sample : Fin k → R × R) :
    0 < canonicalW m (canonicalCompletion m k sample) := by
  apply Finset.prod_pos
  intro j _
  have hw : (canonicalCompletion m k sample (j, false)).2 +
      (canonicalCompletion m k sample (j, true)).2 =
      (canonicalCompletion m k sample (j, false)).1 *
        (canonicalCompletion m k sample (j, true)).1 := by
    by_cases hj : j.val < k <;> simp [canonicalCompletion, hj]
  unfold edgeW
  rw [if_pos hw, mul_one]
  have hc : (0 : ℝ) < Fintype.card R := by exact_mod_cast
    (Fintype.card_pos : 0 < Fintype.card R)
  positivity

theorem matchingW_pos_of_canonical (m : ℕ) (σ : Equiv.Perm (Sites m))
    (z : Sites m → R × R) (hz : 0 < canonicalW m (z ∘ σ)) :
    0 < matchingW m z := by
  unfold matchingW
  apply mul_pos
  · apply inv_pos.mpr
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm (Sites m)))
  · apply lt_of_lt_of_le hz
    exact Finset.single_le_sum
      (f := fun τ : Equiv.Perm (Sites m) => canonicalW m (z ∘ τ))
      (fun τ _ => canonicalW_nonneg m (z ∘ τ)) (Finset.mem_univ σ)

/-- Every assignment on at most half the sites has a positive extension
under the one fixed matching law. -/
theorem selected_positive_extension {m k : ℕ} (hk : k ≤ m)
    (selection : Fin k → Sites m) (hselection : Function.Injective selection)
    (sample : Fin k → R × R) :
    ∃ z : Sites m → R × R, z ∘ selection = sample ∧ 0 < (matchingLaw m).w z := by
  obtain ⟨σ, hσ⟩ := Posterior.exists_permutation_of_injections
    (falseSites m k hk) selection (falseSites_injective m k hk) hselection
  let z := canonicalCompletion m k sample ∘ σ.symm
  refine ⟨z, ?_, ?_⟩
  · funext i
    change canonicalCompletion m k sample (σ.symm (selection i)) = sample i
    rw [← hσ i, σ.symm_apply_apply]
    exact canonicalCompletion_false m k hk sample i
  · apply matchingW_pos_of_canonical m σ z
    have he : z ∘ σ = canonicalCompletion m k sample := by
      funext i
      simp [z, Function.comp_def]
    rw [he]
    exact canonicalCompletion_pos m k sample

/-- The random-matching marginal has full support whenever no more than
half its coordinates are observed. -/
theorem matching_marginal_fullSupport (n : ℕ) (hn : Even n) (k : ℕ)
    (hk : k ≤ n) (hhalf : 2 * k ≤ n) :
    FinProb.FullSupport (marginal (matchingLawFin (R := R) n hn) k hk) := by
  intro sample
  have hkm : k ≤ n / 2 := by omega
  obtain ⟨z, hz, hpos⟩ := selected_positive_extension hkm
    (sampleSites n hn k hk) (sampleSites_injective n hn k hk) sample
  let e := evenSitesEquiv n hn
  let full : Fin n → R × R := z ∘ e.symm
  have hprefix : (fun i : Fin k => full ⟨i.val, lt_of_lt_of_le i.isLt hk⟩) = sample := by
    exact hz
  have hfull : 0 < (matchingLawFin (R := R) n hn).w full := by
    have he : full ∘ e = z := by
      funext i
      simp [full, Function.comp_def]
    change 0 < (matchingLaw (n / 2)).w (full ∘ e)
    rw [he]
    exact hpos
  unfold marginal
  rw [FinProb.map_w]
  apply lt_of_lt_of_le hfull
  have hh := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun u : Fin n → R × R =>
      @ite ℝ ((fun i : Fin k => u ⟨i.val, lt_of_lt_of_le i.isLt hk⟩) = sample)
        (Classical.propDecidable _) ((matchingLawFin (R := R) n hn).w u) 0)
    (fun u _ => by dsimp only; split_ifs; exact (matchingLawFin n hn).nonneg u; rfl)
    (Finset.mem_univ full)
  simpa only [hprefix, if_true] using hh

end Paper06.Matching

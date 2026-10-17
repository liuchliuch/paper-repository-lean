import Paper29.LocalChannelTools

noncomputable section
set_option maxHeartbeats 600000
open scoped BigOperators Classical
namespace Paper29.HardDistribution
open Transcript

/-- The padded original pool has the same fresh Bernoulli channel at every
informative row. Padding carries zero information under each actual posterior. -/
theorem hard_pool_local_information {E : Type} [Fintype E] {n r N : ℕ}
    (hN : 0 < N) (hblocks : r*N ≤ n)
    (q : E → ℝ) (hq : ∀ e,0 ≤ q e) (hsq : ∑ e,q e=1)
    (β : ℝ) (hβ : 0 ≤ β) (hβhi : β ≤ 1/4) (policy : Policy E (Fin n) Bool)
    (t : ℕ) (h : History E (Fin n) Bool t) (j : Fin n)
    (hj : policy.choose t h=some j) :
    let P := hardSeedLaw (r:=r) (N:=N) q hq hsq β hβ (hβhi.trans (by norm_num))
    0 < P.mass (fun ω => policy.history ω.2.2 (poolBits hblocks ω.2.1) t) h →
    P.localInformation Prod.fst (fun ω => poolBits hblocks ω.2.1 j)
      (fun ω => policy.history ω.2.2 (poolBits hblocks ω.2.1) t) h ≤ 16*β^2 := by
  let P := hardSeedLaw (r:=r) (N:=N) q hq hsq β hβ (hβhi.trans (by norm_num))
  dsimp only
  intro hh
  change 0 < P.mass _ h at hh
  change P.localInformation _ _ _ h ≤ _
  by_cases hrow : ∃ a,blockRow hblocks a=j
  · obtain ⟨a,rfl⟩ := hrow
    have hc (s : Signs r) (b : Bool) :
        P.mass (fun ω => ((ω.1,ω.2.1 a),policy.history ω.2.2 (poolBits hblocks ω.2.1) t)) ((s,b),h) =
          bitMass (1/2+β*sign (s a.1)) b *
            P.mass (fun ω => (ω.1,policy.history ω.2.2 (poolBits hblocks ω.2.1) t)) (s,h) := by
      apply ProductObservation.fresh_joint_mass_of_invariant (signMass r)
        (by intro s; unfold signMass; positivity) (signMass_total r) q hq hsq
        (fun s a b => bitMass (1/2+β*sign (s a.1)) b)
        (by intro s a b; apply bitMass_nonneg <;> cases hs : s a.1 <;> simp [sign,hs] <;> linarith)
        (by intro s a; exact bitMass_total _)
        (fun e y => policy.history e (poolBits hblocks y) t) h a ?_ s b
      intro e y v
      dsimp only
      rw [poolBits_update hN]
      exact policy.history_fiber_update e (poolBits hblocks y) t h (blockRow hblocks a) v hj
    have hinfo := P.local_biased_bit_information_le Prod.fst (fun ω => ω.2.1 a)
      (fun ω => policy.history ω.2.2 (poolBits hblocks ω.2.1) t) h hh (fun s => s a.1) β hβ hβhi hc
    simpa only [poolBits_blockRow hN] using hinfo
  · have he : (fun ω : Signs r × (Bits r N × E) => poolBits hblocks ω.2.1 j) =
        (fun _ => false) := funext (fun ω => poolBits_padded hblocks ω.2.1 j hrow)
    have hz := P.local_information_const Prod.fst
      (fun ω => policy.history ω.2.2 (poolBits hblocks ω.2.1) t) h hh false
    calc
      _ = 0 := by exact (congrArg (fun response => P.localInformation Prod.fst response
          (fun ω => policy.history ω.2.2 (poolBits hblocks ω.2.1) t) h) he).trans hz
      _ ≤ 16*β^2 := by positivity

/-- Actual transcript bound for arbitrary finite private seeds on the full
original pool, with padding rows and stopping included. -/
theorem hard_pool_transcript_bound {E : Type} [Fintype E] {n r N : ℕ}
    (hN : 0 < N) (hblocks : r*N ≤ n)
    (q : E → ℝ) (hq : ∀ e,0 ≤ q e) (hsq : ∑ e,q e=1)
    (β : ℝ) (hβ : 0 ≤ β) (hβhi : β ≤ 1/4) (policy : Policy E (Fin n) Bool) :
    let P := hardSeedLaw (r:=r) (N:=N) q hq hsq β hβ (hβhi.trans (by norm_num))
    P.information Prod.fst (historyRV policy (fun ω => ω.2.2) (fun ω => poolBits hblocks ω.2.1) n) ≤
      16*β^2*expectedQueries P policy (fun ω => ω.2.2) (fun ω => poolBits hblocks ω.2.1) n := by
  apply finite_adaptive_transcript_bound
  · exact Law.Independent.map_left _ _ _ (fun sy : Signs r × Bits r N => (sy.1,poolBits hblocks sy.2))
      (ProductObservation.independent_seed _ _ _ _ _ _ _ _ _)
  · intro t _ h hh j hj
    exact hard_pool_local_information hN hblocks q hq hsq β hβ hβhi policy t h j hj hh

/-- True rate–distortion-to-query lower bound on the full original pool. -/
theorem hard_pool_query_lower {E : Type} [Fintype E] {n r N : ℕ}
    (hN : 0 < N) (hblocks : r*N ≤ n)
    (q : E → ℝ) (hq : ∀ e,0 ≤ q e) (hsq : ∑ e,q e=1)
    (β : ℝ) (hβ : 0 ≤ β) (hβhi : β ≤ 1/4) (policy : Policy E (Fin n) Bool)
    (decoder : History E (Fin n) Bool n → Signs r)
    (herror : let P := hardSeedLaw (r:=r) (N:=N) q hq hsq β hβ (hβhi.trans (by norm_num));
      (∑ ω,P.weight ω*RateDistortion.hamming ω.1
        (decoder (historyRV policy (fun ω => ω.2.2) (fun ω => poolBits hblocks ω.2.1) n ω))) < (1/25:ℝ)*r) :
    let P := hardSeedLaw (r:=r) (N:=N) q hq hsq β hβ (hβhi.trans (by norm_num))
    RateDistortion.cRD*r ≤ 16*β^2*expectedQueries P policy (fun ω => ω.2.2) (fun ω => poolBits hblocks ω.2.1) n := by
  let P := hardSeedLaw (r:=r) (N:=N) q hq hsq β hβ (hβhi.trans (by norm_num))
  apply finite_query_lower P Prod.fst policy (fun ω => ω.2.2) (fun ω => poolBits hblocks ω.2.1) n decoder
    (fun s => ProductObservation.mass_source _ _ _ _ _ _ _ _ _ s) herror
  · exact Law.Independent.map_left _ _ _ (fun sy : Signs r × Bits r N => (sy.1,poolBits hblocks sy.2))
      (ProductObservation.independent_seed _ _ _ _ _ _ _ _ _)
  · intro t _ h hh j hj
    exact hard_pool_local_information hN hblocks q hq hsq β hβ hβhi policy t h j hj hh

end Paper29.HardDistribution

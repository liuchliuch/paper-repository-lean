import Paper37.Adaptive
import Paper37.AdaptiveDP
import Paper37.ContinuationDP

/-! The occupied-coordinate restriction transported through the actual binary
extension/future-gap bijection. -/
noncomputable section
namespace Paper37.AdaptiveContinuation
open scoped BigOperators
open Finset Paper37.Envelope Paper37.EnvelopeBridge Paper37.Prediction Paper37.Renewal
open Paper37.Adaptive Paper37.AdaptiveDP Paper37.ContinuationDP Paper37.DP

/-- The actual number of completed-gap types in a source extension is the
occupied coordinate of its observed-plus-future histogram. -/
theorem extension_nu_eq_occupied (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : z.length+R ≤ H) (b : FutureBlock (parseAge 0 z) R) :
    nu (z++(encode b.val).drop (parseAge 0 z)) =
      occupied (observedCounts z) (gapSet H)
        (countsToFamily (parseAge 0 z+R) b.val.1).val := by
  classical
  let obs := (parseGaps 0 z).map Nat.succ
  let fut := (gapList b.val).map (fun i => i.val+1)
  let g := parseGaps 0 z ++ (gapList b.val).map Fin.val
  have hTH : parseAge 0 z+R ≤ H := by have hh := age_le_length z; omega
  have ho : obs.toFinset ⊆ gapSet H := observed_support z H (by omega)
  have hf : fut.toFinset ⊆ gapSet H := (future_positive_support b.val).trans (gapSet_mono hTH)
  have hc (d : ℕ) : fut.count d = (countsToFamily (parseAge 0 z+R) b.val.1).val d :=
    future_positive_count b.val.1 b.val.2 d
  have hmap : (g.map Nat.succ).toFinset = g.toFinset.image Nat.succ := by ext d; simp
  have hgcard : (g.map Nat.succ).toFinset.card = g.toFinset.card := by
    rw [hmap,Finset.card_image_of_injective _ Nat.succ_injective]
  have hgmap : g.map Nat.succ = obs++fut := by simp [g,obs,fut,List.map_map]
  unfold nu
  rw [← parseGaps_eq_gapsFrom,extension_gaps]
  change g.toFinset.card = _
  rw [← hgcard,hgmap]
  unfold occupied
  congr 1
  ext d
  constructor
  · intro hd
    have hmem : d ∈ obs ∨ d ∈ fut := by simpa using hd
    have hs : d ∈ gapSet H := hmem.elim (fun h => ho (List.mem_toFinset.mpr h))
      (fun h => hf (List.mem_toFinset.mpr h))
    have hp : 0<(obs++fut).count d := List.count_pos_iff.mpr (List.mem_toFinset.mp hd)
    rw [List.count_append,hc] at hp
    exact mem_filter.mpr ⟨hs,by simpa [observedCounts,obs] using hp⟩
  · intro hd
    obtain ⟨hs,hp⟩ := mem_filter.mp hd
    apply List.mem_toFinset.mpr
    apply List.count_pos_iff.mp
    rw [List.count_append,hc]
    simpa [observedCounts,obs] using hp

/-- The restricted source continuation grouped by actual feasible future
histograms, ready for the refined-state regrouping in E.7. -/
theorem restrictedContinuation_histograms (H s : ℕ) (z : List Bool) (R : ℕ)
    (hH : z.length+R ≤ H) :
    restrictedContinuation (z.length+R) s z =
      ∑ c : FeasibleCounts (parseAge 0 z+R),
        if hk : 0<gapCount (fun i => (c.val i).val) then
          (admissibleOrders (gapSet (parseAge 0 z+R)) (parseAge 0 z)
            (countsToFamily (parseAge 0 z+R) c).val:ℚ) *
              (if occupied (observedCounts z) (gapSet H)
                (countsToFamily (parseAge 0 z+R) c).val ≤ s then
                histogramMass H z (countsToFamily (parseAge 0 z+R) c).val else 0)
        else (if occupied (observedCounts z) (gapSet H)
            (countsToFamily (parseAge 0 z+R) c).val ≤ s then
            histogramMass H z (countsToFamily (parseAge 0 z+R) c).val else 0) := by
  unfold restrictedContinuation
  rw [show z.length+R-z.length=R by omega]
  apply sum_extensions_histograms z R (restrictedEnvelope s)
  intro b
  unfold restrictedEnvelope
  rw [extension_nu_eq_occupied H z R hH b,extension_eq_histogramMass H z R hH b]

/-- The no-future-renewal slice retains precisely the observed occupied types. -/
lemma occupied_observed_zero (H : ℕ) (z : List Bool) (hz : z.length ≤ H) :
    occupied (observedCounts z) (gapSet H) 0 = nu z := by
  classical
  let obs := (parseGaps 0 z).map Nat.succ
  have hs : obs.toFinset ⊆ gapSet H := observed_support z H hz
  have heq : (gapSet H).filter (fun d => 0<observedCounts z d+(0:ℕ)) = obs.toFinset := by
    ext d
    constructor
    · intro hd
      have hp := (mem_filter.mp hd).2
      exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by simpa [observedCounts,obs] using hp))
    · intro hd
      exact mem_filter.mpr ⟨hs hd,by
        simpa [observedCounts,obs] using List.count_pos_iff.mpr (List.mem_toFinset.mp hd)⟩
  unfold occupied
  simp only [Pi.zero_apply]
  rw [heq]
  have himage : obs.toFinset = (parseGaps 0 z).toFinset.image Nat.succ := by
    ext d
    simp [obs]
  rw [himage,Finset.card_image_of_injective _ Nat.succ_injective]
  unfold nu
  rw [← parseGaps_eq_gapsFrom]

end Paper37.AdaptiveContinuation

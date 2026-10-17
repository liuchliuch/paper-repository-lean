import Paper29.NormalizedPolicy

noncomputable section
open scoped Classical ENNReal
namespace Paper29.Transcript

universe u

theorem Policy.history_seed {E I R : Type u} (p : Policy E I R) (e : E) (b : I → R) (t : ℕ) :
    History.seed t (p.history e b t)=e := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [Policy.history,History.seed] using ih

/-- The finite normalized policy follows the exact original seed slice, with
output/divergence converted to absorbing padded slots. -/
theorem representative_history_state {Ω E R : Type} {n d : ℕ} (rep : E → Ω) (label : R → ℝ)
    (p : QueryModel.Policy Ω n d) (hfresh : QueryModel.Fresh p) (e : E) (b : Fin n → R) (t : ℕ) :
    let policy := representativePolicy rep label p hfresh
    let h := policy.history e b t
    (History.stopped t h,History.answered t h) =
      (QueryModel.normalizeStep label p (rep e) b)^[t] (false,[]) := by
  let policy := representativePolicy rep label p hfresh
  induction t with
  | zero => rfl
  | succ t ih =>
    change (History.stopped t (policy.history e b t),History.answered t (policy.history e b t)) = _ at ih
    have hseed := policy.history_seed e b t
    rw [Function.iterate_succ_apply',← ih]
    change (History.stopped (t+1) (policy.history e b (t+1)),History.answered (t+1) (policy.history e b (t+1))) = _
    change (History.stopped (t+1) (policy.history e b t,
        (policy.choose t (policy.history e b t)).map (fun i => (i,b i))),
      History.answered (t+1) (policy.history e b t,
        (policy.choose t (policy.history e b t)).map (fun i => (i,b i)))) = _
    have hc : policy.choose t (policy.history e b t) =
        (if History.stopped t (policy.history e b t) then none else
          match p (rep (History.seed t (policy.history e b t)))
              ((History.answered t (policy.history e b t)).map (fun a => (a.1,label a.2))) with
          | .query i => some i
          | _ => none) := rfl
    simp only [History.stopped,History.answered,hc,hseed]
    cases hs : History.stopped t (policy.history e b t) <;>
      cases ha : p (rep e) ((History.answered t (policy.history e b t)).map (fun a => (a.1,label a.2))) <;>
      simp [QueryModel.normalizeStep,hs,ha]

/-- A decoder measurable from the complete finite transcript, including its seed. -/
def representativeDecoder {Ω E R : Type} {n d r : ℕ} (rep : E → Ω) (label : R → ℝ)
    (p : QueryModel.Policy Ω n d) (hrd : r ≤ d) (t : ℕ) (h : History E (Fin n) R t) : RateDistortion.Cube r :=
  match p (rep (History.seed t h)) ((History.answered t h).map (fun a => (a.1,label a.2))) with
  | .output x => fun j => HardDistribution.decode (x (Fin.castLE hrd j))
  | _ => fun _ => false

/-- Returned source outputs have exactly the normalized policy's decoded word. -/
theorem representative_decoder_returned {Ω E R : Type} {n d r : ℕ}
    (rep : E → Ω) (label : R → ℝ) (p : QueryModel.Policy Ω n d) (hfresh : QueryModel.Fresh p)
    (hrd : r ≤ d) (e : E) (b : Fin n → R) (x : Fin d → ℝ) (g : QueryModel.History n)
    (hrun : QueryModel.run p (rep e) (fun i => label (b i))=some (x,g)) :
    representativeDecoder rep label p hrd n ((representativePolicy rep label p hfresh).history e b n) =
      (fun j => HardDistribution.decode (x (Fin.castLE hrd j))) := by
  have hh := QueryModel.execute_return_normalize label p (rep e) b n [] x g hrun
  have hs := representative_history_state rep label p hfresh e b n
  have ha := hh.2
  have hans := congrArg Prod.snd hs
  rw [← hans] at ha
  unfold representativeDecoder
  rw [Policy.history_seed,ha]

/-- Normalization never increases actual distinct-query cost. Divergent source
runs retain infinite cost, so no almost-sure return assumption is hidden. -/
theorem representative_queryCount_le {Ω E R : Type} {n d : ℕ}
    (rep : E → Ω) (label : R → ℝ) (p : QueryModel.Policy Ω n d) (hfresh : QueryModel.Fresh p)
    (e : E) (b : Fin n → R) :
    ENNReal.ofReal (queryCount (representativePolicy rep label p hfresh) e b n) ≤
      QueryModel.queryCount p (rep e) (fun i => label (b i)) := by
  let policy := representativePolicy rep label p hfresh
  cases hr : QueryModel.run p (rep e) (fun i => label (b i)) with
  | none => simp only [QueryModel.queryCount,hr]; exact le_top
  | some out =>
    rcases out with ⟨x,g⟩
    have hh := QueryModel.execute_return_normalize label p (rep e) b n [] x g hr
    have hs := representative_history_state rep label p hfresh e b n
    have hans := congrArg Prod.snd hs
    have htrace := hh.1
    rw [← hans] at htrace
    have hnodup := history_queries_nodup policy e b n
    have hindices := History.answered_indices n (policy.history e b n)
    rw [queryCount_eq_history_length,QueryModel.queryCount,hr,htrace]
    simp only [List.map_map,Function.comp_def]
    rw [hindices,List.toFinset_card_of_nodup hnodup]
    simp [policy]

end Paper29.Transcript

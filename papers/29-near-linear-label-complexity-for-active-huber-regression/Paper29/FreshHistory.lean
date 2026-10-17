import Paper29.Transcript

noncomputable section
namespace Paper29.Transcript
universe u

/-- A deterministic adaptive history reads exactly its queried coordinates. -/
theorem Policy.history_eq_of_agrees {E I R : Type u} (p : Policy E I R)
    (e : E) (b c : I → R) (t : ℕ)
    (hbc : ∀ i ∈ History.queried t (p.history e b t), b i = c i) :
    p.history e b t = p.history e c t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hprefix : ∀ i ∈ History.queried t (p.history e b t), b i = c i := by
      intro i hi
      apply hbc i
      change i ∈ _ ++ _
      exact List.mem_append_left _ hi
    have he := ih hprefix
    change (p.history e b t, (p.choose t (p.history e b t)).map (fun i => (i,b i))) =
      (p.history e c t, (p.choose t (p.history e c t)).map (fun i => (i,c i)))
    rw [← he]
    cases hc : p.choose t (p.history e b t) with
    | none => rfl
    | some j =>
      have hj : j ∈ History.queried (t+1) (p.history e b (t+1)) := by
        simp [Policy.history,History.queried,hc]
      simp only [Option.map_some,Prod.mk.injEq,true_and]
      rw [hbc j hj]

/-- An active history cannot depend on the as-yet unqueried selected response. -/
theorem Policy.history_update_of_fresh {E I R : Type u} [DecidableEq I]
    (p : Policy E I R) (e : E) (b : I → R) (t : ℕ) (j : I) (v : R)
    (hfresh : j ∉ History.queried t (p.history e b t)) :
    p.history e (Function.update b j v) t = p.history e b t := by
  symm
  apply p.history_eq_of_agrees e b (Function.update b j v) t
  intro i hi
  have hij : i ≠ j := by intro he; subst i; exact hfresh hi
  simp [Function.update_of_ne hij]

/-- Full history-fiber invariance for a selected fresh response, in both
counterfactual directions. This is the own adaptive-posterior argument needed
before applying the finite product law's fresh-coordinate marginal identity. -/
theorem Policy.history_fiber_update {E I R : Type u} [DecidableEq I]
    (p : Policy E I R) (e : E) (b : I → R) (t : ℕ) (h : History E I R t)
    (j : I) (v : R) (hchoose : p.choose t h = some j) :
    p.history e (Function.update b j v) t = h ↔ p.history e b t = h := by
  constructor
  · intro hu
    have hf := p.fresh t h j hchoose
    have hf' : j ∉ History.queried t (p.history e (Function.update b j v) t) := by rwa [hu]
    have hh := p.history_update_of_fresh e (Function.update b j v) t j (b j) hf'
    have hrestore : Function.update (Function.update b j v) j (b j) = b := by
      funext i
      by_cases hi : i=j
      · subst i; simp
      · simp [Function.update_of_ne hi]
    rw [hrestore,hu] at hh
    exact hh
  · intro hb
    have hf := p.fresh t h j hchoose
    have hf' : j ∉ History.queried t (p.history e b t) := by rwa [hb]
    rw [p.history_update_of_fresh e b t j v hf',hb]

end Paper29.Transcript

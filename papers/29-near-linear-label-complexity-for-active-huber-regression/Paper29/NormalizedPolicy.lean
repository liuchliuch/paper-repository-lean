import Paper29.FiniteExecution
import Paper29.Transcript

noncomputable section
open scoped Classical
namespace Paper29.QueryModel

/-- One stopped state of the original deterministic seed slice over finite labels. -/
def normalizeStep {Ω R : Type} {n d : ℕ} (label : R → ℝ) (p : Policy Ω n d) (ω : Ω)
    (b : Fin n → R) (state : Bool × List (Fin n × R)) : Bool × List (Fin n × R) :=
  if state.1 then state else
    match p ω (state.2.map (fun a => (a.1,label a.2))) with
    | .query i => (false,state.2++[(i,b i)])
    | _ => (true,state.2)

theorem normalize_stopped_iterate {Ω R : Type} {n d : ℕ} (label : R → ℝ) (p : Policy Ω n d)
    (ω : Ω) (b : Fin n → R) (h : List (Fin n × R)) (k : ℕ) :
    (normalizeStep label p ω b)^[k] (true,h) = (true,h) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih]; rfl

/-- Returned runs correspond exactly to the frozen finite-label state after
n slots, with the same real output decision at that state. -/
theorem execute_return_normalize {Ω R : Type} {n d : ℕ} (label : R → ℝ) (p : Policy Ω n d)
    (ω : Ω) (b : Fin n → R) (k : ℕ) (h : List (Fin n × R))
    (x : Fin d → ℝ) (g : History n)
    (hrun : execute p ω (fun i => label (b i)) (k+1) (h.map (fun a => (a.1,label a.2))) = some (x,g)) :
    let final := (normalizeStep label p ω b)^[k] (false,h)
    g=final.2.map (fun a => (a.1,label a.2)) ∧
      p ω (final.2.map (fun a => (a.1,label a.2))) = .output x := by
  induction k generalizing h with
  | zero =>
    cases ha : p ω (h.map (fun a => (a.1,label a.2))) with
    | output y =>
      have he : y=x ∧ h.map (fun a => (a.1,label a.2))=g := by simpa only [execute,ha,Option.some.injEq,Prod.mk.injEq] using hrun
      exact ⟨he.2.symm,by
        change p ω (h.map (fun a => (a.1,label a.2))) = .output x
        rw [ha,he.1]⟩
    | query i => simp only [execute,ha] at hrun; cases hrun
    | diverge => simp only [execute,ha] at hrun; cases hrun
  | succ k ih =>
    cases ha : p ω (h.map (fun a => (a.1,label a.2))) with
    | output y =>
      have he : y=x ∧ h.map (fun a => (a.1,label a.2))=g := by simpa only [execute,ha,Option.some.injEq,Prod.mk.injEq] using hrun
      have hstep : normalizeStep label p ω b (false,h) = (true,h) := by simp [normalizeStep,ha]
      simp only [Function.iterate_succ_apply,hstep,normalize_stopped_iterate]
      exact ⟨he.2.symm,by rw [ha,he.1]⟩
    | query i =>
      have hh : execute p ω (fun i => label (b i)) (k+1)
          ((h++[(i,b i)]).map (fun a => (a.1,label a.2))) = some (x,g) := by
        simpa only [execute,ha,List.map_append,List.map_cons,List.map_nil] using hrun
      have hstep : normalizeStep label p ω b (false,h) = (false,h++[(i,b i)]) := by simp [normalizeStep,ha]
      simpa only [Function.iterate_succ_apply,hstep] using ih (h++[(i,b i)]) hh
    | diverge => simp only [execute,ha] at hrun; cases hrun

end Paper29.QueryModel
namespace Paper29.Transcript
universe u

def History.seed {E I R : Type u} : (t : ℕ) → History E I R t → E
  | 0,e => e
  | t+1,h => History.seed t h.1

def History.answered {E I R : Type u} : (t : ℕ) → History E I R t → List (I × R)
  | 0,_ => []
  | t+1,h => History.answered t h.1 ++ match h.2 with
    | none => []
    | some z => [z]

def History.stopped {E I R : Type u} : (t : ℕ) → History E I R t → Bool
  | 0,_ => false
  | t+1,h => History.stopped t h.1 || h.2.isNone

theorem History.answered_indices {E I R : Type u} (t : ℕ) (h : History E I R t) :
    (History.answered t h).map Prod.fst = History.queried t h := by
  induction t with
  | zero => rfl
  | succ t ih => rcases h with ⟨h,z⟩; cases z <;> simp [History.answered,History.queried,ih]

def representativePolicy {Ω E R : Type} {n d : ℕ} (rep : E → Ω) (label : R → ℝ)
    (p : QueryModel.Policy Ω n d) (hfresh : QueryModel.Fresh p) : Policy E (Fin n) R where
  choose t h := if History.stopped t h then none else
    match p (rep (History.seed t h)) ((History.answered t h).map (fun a => (a.1,label a.2))) with
    | .query i => some i
    | _ => none
  stopped t h := by simp [History.stopped]
  fresh t h j hj := by
    by_cases hs : History.stopped t h=true
    · simp only [if_pos hs,reduceCtorEq] at hj
    · simp only [if_neg hs] at hj
      cases ha : p (rep (History.seed t h)) ((History.answered t h).map (fun a => (a.1,label a.2))) with
      | output x => rw [ha] at hj; cases hj
      | diverge => rw [ha] at hj; cases hj
      | query i =>
        rw [ha] at hj
        have he : i=j := Option.some.inj hj
        subst i
        have hh := hfresh (rep (History.seed t h)) _ j ha
        simpa only [List.map_map,Function.comp_def,History.answered_indices] using hh

end Paper29.Transcript

import ELV.ReflectionCompile

noncomputable section
namespace ELV.Query
open ELV.Stabilize
variable {E N Q Q' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N]
  [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
  [NormedAddCommGroup Q'] [InnerProductSpace ℂ Q']

def Gate.requery (e : Q ≃ₗᵢ[ℂ] Q') : Gate E N Q → Gate E N Q'
  | .work U => .work U
  | .query L => .query (L.trans (pairCongr (LinearIsometryEquiv.refl ℂ N) e))

def requery (e : Q ≃ₗᵢ[ℂ] Q') (c : Circuit E N Q) : Circuit E N Q' := c.map (Gate.requery e)

lemma Gate.requery_run (e : Q ≃ₗᵢ[ℂ] Q') (O : Q ≃ₗᵢ[ℂ] Q) (O' : Q' ≃ₗᵢ[ℂ] Q')
    (hO : ∀ q, O' (e q)=e (O q)) (g : Gate E N Q) (z : E) :
    (g.requery e).unitary O' z = g.unitary O z := by
  cases g with
  | work U => rfl
  | query L =>
    apply L.injective
    simp [Gate.requery,Gate.unitary,pairCongr,LinearIsometryEquiv.trans_apply,hO]
    change WithLp.toLp 2 ((L z).fst,e.symm (e (O (L z).snd))) = _
    rw [e.symm_apply_apply]

lemma Gate.requery_queried (e : Q ≃ₗᵢ[ℂ] Q') (g : Gate E N Q) (z : E) :
    (g.requery e).queried z=e (g.queried z) := by
  cases g <;> simp [Gate.requery,Gate.queried,pairCongr,LinearIsometryEquiv.trans_apply]

lemma requery_run (e : Q ≃ₗᵢ[ℂ] Q') (O : Q ≃ₗᵢ[ℂ] Q) (O' : Q' ≃ₗᵢ[ℂ] Q')
    (hO : ∀ q, O' (e q)=e (O q)) (c : Circuit E N Q) (z : E) :
    run O' (requery e c) z=run O c z := by
  induction c generalizing z with
  | nil => rfl
  | cons g c ih =>
    simp only [requery,List.map_cons,run,Gate.requery_run e O O' hO]
    exact ih _

lemma requery_cost (e : Q ≃ₗᵢ[ℂ] Q') (O : Q ≃ₗᵢ[ℂ] Q) (O' : Q' ≃ₗᵢ[ℂ] Q')
    (hO : ∀ q, O' (e q)=e (O q)) (c : Circuit E N Q) (z : E) :
    cost O' (requery e c) z=cost O c z := by
  induction c generalizing z with
  | nil => simp [requery]
  | cons g c ih =>
    simp only [requery,List.map_cons,cost_cons,Gate.requery_run e O O' hO,
      Gate.requery_queried,e.norm_map]
    exact congrArg (fun r : ℝ => ‖g.queried z‖^2+r) (ih _)

lemma requery_queryCount (e : Q ≃ₗᵢ[ℂ] Q') (c : Circuit E N Q) :
    queryCount (requery e c)=queryCount c := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    change queryCount (requery e c)=queryCount c at ih
    cases g with
    | work U => simpa only [requery,List.map_cons,Gate.requery,queryCount] using ih
    | query L => simpa only [requery,List.map_cons,Gate.requery,queryCount] using congrArg (fun k : ℕ => 1+k) ih

lemma transport_queryCount {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (e : E ≃ₗᵢ[ℂ] F) (c : Circuit E N Q) : queryCount (transport e c)=queryCount c := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    cases g with
    | work U => simpa only [transport,List.map_cons,Gate.transport,queryCount] using ih
    | query L => simpa only [transport,List.map_cons,Gate.transport,queryCount] using congrArg (fun k : ℕ => 1+k) ih

lemma parallel_queryCount {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    (c : Circuit E N Q) : queryCount (parallel (A:=A) c)=queryCount c := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    cases g with
    | work U => simpa only [parallel,List.map_cons,Gate.parallel,queryCount] using ih
    | query L => simpa only [parallel,List.map_cons,Gate.parallel,queryCount] using congrArg (fun k : ℕ => 1+k) ih

end ELV.Query

import ELV.QueryCircuit

/-! Fixed unitary changes of workspace, unqueried parallel summands, and
homogeneity of actual finite-circuit query cost. -/
noncomputable section
namespace ELV.Query
open ELV.Stabilize
variable {E F N Q A : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N]
  [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
  [NormedAddCommGroup A] [InnerProductSpace ℂ A]

def Gate.transport (e : E ≃ₗᵢ[ℂ] F) : Gate E N Q → Gate F N Q
  | .work U => .work (e.symm.trans (U.trans e))
  | .query L => .query (e.symm.trans L)

lemma Gate.transport_run (e : E ≃ₗᵢ[ℂ] F) (g : Gate E N Q) (O : Q ≃ₗᵢ[ℂ] Q) (z : E) :
    (g.transport e).unitary O (e z) = e (g.unitary O z) := by
  cases g <;> simp [Gate.transport,Gate.unitary,LinearIsometryEquiv.trans_apply]

lemma Gate.transport_queried (e : E ≃ₗᵢ[ℂ] F) (g : Gate E N Q) (z : E) :
    (g.transport e).queried (e z) = g.queried z := by
  cases g <;> simp [Gate.transport,Gate.queried,LinearIsometryEquiv.trans_apply]

def transport (e : E ≃ₗᵢ[ℂ] F) (c : Circuit E N Q) : Circuit F N Q := c.map (Gate.transport e)

theorem run_transport (e : E ≃ₗᵢ[ℂ] F) (c : Circuit E N Q) (O : Q ≃ₗᵢ[ℂ] Q) (z : E) :
    run O (transport e c) (e z) = e (run O c z) := by
  induction c generalizing z with
  | nil => rfl
  | cons g c ih =>
    simp only [transport,List.map_cons,run,Gate.transport_run]
    exact ih _

theorem cost_transport (e : E ≃ₗᵢ[ℂ] F) (c : Circuit E N Q) (O : Q ≃ₗᵢ[ℂ] Q) (z : E) :
    cost O (transport e c) (e z) = cost O c z := by
  induction c generalizing z with
  | nil => simp [transport]
  | cons g c ih =>
    simp only [transport,List.map_cons,cost_cons,Gate.transport_run,Gate.transport_queried]
    exact congrArg (fun r : ℝ => ‖g.queried z‖ ^ 2 + r) (ih _)

lemma Gate.queried_smul (g : Gate E N Q) (a : ℂ) (z : E) : g.queried (a • z) = a • g.queried z := by
  cases g <;> simp [Gate.queried,map_smul]

theorem run_smul (c : Circuit E N Q) (O : Q ≃ₗᵢ[ℂ] Q) (a : ℂ) (z : E) :
    run O c (a • z) = a • run O c z := by
  induction c generalizing z with
  | nil => rfl
  | cons g c ih => simp only [run,map_smul,ih]

theorem cost_smul (c : Circuit E N Q) (O : Q ≃ₗᵢ[ℂ] Q) (a : ℂ) (z : E) :
    cost O c (a • z) = ‖a‖ ^ 2 * cost O c z := by
  induction c generalizing z with
  | nil => simp
  | cons g c ih =>
    rw [cost_cons,cost_cons,Gate.queried_smul,map_smul,ih,norm_smul,mul_pow]
    ring

/-- Add a genuinely unqueried parallel summand, without charging its norm. -/
def Gate.parallel : Gate E N Q → Gate (HilbertPair A E) (HilbertPair A N) Q
  | .work U => .work (pairCongr (LinearIsometryEquiv.refl ℂ A) U)
  | .query L => .query ((pairCongr (LinearIsometryEquiv.refl ℂ A) L).trans pairAssoc.symm)

lemma Gate.parallel_run (g : Gate E N Q) (O : Q ≃ₗᵢ[ℂ] Q) (a : A) (z : E) :
    g.parallel.unitary O (WithLp.toLp 2 (a,z)) = WithLp.toLp 2 (a,g.unitary O z) := by
  cases g <;> rfl

lemma Gate.parallel_queried (g : Gate E N Q) (a : A) (z : E) :
    g.parallel.queried (WithLp.toLp 2 (a,z)) = g.queried z := by
  cases g <;> rfl

def parallel (c : Circuit E N Q) : Circuit (HilbertPair A E) (HilbertPair A N) Q :=
  c.map Gate.parallel

theorem run_parallel (c : Circuit E N Q) (O : Q ≃ₗᵢ[ℂ] Q) (a : A) (z : E) :
    run O (parallel c) (WithLp.toLp 2 (a,z)) = WithLp.toLp 2 (a,run O c z) := by
  induction c generalizing z with
  | nil => rfl
  | cons g c ih =>
    simp only [parallel,List.map_cons,run,Gate.parallel_run]
    exact ih _

theorem cost_parallel (c : Circuit E N Q) (O : Q ≃ₗᵢ[ℂ] Q) (a : A) (z : E) :
    cost O (parallel c) (WithLp.toLp 2 (a,z)) = cost O c z := by
  induction c generalizing z with
  | nil => simp [parallel]
  | cons g c ih =>
    simp only [parallel,List.map_cons,cost_cons,Gate.parallel_run,Gate.parallel_queried]
    exact congrArg (fun r : ℝ => ‖g.queried z‖ ^ 2 + r) (ih _)

end ELV.Query

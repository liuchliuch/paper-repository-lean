import ELV.CircuitTransforms
import ELV.LpHilbert

/-! Replace every reflection query by two real directional queries. All
inserted layouts and work operations depend only on the known reflection. -/
noncomputable section
namespace ELV.Query
open ELV.Stabilize
variable {E N Q : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N]
  [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]

def swapPair : HilbertPair Q Q ≃ₗᵢ[ℂ] HilbertPair Q Q where
  toLinearEquiv :=
    { toFun := fun z => WithLp.toLp 2 (z.snd,z.fst)
      invFun := fun z => WithLp.toLp 2 (z.snd,z.fst)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [WithLp.prod_norm_sq_eq_of_L2,WithLp.toLp_fst,WithLp.toLp_snd] using
      add_comm (‖z.snd‖^2) (‖z.fst‖^2)

lemma run_append (O : Q ≃ₗᵢ[ℂ] Q) (c d : Circuit E N Q) (z : E) :
    run O (c++d) z = run O d (run O c z) := by
  induction c generalizing z with
  | nil => rfl
  | cons g c ih => exact ih _

lemma cost_append (O : Q ≃ₗᵢ[ℂ] Q) (c d : Circuit E N Q) (z : E) :
    cost O (c++d) z = cost O c z + cost O d (run O c z) := by
  induction c generalizing z with
  | nil => simp [run]
  | cons g c ih =>
    simp only [List.cons_append,cost_cons,run,ih]
    ring

/-- Add an initially empty directional branch, and associate the query pair. -/
def expandedLayout (L : E ≃ₗᵢ[ℂ] HilbertPair N Q) :
    HilbertPair E Q ≃ₗᵢ[ℂ] HilbertPair N (HilbertPair Q Q) :=
  (pairCongr L (LinearIsometryEquiv.refl ℂ Q)).trans pairAssoc

def layoutWork (L : E ≃ₗᵢ[ℂ] HilbertPair N Q) (U : HilbertPair Q Q ≃ₗᵢ[ℂ] HilbertPair Q Q) :
    HilbertPair E Q ≃ₗᵢ[ℂ] HilbertPair E Q :=
  (expandedLayout L).trans ((pairCongr (LinearIsometryEquiv.refl ℂ N) U).trans (expandedLayout L).symm)

/-- The known middle reflection acts before swapping the direction bit. -/
def reflectionGate (Z : Q ≃ₗᵢ[ℂ] Q) (L : E ≃ₗᵢ[ℂ] HilbertPair N Q) :
    Circuit (HilbertPair E Q) N (HilbertPair Q Q) :=
  [.query (expandedLayout L),
   .work (layoutWork L ((pairCongr Z (LinearIsometryEquiv.refl ℂ Q)).trans swapPair)),
   .query (expandedLayout L),.work (layoutWork L swapPair)]

lemma reflectionGate_run (O Z : Q ≃ₗᵢ[ℂ] Q) (L : E ≃ₗᵢ[ℂ] HilbertPair N Q) (z : E) :
    run (pairCongr O O.symm) (reflectionGate Z L) (WithLp.toLp 2 (z,0)) =
      WithLp.toLp 2 ((Gate.query L).unitary (O.trans (Z.trans O.symm)) z,0) := by
  apply (expandedLayout L).injective
  simp [reflectionGate,run,Gate.unitary,expandedLayout,layoutWork,pairCongr,pairAssoc,
    swapPair,LinearIsometryEquiv.trans_apply]

lemma reflectionGate_cost (O Z : Q ≃ₗᵢ[ℂ] Q) (L : E ≃ₗᵢ[ℂ] HilbertPair N Q) (z : E) :
    cost (pairCongr O O.symm) (reflectionGate Z L) (WithLp.toLp 2 (z,0)) =
      2*‖(L z).snd‖^2 := by
  simp [reflectionGate,cost_cons,Gate.queried,Gate.unitary,expandedLayout,layoutWork,
    pairCongr,pairAssoc,swapPair,LinearIsometryEquiv.trans_apply,WithLp.prod_norm_sq_eq_of_L2]
  ring

def compileGate (Z : Q ≃ₗᵢ[ℂ] Q) : Gate E N Q → Circuit (HilbertPair E Q) N (HilbertPair Q Q)
  | .work U => [.work (pairCongr U (LinearIsometryEquiv.refl ℂ Q))]
  | .query L => reflectionGate Z L

def compileReflection (Z : Q ≃ₗᵢ[ℂ] Q) : Circuit E N Q → Circuit (HilbertPair E Q) N (HilbertPair Q Q)
  | [] => []
  | g::c => compileGate Z g ++ compileReflection Z c

lemma compileGate_run (O Z : Q ≃ₗᵢ[ℂ] Q) (g : Gate E N Q) (z : E) :
    run (pairCongr O O.symm) (compileGate Z g) (WithLp.toLp 2 (z,0)) =
      WithLp.toLp 2 (g.unitary (O.trans (Z.trans O.symm)) z,0) := by
  cases g with
  | work U => rfl
  | query L => exact reflectionGate_run O Z L z

lemma compileGate_cost (O Z : Q ≃ₗᵢ[ℂ] Q) (g : Gate E N Q) (z : E) :
    cost (pairCongr O O.symm) (compileGate Z g) (WithLp.toLp 2 (z,0)) = 2*‖g.queried z‖^2 := by
  cases g with
  | work U => simp [compileGate,cost_cons,Gate.queried]
  | query L => exact reflectionGate_cost O Z L z

/-- Actual run equivalence, on the original state with an empty added branch. -/
theorem compileReflection_run (O Z : Q ≃ₗᵢ[ℂ] Q) (c : Circuit E N Q) (z : E) :
    run (pairCongr O O.symm) (compileReflection Z c) (WithLp.toLp 2 (z,0)) =
      WithLp.toLp 2 (run (O.trans (Z.trans O.symm)) c z,0) := by
  induction c generalizing z with
  | nil => rfl
  | cons g c ih =>
    rw [compileReflection,run_append,compileGate_run,ih]
    rfl

/-- The two actual queries have equal norms, hence exactly double the cost. -/
theorem compileReflection_cost (O Z : Q ≃ₗᵢ[ℂ] Q) (c : Circuit E N Q) (z : E) :
    cost (pairCongr O O.symm) (compileReflection Z c) (WithLp.toLp 2 (z,0)) =
      2*cost (O.trans (Z.trans O.symm)) c z := by
  induction c generalizing z with
  | nil => simp [compileReflection]
  | cons g c ih =>
    rw [compileReflection,cost_append,compileGate_cost,compileGate_run,ih,cost_cons]
    ring

/-- Query count counts real oracle gates, omitting free work. -/
def queryCount : Circuit E N Q → ℕ
  | [] => 0
  | .work _ :: c => queryCount c
  | .query _ :: c => 1+queryCount c

lemma queryCount_append (c d : Circuit E N Q) : queryCount (c++d)=queryCount c+queryCount d := by
  induction c with
  | nil => simp [queryCount]
  | cons g c ih => cases g <;> simp [queryCount,ih,Nat.add_assoc]

lemma compileReflection_queryCount (Z : Q ≃ₗᵢ[ℂ] Q) (c : Circuit E N Q) :
    queryCount (compileReflection Z c) = 2*queryCount c := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    cases g <;> simp [compileReflection,compileGate,reflectionGate,queryCount_append,queryCount,ih,Nat.mul_add,Nat.add_assoc] <;> omega

end ELV.Query

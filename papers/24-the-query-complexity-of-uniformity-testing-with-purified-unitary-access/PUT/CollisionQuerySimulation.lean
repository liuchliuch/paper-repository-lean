import PUT.CollisionCircuit

/-!
# Standard function-query compilation

A standard query adds `f(address)` to a target register. Every other gate is
independent of `f`. The generic compiler below evaluates the legal address,
performs a known action controlled by the returned value, and uncomputes.
Its query count is the syntactic count of actual standard-query gates.
-/
noncomputable section
namespace PUT.CollisionQuerySimulation
open PUT.QueryModel PUT.CollisionCircuit

variable {D : ℕ} [NeZero D]
variable {B : Type*} [Fintype B] [DecidableEq B]

abbrev QueryBasis (B : Type*) (D : ℕ) := B × (Fin D × Fin D)
abbrev QuerySpace (B : Type*) (D : ℕ) := EuclideanSpace ℂ (QueryBasis B D)

/-- Standard additive function query, tensored with unrestricted workspace. -/
def standard (f : Fin D → Fin D) : Equiv.Perm (QueryBasis B D) where
  toFun := fun ⟨b,a,z⟩ => (b,a,z + f a)
  invFun := fun ⟨b,a,z⟩ => (b,a,z - f a)
  left_inv := by rintro ⟨b,a,z⟩; simp
  right_inv := by rintro ⟨b,a,z⟩; simp

def negateTarget : Equiv.Perm (QueryBasis B D) where
  toFun := fun ⟨b,a,z⟩ => (b,a,-z)
  invFun := fun ⟨b,a,z⟩ => (b,a,-z)
  left_inv := by rintro ⟨b,a,z⟩; simp
  right_inv := by rintro ⟨b,a,z⟩; simp

/-- One inverse additive query is one forward query conjugated by negation. -/
theorem standard_inverse (f : Fin D → Fin D) :
    ((negateTarget (B := B)).trans (standard f)).trans negateTarget = (standard f).symm := by
  ext ⟨b,a,z⟩ <;> simp [negateTarget, standard, Equiv.trans_apply, sub_eq_add_neg, add_comm]

inductive Gate (B : Type*) [Fintype B] (D : ℕ) where
  | free (U : QuerySpace B D ≃ₗᵢ[ℂ] QuerySpace B D)
  | query (direction : Direction)

abbrev Program (B : Type*) [Fintype B] (D : ℕ) := List (Gate B D)

def Gate.operation (f : Fin D → Fin D) : Gate B D →
    QuerySpace B D ≃ₗᵢ[ℂ] QuerySpace B D
  | .free U => U
  | .query q => queryUnitary (lift (standard f)) q

def Program.operation (w : Program B D) (f : Fin D → Fin D) :
    QuerySpace B D ≃ₗᵢ[ℂ] QuerySpace B D :=
  match w with
  | [] => .refl ℂ _
  | g :: gs => (g.operation f).trans (Program.operation gs f)

def Program.queries (w : Program B D) : ℕ :=
  (w.map fun g => match g with | .free _ => 0 | .query _ => 1).sum

/-- Clean query-address and target ancillas. -/
def clean (v : EuclideanSpace ℂ B) : QuerySpace B D :=
  ∑ b, EuclideanSpace.single (b,(0,0)) (v b)

@[simp] theorem clean_single (b : B) (c : ℂ) :
    clean (D := D) (EuclideanSpace.single b c) = EuclideanSpace.single (b,(0,0)) c := by
  ext ⟨x,a,z⟩
  simp only [clean, eval_sum, EuclideanSpace.single_apply, Prod.mk.injEq, ite_and]
  simp
  split_ifs <;> rfl

theorem clean_coordinate (v : EuclideanSpace ℂ B) (b : B) (a z : Fin D) :
    clean v (b,a,z) = if a = 0 ∧ z = 0 then v b else 0 := by
  simp only [clean, eval_sum, EuclideanSpace.single_apply, Prod.mk.injEq]
  by_cases ha : a = 0 <;> by_cases hz : z = 0 <;> simp [ha, hz, eq_comm]

theorem expansion (v : EuclideanSpace ℂ B) : v = ∑ b, EuclideanSpace.single b (v b) := by
  ext b
  simp [eval_sum, EuclideanSpace.single_apply]

theorem clean_lift (e : Equiv.Perm (QueryBasis B D)) (t : Equiv.Perm B)
    (h : ∀ b, e (b,(0,0)) = (t b,(0,0))) (v : EuclideanSpace ℂ B) :
    lift e (clean v) = clean (lift t v) := by
  rw [clean]
  simp only [map_sum, lift_single, h]
  change (∑ b, EuclideanSpace.single (t b,(0,0)) (v b)) =
    ∑ b, EuclideanSpace.single (b,(0,0)) (v (t.symm b))
  calc
    _ = ∑ b, EuclideanSpace.single (t b,((0,0) : Fin D × Fin D)) (v (t.symm (t b))) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Equiv.symm_apply_apply]
    _ = _ := Equiv.sum_comp (t : B ≃ B)
      (fun b => EuclideanSpace.single (b,((0,0) : Fin D × Fin D)) (v (t.symm b)))

/-! ## Compositional clean-ancilla semantics -/

def curry : QuerySpace B D ≃ₗᵢ[ℂ] Register (Fin D × Fin D) (EuclideanSpace ℂ B) :=
  (lift (show QueryBasis B D ≃ (q : Fin D × Fin D) × B from
    { toFun := fun ⟨b,q⟩ => ⟨q,b⟩
      invFun := fun ⟨q,b⟩ => (b,q)
      left_inv := by rintro ⟨b,q⟩; rfl
      right_inv := by rintro ⟨q,b⟩; rfl })).trans
    (LinearIsometryEquiv.piLpCurry ℂ 2 (fun _ _ => ℂ))

theorem curry_clean (v : EuclideanSpace ℂ B) :
    curry (clean (D := D) v) = WithLp.toLp 2 (fun q : Fin D × Fin D =>
      if q = (0,0) then v else 0) := by
  ext ⟨a,z⟩ b
  simp only [curry, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.piLpCurry_apply, PiLp.toLp_apply]
  change clean v (b,a,z) = _
  rw [clean_coordinate]
  by_cases ha : a = 0 <;> by_cases hz : z = 0 <;> simp [ha,hz]

theorem clean_norm (v : EuclideanSpace ℂ B) : ‖clean (D := D) v‖ = ‖v‖ := by
  have h : ‖clean (D := D) v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← (curry (B := B) (D := D)).norm_map, curry_clean, PiLp.norm_sq_eq_of_L2]
    have ht (q : Fin D × Fin D) : ‖if q = (0,0) then v else 0‖ ^ 2 =
        if q = (0,0) then ‖v‖ ^ 2 else 0 := by split_ifs <;> simp
    simp_rw [PiLp.toLp_apply, ht]
    simp
  nlinarith [norm_nonneg (clean (D := D) v), norm_nonneg v]

/-- The ancilla extension of any oracle-independent source unitary. -/
def freeExtension (U : EuclideanSpace ℂ B ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) :
    QuerySpace B D ≃ₗᵢ[ℂ] QuerySpace B D :=
  ((curry (B := B) (D := D)).trans (withWorkspace (ι := Fin D × Fin D) U)).trans
    (curry (B := B) (D := D)).symm

@[simp] theorem freeExtension_clean (U : EuclideanSpace ℂ B ≃ₗᵢ[ℂ] EuclideanSpace ℂ B)
    (v : EuclideanSpace ℂ B) : freeExtension (D := D) U (clean v) = clean (U v) := by
  apply (curry (B := B) (D := D)).injective
  simp only [freeExtension, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, curry_clean]
  ext q
  by_cases hq : q = (0,0) <;> simp [withWorkspace, hq]

@[simp] theorem Program.operation_append (w z : Program B D) (f : Fin D → Fin D) :
    (w ++ z).operation f = (w.operation f).trans (z.operation f) := by
  induction w with
  | nil => rfl
  | cons g w hw => simp only [List.cons_append, Program.operation, hw]; rfl

@[simp] theorem Program.queries_append (w z : Program B D) :
    (w ++ z).queries = w.queries + z.queries := by simp [Program.queries]

def Gate.inverse : Gate B D → Gate B D
  | .free U => .free U.symm
  | .query .forward => .query .inverse
  | .query .inverse => .query .forward

@[simp] theorem Gate.operation_inverse (g : Gate B D) (f : Fin D → Fin D) :
    g.inverse.operation f = (g.operation f).symm := by
  cases g with
  | free U => rfl
  | query q => cases q <;> rfl

def Program.inverse (w : Program B D) : Program B D := w.reverse.map Gate.inverse

@[simp] theorem Program.operation_inverse (w : Program B D) (f : Fin D → Fin D) :
    w.inverse.operation f = (w.operation f).symm := by
  induction w with
  | nil => rfl
  | cons g w hw =>
    unfold Program.inverse at hw
    simp only [Program.inverse, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, Program.operation_append, Program.operation, Gate.operation_inverse,
      hw, LinearIsometryEquiv.symm_trans]
    rfl

@[simp] theorem Program.queries_inverse (w : Program B D) : w.inverse.queries = w.queries := by
  simp only [Program.inverse, Program.queries, List.map_map, List.map_reverse, List.sum_reverse]
  congr 2
  funext g
  cases g with
  | free U => rfl
  | query q => cases q <;> rfl

/-- A genuine standard-query implementation on a clean ancilla subspace. -/
structure Implements (U : (Fin D → Fin D) → EuclideanSpace ℂ B ≃ₗᵢ[ℂ] EuclideanSpace ℂ B)
    (N : ℕ) where
  program : Program B D
  count : program.queries = N
  correct : ∀ f v, program.operation f (clean v) = clean (U f v)

def Implements.free (U : EuclideanSpace ℂ B ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) :
    Implements (D := D) (fun _ => U) 0 where
  program := [.free (freeExtension U)]
  count := rfl
  correct := by intro f v; exact freeExtension_clean U v

def Implements.trans {U V} {m n : ℕ} (hU : Implements (B := B) (D := D) U m)
    (hV : Implements V n) : Implements (fun f => (U f).trans (V f)) (m+n) where
  program := hU.program ++ hV.program
  count := by rw [Program.queries_append, hU.count, hV.count]
  correct := by intro f v; rw [Program.operation_append]; simp [hU.correct, hV.correct]

def Implements.inverse {U} {m : ℕ} (hU : Implements (B := B) (D := D) U m) :
    Implements (fun f => (U f).symm) m where
  program := hU.program.inverse
  count := by rw [Program.queries_inverse, hU.count]
  correct := by
    intro f v
    have h := hU.correct f ((U f).symm v)
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    rw [Program.operation_inverse]
    exact (hU.program.operation f).injective (by simpa using h.symm)

/-- Write a legal address into an initially clean address register. -/
def address (a : B → Fin D) : Equiv.Perm (QueryBasis B D) where
  toFun := fun ⟨b,r,z⟩ => (b,r + a b,z)
  invFun := fun ⟨b,r,z⟩ => (b,r - a b,z)
  left_inv := by rintro ⟨b,r,z⟩; simp
  right_inv := by rintro ⟨b,r,z⟩; simp

/-- Known action controlled by the value in the function target. -/
def act (A : Fin D → Equiv.Perm B) : Equiv.Perm (QueryBasis B D) where
  toFun := fun ⟨b,r,z⟩ => (A z b,r,z)
  invFun := fun ⟨b,r,z⟩ => ((A z).symm b,r,z)
  left_inv := by rintro ⟨b,r,z⟩; simp
  right_inv := by rintro ⟨b,r,z⟩; simp

/-- The exact two-query standard-function circuit. -/
def compile (a : B → Fin D) (A : Fin D → Equiv.Perm B) : Program B D :=
  [.free (lift (address a)), .query .forward, .free (lift (act A)),
    .query .inverse, .free (lift (address a).symm)]

@[simp] theorem compile_queries (a : B → Fin D) (A : Fin D → Equiv.Perm B) :
    (compile a A).queries = 2 := rfl

/-- Correctness on *all* source states; the action must retain its query
address so the scratch can be uncomputed. No simulation/cost claim is a premise. -/
theorem compile_clean (a : B → Fin D) (A : Fin D → Equiv.Perm B)
    (hA : ∀ z b, a (A z b) = a b) (f : Fin D → Fin D)
    (t : Equiv.Perm B) (ht : ∀ b, t b = A (f (a b)) b) (v : EuclideanSpace ℂ B) :
    (compile a A).operation f (clean v) = clean (lift t v) := by
  let e := (((address a).trans (standard f)).trans (act A)).trans
    ((standard f).symm.trans (address a).symm)
  have he : ∀ b, e (b,(0,0)) = (t b,(0,0)) := by
    intro b
    simp [e, address, standard, act, Equiv.trans_apply, hA, ht]
  have hop : (compile a A).operation f = lift e := by
    simp only [compile, Program.operation, Gate.operation, queryUnitary]
    simp only [lift, LinearIsometryEquiv.piLpCongrLeft_symm]
    ext x b
    rfl
  rw [hop]
  exact clean_lift e t he v

/-! The padded evaluation used in equation (22). -/
variable {R : ℕ}

def collisionAddress : Basis D R → Fin D
  | .inl _ => 0
  | .inr (_,x,_) => dummy x

def collisionAction (z : Fin D) : Equiv.Perm (Basis D R) where
  toFun := Sum.map id (fun ⟨o,x,s⟩ => (o,x,s+z))
  invFun := Sum.map id (fun ⟨o,x,s⟩ => (o,x,s-z))
  left_inv := by intro b; rcases b with u | ⟨o,x,s⟩ <;> simp
  right_inv := by intro b; rcases b with u | ⟨o,x,s⟩ <;> simp

/-- A padded, legal-input evaluation (including the flag) uses two actual
standard queries. The clean-state identity lifts to arbitrary superpositions. -/
theorem evaluate_two_queries (f : Fin D → Fin D) (v : Space D R) :
    (compile collisionAddress collisionAction).operation f (clean v) =
      clean (lift (evaluate f) v) := by
  apply compile_clean
  · intro z b; rcases b with u | ⟨o,x,s⟩ <;> rfl
  · intro b; rcases b with u | ⟨o,x,s⟩ <;> rfl

/-- Controlled padded action is still an oracle-independent reversible gate. -/
def controlledAction (z : Fin D) : Equiv.Perm (Bool × Basis D R) where
  toFun := fun ⟨c,b⟩ => (c, if c then collisionAction z b else b)
  invFun := fun ⟨c,b⟩ => (c, if c then (collisionAction z).symm b else b)
  left_inv := by rintro ⟨c,b⟩; cases c <;> simp
  right_inv := by rintro ⟨c,b⟩; cases c <;> simp

def controlledEvaluate (f : Fin D → Fin D) : Equiv.Perm (Bool × Basis D R) where
  toFun := fun ⟨c,b⟩ => (c, if c then evaluate f b else b)
  invFun := fun ⟨c,b⟩ => (c, if c then (evaluate f).symm b else b)
  left_inv := by rintro ⟨c,b⟩; cases c <;> simp
  right_inv := by rintro ⟨c,b⟩; cases c <;> simp

/-- Controlling an evaluation needs no controlled primitive oracle: compute
unconditionally, conditionally act, then uncompute, at cost two. -/
theorem controlledEvaluate_two_queries (f : Fin D → Fin D)
    (v : EuclideanSpace ℂ (Bool × Basis D R)) :
    (compile (fun b => collisionAddress b.2) controlledAction).operation f (clean v) =
      clean (lift (controlledEvaluate f) v) := by
  apply compile_clean
  · intro z ⟨c,b⟩; cases c <;> rcases b with u | ⟨o,x,s⟩ <;> rfl
  · intro ⟨c,b⟩; cases c <;> rcases b with u | ⟨o,x,s⟩ <;> rfl

/-- Exact program witness for the padded evaluation on the entire space. -/
def evaluationImplementation : Implements (D := D) (fun f => lift (evaluate (R := R) f)) 2 where
  program := compile collisionAddress collisionAction
  count := compile_queries _ _
  correct := evaluate_two_queries

/-- The complete preparation, rather than only its prepared state, is
implemented using four standard function queries. -/
def preparationImplementation : Implements (D := D) (fun f => unitary (R := R) f) 4 := by
  let h := (((Implements.free (knownPreparation (D := D) (R := R))).trans
    (evaluationImplementation (D := D) (R := R))).trans
    (Implements.free (lift (copy (D := D) (R := R))))).trans
    (evaluationImplementation (D := D) (R := R)).inverse
  refine ⟨h.program, h.count, ?_⟩
  intro f v
  have he : (((knownPreparation (D := D) (R := R)).trans (lift (evaluate f))).trans
      (lift copy)).trans (lift (evaluate f)).symm = unitary f := by
    simp only [PUT.CollisionCircuit.unitary, computeCopyUncompute, lift_trans, lift,
      LinearIsometryEquiv.piLpCongrLeft_symm]
    ext x b
    rfl
  simpa only [he] using h.correct f v

/-- Reversing the full preparation does not change the query count. -/
def inversePreparationImplementation :
    Implements (D := D) (fun f => (unitary (R := R) f).symm) 4 :=
  preparationImplementation.inverse

/-- Reindex a controlled source register as an explicit qubit tensor factor. -/
def controlCurry : EuclideanSpace ℂ (Bool × B) ≃ₗᵢ[ℂ] Register Bool (EuclideanSpace ℂ B) :=
  (lift (show (Bool × B) ≃ (c : Bool) × B from
    { toFun := fun ⟨c,b⟩ => ⟨c,b⟩
      invFun := fun ⟨c,b⟩ => (c,b)
      left_inv := by rintro ⟨c,b⟩; rfl
      right_inv := by rintro ⟨c,b⟩; rfl })).trans
    (LinearIsometryEquiv.piLpCurry ℂ 2 (fun _ _ => ℂ))

def controlUnitary (U : EuclideanSpace ℂ B ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) :
    EuclideanSpace ℂ (Bool × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × B) :=
  ((controlCurry (B := B)).trans (controlled U)).trans (controlCurry (B := B)).symm

def controlPermutation (e : Equiv.Perm B) : Equiv.Perm (Bool × B) where
  toFun := fun ⟨c,b⟩ => (c, if c then e b else b)
  invFun := fun ⟨c,b⟩ => (c, if c then e.symm b else b)
  left_inv := by rintro ⟨c,b⟩; cases c <;> simp
  right_inv := by rintro ⟨c,b⟩; cases c <;> simp

@[simp] theorem control_lift (e : Equiv.Perm B) : controlUnitary (lift e) =
    lift (controlPermutation e) := by
  ext v ⟨c,b⟩
  cases c <;> rfl

set_option maxRecDepth 4096 in
@[simp] theorem control_trans (U V : EuclideanSpace ℂ B ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) :
    controlUnitary (U.trans V) = (controlUnitary U).trans (controlUnitary V) := by
  ext v ⟨c,b⟩
  cases c <;> rfl

@[simp] theorem control_inverse (U : EuclideanSpace ℂ B ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) :
    controlUnitary U.symm = (controlUnitary U).symm := by
  simp only [controlUnitary, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.symm_symm, controlled_inverse]
  rfl

def controlledEvaluationImplementation :
    Implements (D := D) (fun f => controlUnitary (lift (evaluate (R := R) f))) 2 where
  program := compile (fun b => collisionAddress b.2) controlledAction
  count := compile_queries _ _
  correct := by intro f v; rw [control_lift]; exact controlledEvaluate_two_queries f v

/-- Controlling all gates of the preparation preserves the four-query cost;
all primitive queries are standard unconditional additive function queries. -/
def controlledPreparationImplementation :
    Implements (D := D) (fun f => controlUnitary (unitary (R := R) f)) 4 := by
  let h := (((Implements.free (controlUnitary (knownPreparation (D := D) (R := R)))).trans
    (controlledEvaluationImplementation (D := D) (R := R))).trans
    (Implements.free (controlUnitary (lift (copy (D := D) (R := R)))))).trans
    (controlledEvaluationImplementation (D := D) (R := R)).inverse
  refine ⟨h.program, h.count, ?_⟩
  intro f v
  have he : (((controlUnitary (knownPreparation (D := D) (R := R))).trans
      (controlUnitary (lift (evaluate f)))).trans (controlUnitary (lift copy))).trans
      (controlUnitary (lift (evaluate f))).symm = controlUnitary (unitary f) := by
    rw [← control_inverse, ← control_trans, ← control_trans, ← control_trans]
    congr 1
    simp only [PUT.CollisionCircuit.unitary, computeCopyUncompute, lift_trans, lift,
      LinearIsometryEquiv.piLpCongrLeft_symm]
    ext x b
    rfl
  simpa only [he] using h.correct f v

def controlledInversePreparationImplementation :
    Implements (D := D) (fun f => (controlUnitary (unitary (R := R) f)).symm) 4 :=
  controlledPreparationImplementation.inverse

end PUT.CollisionQuerySimulation

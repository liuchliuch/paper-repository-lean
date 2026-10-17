import Paper19.NatOrbits
import Paper19.NatReductions
import Paper19.UniformAllInputs

namespace Paper19
open Infinitary

noncomputable def structureA (T : InputTree) : NatModel := natModel T.rootCompletion false
noncomputable def structureB (T : InputTree) : NatModel := natModel T.rootCompletion true

theorem structures_computable (T : InputTree) (hT : ComputablePred T.mem) :
    (structureA T).Computable ∧ (structureB T).Computable :=
  ⟨natModel_computable _ (T.rootCompletion_computable hT) false,
   natModel_computable _ (T.rootCompletion_computable hT) true⟩

theorem structures_isomorphic_iff (T : InputTree) :
    Nonempty (NatIso (structureA T) (structureB T)) ↔ ∃ o, T.IsPath o := by
  constructor
  · rintro ⟨f⟩
    let c : PresentationIso T.rootCompletion (Carrier.zeroVec 0) Carrier.rootOne := f.toCarrier
    exact ⟨presentationToPath c,(T.path_iff_rootCompletion _).mpr (presentationToPath_correct c)⟩
  · rintro ⟨o,ho⟩
    exact ⟨(pathToPresentation ((T.path_iff_rootCompletion o).mp ho)).toNatIso⟩

/-- The original three-clause conclusion, on the full input class including
empty trees and the domain Nat. The two actual programs are named in the
statement, and their uniform oracle derivations are part of the conclusion. -/
def Theorem1Statement : Prop :=
  UniformConstructionStatement ∧ ∀ (T : InputTree), ComputablePred T.mem →
    ((structureA T).Computable ∧ (structureB T).Computable) ∧
    (∀ (tag : Bool) (m : ℕ) (a : Fin m → ℕ),
      ∃ φ : Formula, ComputablyPresented φ ∧ ∀ b : Fin m → ℕ,
        φ.RealizeNat (natModel T.rootCompletion tag)
          (natTupleEnv (natModel T.rootCompletion tag) b) ↔
            NatTupleOrbit (natModel T.rootCompletion tag) a b) ∧
    (Nonempty (NatIso (structureA T) (structureB T)) ↔ ∃ o, T.IsPath o) ∧
    UniformOracleComputable (forwardNatProgram T.rootCompletion) ∧
    UniformOracleComputable (backwardNatProgram T.rootCompletion) ∧
    (∀ (o : Stream) (ho : T.IsPath o) (n : ℕ),
      forwardNatProgram T.rootCompletion o n =
        (PresentationIso.toNatIso (a := false) (b := true)
          (pathToPresentation ((T.path_iff_rootCompletion o).mp ho))).map n) ∧
    (∀ f : NatIso (structureA T) (structureB T),
      T.IsPath (backwardNatProgram T.rootCompletion f.map))

/-- Theorem 1, without orbit, bridge, rank-bound or isomorphism-existence
conclusions supplied as premises. -/
theorem theorem_1 : Theorem1Statement := by
  refine ⟨uniform_construction_all_inputs,?_⟩
  intro T hT
  have hc := T.rootCompletion_computable hT
  exact ⟨structures_computable T hT,
    fun tag m a => all_nat_tuple_orbits _ hc tag m a,
    structures_isomorphic_iff T, forwardNat_uniform _ hc, backwardNat_uniform _ hc,
    fun o ho n => forwardNat_correct ((T.path_iff_rootCompletion o).mp ho) n,
    fun f => (T.path_iff_rootCompletion _).mpr (backwardNat_correct f)⟩

end Paper19

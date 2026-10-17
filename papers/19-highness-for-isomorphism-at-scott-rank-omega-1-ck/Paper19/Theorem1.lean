import Paper19.Spec

namespace Paper19
open Paper19.Spec Paper19.Infinitary

/-- Closed structural and formula conclusion. The complete uniform natural-number presentation theorem is theorem_1
in FullTheorem.lean. -/
theorem theorem1_structural : Thm1_OrbitDefinitions ∧ Thm1_Isomorphic ∧ Thm1_ProgramsCorrect :=
  ⟨fun _ hT tag m a => all_tuple_orbits hT tag m a,
   theorem1_isomorphic, fun _ f => presentationToPath_correct f⟩

end Paper19

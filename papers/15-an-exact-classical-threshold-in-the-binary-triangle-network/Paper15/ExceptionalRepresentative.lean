import Paper15.OrbitSoundness
namespace Paper15

/-- The exceptional canonical word is an explicit symmetry image of (6). -/
theorem exceptional_representative_in_orbit : inExceptionalOrbit (DetTriangle.ofPattern 2889227) := by
  let g : Symmetry := ⟨Equiv.swap 0 1,Equiv.swap 0 1,Equiv.swap 0 1,Equiv.refl _,true⟩
  refine ⟨g,?_⟩
  apply DetTriangle.ext <;> apply RespTable.ext <;> intro i j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [g,Symmetry.apply,valueReindex,applyPerm,flipAll,RespTable.flip,
      DetTriangle.exceptional,DetTriangle.exceptionalTable,DetTriangle.ofPattern,
      signOfBit,bitOf,Equiv.swap_apply_def] <;> decide +kernel

end Paper15

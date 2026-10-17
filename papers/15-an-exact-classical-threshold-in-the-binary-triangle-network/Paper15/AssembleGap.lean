import Paper15.OrbitSoundness
import Paper15.Main

noncomputable section
namespace Paper15
open OrbitCheck

def OrbitCheck.Words.toFinset : Words → Finset Nat
  | .leaf w => {w}
  | .branch l r => l.toFinset ∪ r.toFinset

lemma OrbitCheck.Words.mem_toFinset (t : Words) (w : Nat) : w∈t.toFinset ↔ t.mem w := by
  induction t with
  | leaf a => simp [Words.toFinset,Words.mem]
  | branch l r hl hr => simp [Words.toFinset,Words.mem,hl,hr]

theorem all_response_tables_covered_of_checked
    (all_neighbours_checked : representatives.All HasCheckedNeighbours) : ∀T : DetTriangle,
    ∃r∈representatives.toFinset,∃g : Symmetry,g.apply (DetTriangle.ofPattern r)=T := by
  apply orbit_coverage_from_neighbours
  · have hz : representatives.at 0=0 := by decide +kernel
    exact (representatives.mem_toFinset 0).mpr (hz ▸ representatives.at_mem 0)
  · intro r hr p
    have hm := (representatives.mem_toFinset r).mp hr
    obtain ⟨row,hrow⟩:=Words.all_mem all_neighbours_checked hm
    obtain ⟨s,hs,g,hg⟩:=rowValid_sound hrow p
    exact ⟨s,(representatives.mem_toFinset s).mpr hs,g,hg⟩

/-- Lemma 5. Every deterministic ternary response assignment outside the
exceptional symmetry orbit satisfies the exact 9/25 gap, including all
boundary probability laws. -/
theorem gap_of_checked_trees
    (all_representatives_classified : representatives.All (fun r =>
      GapHolds (DetTriangle.ofPattern r) ∨ inExceptionalOrbit (DetTriangle.ofPattern r)))
    (all_neighbours_checked : representatives.All HasCheckedNeighbours)
    (T : DetTriangle) (hT : ¬inExceptionalOrbit T) : GapHolds T := by
  obtain ⟨r,hr,g,hg⟩:=all_response_tables_covered_of_checked all_neighbours_checked T
  have hc:=Words.all_mem all_representatives_classified ((representatives.mem_toFinset r).mp hr)
  rcases hc with hgap|hexc
  · rw [← hg]
    exact gapHolds_symmetry hgap g
  · exact False.elim (hT (hg ▸ inExceptionalOrbit_symmetry g hexc))

end Paper15

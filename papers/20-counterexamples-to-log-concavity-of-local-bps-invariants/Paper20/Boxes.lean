import Paper20.PartitionHooks
import Mathlib.Combinatorics.Young.YoungDiagram

namespace Paper20
open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def boxesOf (ps : List ℕ) : List (ℕ × ℕ) :=
  ps.zipIdx.flatMap (fun (a,i) => (List.range a).map (fun j => (i,j)))

theorem mem_boxesOf (ps : List ℕ) (i j : ℕ) :
    (i,j) ∈ boxesOf ps ↔ ∃ hi : i < ps.length, j < ps[i] := by
  constructor
  · intro hx
    obtain ⟨⟨a,b⟩, hab, hx⟩ := List.mem_flatMap.mp hx
    dsimp only at hx
    obtain ⟨c, hc, he⟩ := List.mem_map.mp hx
    have hbi : b=i := congrArg Prod.fst he
    have hcj : c=j := congrArg Prod.snd he
    subst b
    subst c
    have hg := List.mk_mem_zipIdx_iff_getElem?.mp hab
    obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp hg
    exact ⟨hi, by simpa only [hget] using List.mem_range.mp hc⟩
  · rintro ⟨hi,hj⟩
    apply List.mem_flatMap.mpr
    refine ⟨(ps[i],i), List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi), ?_⟩
    exact List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩

theorem boxesOf_nodup (ps : List ℕ) : (boxesOf ps).Nodup := by
  unfold boxesOf
  rw [List.nodup_flatMap]
  constructor
  · intro p hp
    exact (List.nodup_range (n := p.1)).map (by intro x y h; exact congrArg Prod.snd h)
  · have hs : ps.zipIdx.Pairwise (fun p q => p.2 ≠ q.2) := by
      have hs := List.nodup_zipIdx_map_snd ps
      change (ps.zipIdx.map Prod.snd).Pairwise (· ≠ ·) at hs
      simpa only [List.pairwise_map] using hs
    apply List.Pairwise.imp _ hs
    intro p q hne x hxp hxq
    obtain ⟨a,ha,he1⟩ := List.mem_map.mp hxp
    obtain ⟨b,hb,he2⟩ := List.mem_map.mp hxq
    exact hne ((congrArg Prod.fst he1).trans (congrArg Prod.fst he2).symm)

theorem boxesOf_toFinset (ps : List ℕ) :
    (boxesOf ps).toFinset = YoungDiagram.cellsOfRowLens ps := by
  ext ⟨i,j⟩
  simp only [List.mem_toFinset, mem_boxesOf, YoungDiagram.mem_cellsOfRowLens]

/-- Every quantity in the executable hook formula ranges over precisely
the boxes of the corresponding Young diagram. -/
theorem hooksOf_eq_boxes_map (ps : List ℕ) :
    hooksOf ps = (boxesOf ps).map (fun (i,j) =>
      ps.getD i 0-j+(ps.filter (· > j)).length-i-1) := by
  unfold hooksOf boxesOf
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro p hp
  rcases p with ⟨a,i⟩
  dsimp only
  rw [List.map_map]
  have he : ps.getD i 0 = a := by
    rw [List.getD_eq_getD_getElem?, List.mk_mem_zipIdx_iff_getElem?.mp hp]
    rfl
  simp only [he, Function.comp_def]

end Paper20

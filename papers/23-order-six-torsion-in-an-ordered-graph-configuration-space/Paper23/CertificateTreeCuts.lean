import Paper23.CertificateCofaceExpansion
import Paper23.CertificateModulo

/-! A finite partition of the actual cochain search tree and the soundness of
its projected, signed sparse transpose. -/
namespace Paper23.CertificateChecks
open Cubical CertificateData

/-- Split a dictionary into subtrees and singleton pivots without losing or
reordering an entry. The depth only controls numerical proof granularity. -/
def cutTree : ℕ → LookupTree → List LookupTree :=
  Nat.rec (fun tree => [tree]) (fun _ rec tree =>
    match tree with
    | .empty => []
    | .node k v left right => rec left ++ [.node k v .empty .empty] ++ rec right)

theorem cutTree_zero (tree : LookupTree) : cutTree 0 tree = [tree] := rfl

theorem cutTree_succ_empty (n : ℕ) : cutTree (n+1) .empty = [] := rfl

theorem cutTree_succ_node (n k : ℕ) (v : ℤ) (left right : LookupTree) :
    cutTree (n+1) (.node k v left right) =
      cutTree n left ++ [.node k v .empty .empty] ++ cutTree n right := rfl

theorem cutTree_entries (fuel : ℕ) (tree : LookupTree) :
    (cutTree fuel tree).flatMap treeEntries = treeEntries tree := by
  induction fuel generalizing tree with
  | zero => simp [cutTree]
  | succ fuel ih =>
    cases tree with
    | empty => rfl
    | node k v left right =>
      simp only [cutTree_succ_node,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
         List.append_nil,treeEntries_node,treeEntries_empty,ih,List.nil_append,List.append_assoc]

/-- Projected cofaces of all finitely supported integral cochain entries. -/
def codeCofaceEntries (xs : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  xs.flatMap fun p => scaleEntries p.2 (codeCofaces (decodeCube p.1))

theorem codeCofaceEntries_sound (xs : List (ℕ × ℤ)) :
    codeChain (codeCofaceEntries xs) = restrictCubes 3 (coBoundary (codeChain xs)) := by
  induction xs with
  | nil => simp [codeCofaceEntries]
  | cons p xs ih =>
    simp only [codeCofaceEntries,List.flatMap_cons,codeChain_append]
    rw [codeChain_scaleEntries,codeCofaces_sound _ (by rfl)]
    change p.2 • restrictCubes 3 (coBoundaryBasis (decodeCube p.1)) +
      codeChain (codeCofaceEntries xs) = _
    rw [ih]
    simp only [codeChain_cons,map_add,map_smul,coBoundary_basis]

noncomputable def codeTreeCofaces (tree : LookupTree) : List (ℕ × ℤ) :=
  codeCofaceEntries (treeEntries tree)

theorem codeTreeCofaces_sound (tree : LookupTree) :
    codeChain (codeTreeCofaces tree) =
      restrictCubes 3 (coBoundary (codeChain (treeEntries tree))) :=
  codeCofaceEntries_sound _

/-- The tree partition denotes precisely the imported finite cochain. -/
theorem phiVector_cut_sum (fuel : ℕ) :
    phiVector = ((cutTree fuel phiTable).map fun tree => codeChain (treeEntries tree)).sum := by
  change codeChain (treeEntries phiTable) = _
  rw [← cutTree_entries fuel phiTable,codeChain_flatMap]

/-- The complete projected transpose is a finite sum of the checked blocks. -/
theorem modular_transpose_cut_sum (fuel : ℕ) :
    reduceChain (restrictCubes 3 (coBoundary phiVector)) =
      ((cutTree fuel phiTable).map fun tree => reduceChain (codeChain (codeTreeCofaces tree))).sum := by
  rw [phiVector_cut_sum fuel]
  simp only [map_list_sum,List.map_map,Function.comp_def,codeTreeCofaces_sound]

end Paper23.CertificateChecks

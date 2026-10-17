import Paper23.CertificateCofaces

/-! A checked sparse-table interpretation. Bounds certify that the imported
search tree is a genuine dictionary with unique keys and no hidden entries. -/
namespace Paper23.CertificateChecks
open Cubical CertificateData

/-- All keys lie in the half-open interval [lo,hi), recursively respecting
both search-tree partitions. -/
noncomputable def treeBounded (lo hi : ℕ) (t : LookupTree) : Bool :=
  LookupTree.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun k _ _ _ left right lo hi =>
      decide (lo ≤ k) && decide (k < hi) && left lo k && right (k+1) hi) t lo hi

theorem treeBounded_empty (lo hi : ℕ) : treeBounded lo hi .empty = true := rfl

theorem treeBounded_node (lo hi k : ℕ) (v : ℤ) (left right : LookupTree) :
    treeBounded lo hi (.node k v left right) =
      (decide (lo ≤ k) && decide (k < hi) && treeBounded lo k left &&
        treeBounded (k+1) hi right) := rfl

noncomputable def treeEntries (t : LookupTree) : List (ℕ × ℤ) :=
  LookupTree.rec [] (fun k v _ _ left right => left ++ [(k,v)] ++ right) t

theorem treeEntries_empty : treeEntries .empty = [] := rfl

theorem treeEntries_node (k : ℕ) (v : ℤ) (left right : LookupTree) :
    treeEntries (.node k v left right) = treeEntries left ++ [(k,v)] ++ treeEntries right := rfl

theorem lookup_empty (n : ℕ) : lookup .empty n = 0 := rfl

theorem lookup_node (key n : ℕ) (value : ℤ) (left right : LookupTree) :
    lookup (.node key value left right) n =
      (if n < key then lookup left n else if n = key then value else lookup right n) := rfl

theorem treeEntries_bounds (lo hi : ℕ) (tree : LookupTree)
    (h : treeBounded lo hi tree = true) :
    ∀ p ∈ treeEntries tree, lo ≤ p.1 ∧ p.1 < hi := by
  induction tree generalizing lo hi with
  | empty => simp [treeEntries]
  | node k v left right ihl ihr =>
    simp only [treeBounded_node,Bool.and_eq_true,decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨hlo,hhi⟩,hl⟩,hr⟩
    intro p hp
    simp only [treeEntries_node,List.mem_append,List.mem_singleton] at hp
    rcases hp with (hp | rfl) | hp
    · have hb := ihl lo k hl p hp
      exact ⟨hb.1, hb.2.trans hhi⟩
    · exact ⟨hlo,hhi⟩
    · have hb := ihr (k+1) hi hr p hp
      exact ⟨by omega,hb.2⟩

/-- Finite evaluation of a dictionary's explicit entries. -/
def entryEvaluation (xs : List (ℕ × ℤ)) (n : ℕ) : ℤ :=
  (xs.map fun p => if p.1 = n then p.2 else 0).sum

theorem entryEvaluation_append (xs ys : List (ℕ × ℤ)) (n : ℕ) :
    entryEvaluation (xs ++ ys) n = entryEvaluation xs n + entryEvaluation ys n := by
  simp [entryEvaluation]

theorem entryEvaluation_zero_of_ne (xs : List (ℕ × ℤ)) (n : ℕ)
    (h : ∀ p ∈ xs, p.1 ≠ n) : entryEvaluation xs n = 0 := by
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha
  simp [h p hp]

/-- Lookup agrees with all explicit entries, proved for arbitrary queries,
including those outside the imported support. -/
theorem lookup_eq_entryEvaluation (lo hi : ℕ) (tree : LookupTree)
    (h : treeBounded lo hi tree = true) (n : ℕ) :
    lookup tree n = entryEvaluation (treeEntries tree) n := by
  induction tree generalizing lo hi with
  | empty => simp [lookup,treeEntries,entryEvaluation]
  | node k v left right ihl ihr =>
    simp only [treeBounded_node,Bool.and_eq_true,decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨hlo,hhi⟩,hl⟩,hr⟩
    have leftZero (hn : k ≤ n) : entryEvaluation (treeEntries left) n = 0 := by
      apply entryEvaluation_zero_of_ne
      intro p hp heq
      have hb := treeEntries_bounds lo k left hl p hp
      omega
    have rightZero (hn : n ≤ k) : entryEvaluation (treeEntries right) n = 0 := by
      apply entryEvaluation_zero_of_ne
      intro p hp heq
      have hb := treeEntries_bounds (k+1) hi right hr p hp
      omega
    simp only [treeEntries_node,entryEvaluation_append]
    by_cases hn : n < k
    · rw [lookup_node,if_pos hn,ihl lo k hl, rightZero (by omega)]
      simp [entryEvaluation,ne_of_gt hn]
    · by_cases heq : n = k
      · subst n
        rw [lookup_node,if_neg (Nat.lt_irrefl _),if_pos rfl,leftZero (by omega),rightZero (by omega)]
        simp [entryEvaluation]
      · rw [lookup_node,if_neg hn,if_neg heq,ihr (k+1) hi hr,leftZero (by omega)]
        simp [entryEvaluation,Ne.symm heq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The imported phi table passes a complete kernel check of every search-tree
partition and the base-71 four-coordinate key bound. -/
theorem phiTable_bounded : treeBounded 0 25411681 phiTable = true := by decide +kernel

/-- The sparse vector represented by the actual cochain dictionary. -/
noncomputable def phiVector : RawChain := codeChain (treeEntries phiTable)

theorem encodeCell_decodeCell (n : ℕ) (hn : n < 71) :
    encodeCell (decodeCell n) = n := by
  by_cases h : n < 32
  · simp [decodeCell,encodeCell,h]
  · have he : n - 32 < 39 := by omega
    simp only [decodeCell,dif_neg h,encodeCell,Nat.mod_eq_of_lt he]
    omega

/-- The base-71 encoder and decoder are inverse throughout the certified key range. -/
theorem encodeCube_decodeCube (n : ℕ) (hn : n < 25411681) :
    encodeCube (decodeCube n) = n := by
  unfold decodeCube encodeCube
  simp only [List.foldl_cons,List.foldl_nil,Nat.mul_zero,Nat.zero_add]
  rw [encodeCell_decodeCell _ (Nat.mod_lt _ (by decide)),
    encodeCell_decodeCell _ (Nat.mod_lt _ (by decide)),
    encodeCell_decodeCell _ (Nat.mod_lt _ (by decide)),
    encodeCell_decodeCell _ (Nat.mod_lt _ (by decide))]
  omega

theorem codeChain_coeff (xs : List (ℕ × ℤ)) (c : RawCube) :
    codeChain xs c = (xs.map fun p => if decodeCube p.1 = c then p.2 else 0).sum := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    simp only [codeChain_cons,Finsupp.add_apply,Finsupp.smul_apply,basis,
      Finsupp.single_apply,smul_eq_mul,List.map_cons,List.sum_cons,ih]
    by_cases h : decodeCube p.1 = c <;> simp [h]

/-- The imported sparse vector is exactly the actual lookup cochain on every
four-particle cube. This identifies all queries, not just the cycle support. -/
theorem phiVector_coeff (c : RawCube) (hlen : c.length = 4) :
    phiVector c = phiValue c := by
  change codeChain (treeEntries phiTable) c = lookup phiTable (encodeCube c)
  rw [codeChain_coeff,lookup_eq_entryEvaluation 0 25411681 phiTable phiTable_bounded]
  unfold entryEvaluation
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have hb := treeEntries_bounds 0 25411681 phiTable phiTable_bounded p hp
  have hi : decodeCube p.1 = c ↔ p.1 = encodeCube c := by
    constructor
    · intro h
      have he := congrArg encodeCube h
      rwa [encodeCube_decodeCube p.1 hb.2] at he
    · intro h
      rw [h,decodeCube_encodeCube c hlen]
  simp only [hi]

end Paper23.CertificateChecks

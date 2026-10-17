import Paper08.FPTASProgram
import Paper08.AntidiagonalCost
import Paper08.LowDegreeDiscreteCost
import Paper08.SchoolbookArithmetic

/-!
# Discrete work of the actual support and quadrature loops

Every charge below is a sum over an actual finite source, before images or
filters remove duplicates. Coordinate keys are explicit lists. Sorting uses
the source mergesort trace proved in `LowDegreeDiscreteCost`, uniformly in the
representation of each finite set. Linear scans, copying and comparisons are
charged by the binary words that they visit.
-/
open scoped BigOperators
namespace Paper08.FPTASDiscreteCost
open FPTASAlgorithm EfficientSupports Enumeration CellGrid RationalQuadrature
open LowDegreeDiscreteCost PrimitiveProgram

/-- Iteration and source sorting, with the actual key and body of each item. -/
def loopWork {α : Type*} (S : Finset α) (key : α → List ℕ) (body : α → ℕ) : ℕ :=
  sortCharge S key + ∑ x ∈ S, (keyBits (key x) + body x + 1)

theorem loopWork_le {α : Type*} (S : Finset α) (key : α → List ℕ) (body : α → ℕ)
    {Q D W : ℕ} (hQ : S.card ≤ Q) (hD : ∀ x ∈ S, keyBits (key x) ≤ D)
    (hW : ∀ x ∈ S, body x ≤ W) :
    loopWork S key body ≤ Q^2*(2*Q*D+6)+Q*(D+W+1) := by
  have hs := sortCharge_le S key hD
  have hb : (∑ x ∈ S, (keyBits (key x) + body x + 1)) ≤ S.card*(D+W+1) := by
    calc
      _ ≤ ∑ _x ∈ S, (D+W+1) := Finset.sum_le_sum (fun x hx => by
        have hd := hD x hx; have hw := hW x hx; omega)
      _ = _ := by simp
  unfold loopWork
  apply Nat.add_le_add (hs.trans ?_) (hb.trans (Nat.mul_le_mul_right _ hQ))
  exact Nat.mul_le_mul (Nat.pow_le_pow_left hQ 2) (by nlinarith)

/-- All comparisons used to intersect the two stored scopes. -/
def scopeIntersectionWork {n : ℕ} (A B : Finset (Fin n)) : ℕ :=
  ∑ a ∈ A, ∑ b ∈ B, (a.val.size+b.val.size+2)

lemma scopeIntersectionWork_le {n r : ℕ} (A B : Finset (Fin n))
    (hA : A.card ≤ r) (hB : B.card ≤ r) :
    scopeIntersectionWork A B ≤ r*r*(2*n+2) := by
  have hh : scopeIntersectionWork A B ≤ A.card*B.card*(2*n+2) := by
    unfold scopeIntersectionWork
    calc
      _ ≤ ∑ _a ∈ A, ∑ _b ∈ B, (2*n+2) := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        have ha' := index_size_le a; have hb' := index_size_le b
        omega
      _ = _ := by simp; ring
  exact hh.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul hA hB))

/-- The graph constructor examines every ordered pair of factor occurrences. -/
def graphWork {n m : ℕ} (scopes : Fin m → Finset (Fin n)) : ℕ :=
  ∑ e : Fin m, ∑ f : Fin m,
    (e.val.size+f.val.size+2+scopeIntersectionWork (scopes e) (scopes f))

theorem graphWork_le {n m r : ℕ} (scopes : Fin m → Finset (Fin n))
    (hs : ∀ e, (scopes e).card ≤ r) :
    graphWork scopes ≤ m*m*(2*m+2+r*r*(2*n+2)) := by
  unfold graphWork
  calc
    _ ≤ ∑ _e : Fin m, ∑ _f : Fin m, (2*m+2+r*r*(2*n+2)) := by
      apply Finset.sum_le_sum
      intro e he
      apply Finset.sum_le_sum
      intro f hf
      have he' := index_size_le e; have hf' := index_size_le f
      have hi := scopeIntersectionWork_le (scopes e) (scopes f) (hs e) (hs f)
      omega
    _ = _ := by simp; ring

/-- A sorted neighbor lookup charges sorting and the actual source scan. -/
def lookupWork {m : ℕ} (N : Fin m → Finset (Fin m)) (u : Fin m) : ℕ :=
  loopWork (N u) indexKey (fun v => v.val.size+u.val.size+2)

def lookupBound (m : ℕ) : ℕ := m^2*(2*m*(m+2)+6)+m*(3*m+5)

lemma lookupWork_le {m : ℕ} (N : Fin m → Finset (Fin m)) (u : Fin m) :
    lookupWork N u ≤ lookupBound m := by
  have hh := loopWork_le (N u) indexKey (fun v => v.val.size+u.val.size+2)
    (Q := m) (D := m+2) (W := 2*m+2)
    (by simpa using Finset.card_le_univ (N u)) (fun v _ => indexKey_bits_le v) (fun v _ => by
      dsimp only
      have hv := index_size_le v; have hu := index_size_le u; omega)
  simpa only [lookupWork, lookupBound, show m+2+(2*m+2)+1=3*m+5 by omega] using hh

/-- Actual pairwise scans used when merging decoded finite vertex sets. -/
def unionWork {m : ℕ} (A B : Finset (Fin m)) : ℕ :=
  ∑ a ∈ A, ∑ b ∈ B, (a.val.size+b.val.size+2)

lemma unionWork_le {m : ℕ} (A B : Finset (Fin m)) :
    unionWork A B ≤ m*m*(2*m+2) :=
  scopeIntersectionWork_le A B (by simpa using Finset.card_le_univ A)
    (by simpa using Finset.card_le_univ B)

/-- The first-child/next-sibling decoder is traversed on its actual tree.
Each node charges its neighbor lookup, set union and insertion scans. -/
def forestWork {m d : ℕ} (N : Fin m → Finset (Fin m)) (root : Fin m) :
    Tree (Fin d) → ℕ
  | .nil => 0
  | .node i l r =>
    let v := next N d root i
    let A := forestVertices (next N d) v l
    let B := forestVertices (next N d) root r
    forestWork N v l + forestWork N root r + lookupWork N root +
      unionWork A B + unionWork {v} (A ∪ B) + 1

def forestNodeBound (m : ℕ) : ℕ := lookupBound m+2*(m*m*(2*m+2))+1

theorem forestWork_le {m d : ℕ} (N : Fin m → Finset (Fin m))
    (root : Fin m) (t : Tree (Fin d)) :
    forestWork N root t ≤ t.numNodes*forestNodeBound m := by
  induction t generalizing root with
  | nil => simp [forestWork]
  | node i l r hl hr =>
    have hlook := lookupWork_le N root
    have hu := unionWork_le (forestVertices (next N d) (next N d root i) l)
      (forestVertices (next N d) root r)
    have hi := unionWork_le {next N d root i}
      (forestVertices (next N d) (next N d root i) l ∪ forestVertices (next N d) root r)
    have hleft := hl (next N d root i)
    have hright := hr root
    dsimp only [forestWork, Tree.numNodes]
    dsimp [forestNodeBound]
    dsimp [forestNodeBound] at hleft hright
    nlinarith

/-- Source roots and forest codes are charged before the image is deduplicated. -/
def candidateWork {m : ℕ} (N : Fin m → Finset (Fin m)) (d k : ℕ) : ℕ :=
  ∑ root : Fin m, ∑ t ∈ forestCodes d k,
    (forestWork N root t + unionWork {root} (forestVertices (next N d) root t) + 1)

def candidateBound (m d k : ℕ) : ℕ :=
  m*(4*d)^k*(k*forestNodeBound m+m*m*(2*m+2)+1)

theorem candidateWork_le {m d k : ℕ} (N : Fin m → Finset (Fin m)) :
    candidateWork N d k ≤ candidateBound m d k := by
  unfold candidateWork
  calc
    _ ≤ ∑ _root : Fin m, ∑ _t ∈ forestCodes d k,
        (k*forestNodeBound m+m*m*(2*m+2)+1) := by
      apply Finset.sum_le_sum
      intro root hroot
      apply Finset.sum_le_sum
      intro t ht
      have hf := forestWork_le N root t
      have hn := EfficientSupports.forest_numNodes ht
      have hu := unionWork_le {root} (forestVertices (next N d) root t)
      rw [hn] at hf
      omega
    _ = m*(forestCodes d k).card*(k*forestNodeBound m+m*m*(2*m+2)+1) := by simp; ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left m (card_forestCodes_le d k))

/-- Key of the exact support/subset pair used by the arithmetic program. -/
def pairKey {m : ℕ} (AB : Finset (Fin m) × Finset (Fin m)) : List ℕ :=
  finsetKey AB.1 ++ finsetKey AB.2

lemma keyBits_append (x y : List ℕ) : keyBits (x++y) = keyBits x+keyBits y-1 := by
  simp [keyBits]
  omega

lemma pairKey_bits_le {m : ℕ} (AB : Finset (Fin m) × Finset (Fin m)) :
    keyBits (pairKey AB) ≤ 4*m+1 := by
  have ha := finsetKey_bits_le AB.1
  have hb := finsetKey_bits_le AB.2
  rw [pairKey, keyBits_append]
  omega

/-- Each retained candidate generates its own subsets, using binary membership
keys for duplicate checks and later traversal. -/
def subsetWork {m : ℕ} (A : Finset (Fin m)) : ℕ :=
  loopWork A.powerset finsetKey (fun B => keyBits (finsetKey A)+keyBits (finsetKey B)+1)

lemma subsetWork_le {m s : ℕ} (A : Finset (Fin m)) (hA : A.card ≤ s) :
    subsetWork A ≤ (2^s)^2*(2*2^s*(2*m+1)+6)+2^s*(6*m+5) := by
  have hh := loopWork_le A.powerset finsetKey
    (fun B => keyBits (finsetKey A)+keyBits (finsetKey B)+1)
    (Q := 2^s) (D := 2*m+1) (W := 4*m+3) ?_ ?_ ?_
  · simpa only [subsetWork, show 2*m+1+(4*m+3)+1=6*m+5 by omega] using hh
  · rw [Finset.card_powerset]
    exact Nat.pow_le_pow_right (by decide) hA
  · exact fun B _ => finsetKey_bits_le B
  · intro B hB
    dsimp only
    have ha := finsetKey_bits_le A; have hb := finsetKey_bits_le B
    omega

/-- Complete support-source work at a fixed forest size. -/
def supportSizeWork {m : ℕ} (N : Fin m → Finset (Fin m)) (d k : ℕ) : ℕ :=
  candidateWork N d k +
    ∑ A ∈ candidateSets (next N d) k, (subsetWork A+keyBits (finsetKey A)+1)

def supportSizeBound (m d s : ℕ) : ℕ :=
  candidateBound m d s + m*(4*d)^s*
    ((2^(s+1))^2*(2*2^(s+1)*(2*m+1)+6)+2^(s+1)*(6*m+5)+2*m+2)

theorem supportSizeWork_le {m d k s : ℕ} (N : Fin m → Finset (Fin m))
    (hd : 1 ≤ d) (hk : k ≤ s) : supportSizeWork N d k ≤ supportSizeBound m d s := by
  have hc := candidateWork_le (d := d) (k := k) N
  have hsubset : ∀ A ∈ candidateSets (next N d) k,
      subsetWork A+keyBits (finsetKey A)+1 ≤
      (2^(s+1))^2*(2*2^(s+1)*(2*m+1)+6)+2^(s+1)*(6*m+5)+2*m+2 := by
    intro A hA
    have hcard : A.card ≤ s+1 := (candidate_card_le _ hA).trans (by omega)
    have hh := subsetWork_le A hcard
    have hb := finsetKey_bits_le A
    omega
  have hsum := Finset.sum_le_sum hsubset
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hcount : (candidateSets (next N d) k).card ≤ m*(4*d)^s := by
    apply (card_candidateSets_le (next N d) k).trans
    simpa using Nat.mul_le_mul_left m (Nat.pow_le_pow_right (by omega : 0 < 4*d) hk)
  have hcb : candidateBound m d k ≤ candidateBound m d s := by
    unfold candidateBound
    gcongr
    omega
  unfold supportSizeWork supportSizeBound
  exact Nat.add_le_add (hc.trans hcb) (hsum.trans (Nat.mul_le_mul_right _ hcount))

/-- Structural scans visit the actual tree nodes and their binary labels. -/
def treeWordWork {d : ℕ} : Tree (Fin d) → ℕ
  | .nil => 1
  | .node i l r => i.val.size+2+treeWordWork l+treeWordWork r

lemma treeWordWork_le {d : ℕ} (t : Tree (Fin d)) :
    treeWordWork t ≤ (2*t.numNodes+1)*(d+2) := by
  induction t with
  | nil => simp [treeWordWork]
  | node i l r hl hr =>
    have hi := index_size_le i
    dsimp only [treeWordWork, Tree.numNodes]
    nlinarith

/-- One cached labelled-forest generation step, directly over actual source
triples of a label and two previously generated subtrees. -/
def codeStep (d : ℕ) (table : List (Finset (Tree (Fin d)))) (k : ℕ) :
    Finset (Tree (Fin d)) :=
  (Finset.antidiagonal k).biUnion fun ij =>
    ((Finset.univ : Finset (Fin d)) ×ˢ
      (table.getD ij.1 ∅ ×ˢ table.getD ij.2 ∅)).map (nodeEmbedding d)

lemma mem_forestCodes_iff {d k : ℕ} (t : Tree (Fin d)) :
    t ∈ forestCodes d k ↔ t.numNodes = k :=
  ⟨EfficientSupports.forest_numNodes, mem_forestCodes t⟩

/-- The cached step enumerates precisely the same labelled trees as the
original shape/labeling construction. -/
theorem codeStep_eq (d k : ℕ) (table : List (Finset (Tree (Fin d))))
    (h : ∀ i, i ≤ k → table.getD i ∅ = forestCodes d i) :
    codeStep d table k = forestCodes d (k+1) := by
  ext t
  rw [mem_forestCodes_iff]
  constructor
  · intro ht
    obtain ⟨ij, hij, ht'⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ht'
    have hij' := Finset.mem_antidiagonal.mp hij
    have hleft := (Finset.mem_product.mp (Finset.mem_product.mp hx).2).1
    have hright := (Finset.mem_product.mp (Finset.mem_product.mp hx).2).2
    rw [h ij.1 (by omega), mem_forestCodes_iff] at hleft
    rw [h ij.2 (by omega), mem_forestCodes_iff] at hright
    simpa only [nodeEmbedding, Function.Embedding.coeFn_mk, Tree.numNodes, hleft, hright] using
      congrArg (fun a : ℕ => a+1) hij'
  · intro ht
    cases t with
    | nil => simp at ht
    | node i l r =>
      have hij : l.numNodes+r.numNodes = k := by simpa using Nat.add_right_cancel ht
      apply Finset.mem_biUnion.mpr
      refine ⟨(l.numNodes,r.numNodes), Finset.mem_antidiagonal.mpr hij, ?_⟩
      apply Finset.mem_map.mpr
      refine ⟨(i,l,r), ?_, rfl⟩
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_univ _, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
      · rw [h l.numNodes (by omega)]
        exact mem_forestCodes l rfl
      · rw [h r.numNodes (by omega)]
        exact mem_forestCodes r rfl

/-- The generation trace charges actual table lookups, source triples, tree
copies, and all-pairs duplicate checking of the generated trees. -/
def codeStepWork (d : ℕ) (table : List (Finset (Tree (Fin d)))) (k : ℕ) : ℕ :=
  (∑ ij ∈ Finset.antidiagonal k,
    (2*(table.length+1)+ij.1.size+ij.2.size+2+
      ∑ i : Fin d, ∑ l ∈ table.getD ij.1 ∅, ∑ r ∈ table.getD ij.2 ∅,
        (treeWordWork (.node i l r)+1))) +
    ∑ t ∈ codeStep d table k, ∑ u ∈ codeStep d table k,
      (treeWordWork t+treeWordWork u+1)

/-- A genuine cached finite table and its source-loop cost. Each lower size
is computed once, then read from the stored table. -/
def codeTableWithCost (d : ℕ) : ℕ → List (Finset (Tree (Fin d))) × ℕ
  | 0 => ([{.nil}], 1)
  | k+1 =>
    let previous := codeTableWithCost d k
    let nextCodes := codeStep d previous.1 k
    (previous.1 ++ [nextCodes], previous.2+codeStepWork d previous.1 k+previous.1.length+1)

lemma codeTable_length (d k : ℕ) : (codeTableWithCost d k).1.length = k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [codeTableWithCost, ih]

/-- Every cached entry is the actual forest-code finite set, with no
correctness or complexity conclusion stored in the program's inputs. -/
theorem codeTable_value (d k i : ℕ) (hi : i ≤ k) :
    (codeTableWithCost d k).1.getD i ∅ = forestCodes d i := by
  induction k with
  | zero =>
    have hei : i=0 := by omega
    subst i
    ext t
    simp [codeTableWithCost, forestCodes, labelings, Tree.treesOfNumNodesEq]
  | succ k ih =>
    by_cases hik : i ≤ k
    · change ((codeTableWithCost d k).1 ++ [_]).getD i ∅ = _
      rw [List.getD_append _ _ _ _ (by rw [codeTable_length]; omega)]
      exact ih hik
    · have hei : i=k+1 := by omega
      subst i
      change ((codeTableWithCost d k).1 ++ [codeStep d (codeTableWithCost d k).1 k]).getD (k+1) ∅ = _
      rw [List.getD_append_right _ _ _ _ (by rw [codeTable_length]), codeTable_length, Nat.sub_self]
      change codeStep d (codeTableWithCost d k).1 k = forestCodes d (k+1)
      exact codeStep_eq d k _ (fun j hj => codeTable_value d k j hj)

/-- Substitute the actual cached entries into the support/subset construction. -/
def cachedSupportPairs {m : ℕ} (N : Fin m → Finset (Fin m)) (d s : ℕ) :
    Finset (Finset (Fin m) × Finset (Fin m)) :=
  let table := codeTableWithCost d s
  (Finset.range s).biUnion fun k =>
    (((Finset.univ : Finset (Fin m)) ×ˢ table.1.getD k ∅).image
      fun x => vertices (next N d) x.1 x.2).biUnion fun A =>
        A.powerset.image (fun B => (A,B))

@[simp] theorem cachedSupportPairs_eq {m : ℕ} (N : Fin m → Finset (Fin m)) (d s : ℕ) :
    cachedSupportPairs N d s = supportPairs N d s := by
  unfold cachedSupportPairs supportPairs candidatePairs candidateSets
  apply Finset.biUnion_congr rfl
  intro k hk
  rw [codeTable_value d s k (Finset.mem_range.mp hk).le]

/-- A numerical envelope used only after the actual source trace is defined. -/
def codeStepBound (d s : ℕ) : ℕ :=
  (s+1)*(4*(s+2)+d*(4*d)^s*((2*(s+1)+1)*(d+2)+1)) +
    ((4*d)^(s+1))^2*(2*((2*(s+1)+1)*(d+2))+1)

lemma nat_size_le_succ (a : ℕ) : a.size ≤ a+1 := by
  apply Nat.size_le.mpr
  exact (Nat.lt_two_pow_self (n := a)).trans_le (Nat.pow_le_pow_right (by decide) (by omega))

/-- Generation work is bounded using the original Catalan count, applied to
each actual source pair and the actual generated duplicate-check sources. -/
theorem codeStepWork_le {d k s : ℕ} (hd : 1 ≤ d) (hk : k ≤ s) :
    codeStepWork d (codeTableWithCost d k).1 k ≤ codeStepBound d s := by
  let T := (codeTableWithCost d k).1
  let W := (2*(s+1)+1)*(d+2)+1
  have hsource : ∀ ij ∈ Finset.antidiagonal k,
      (∑ i : Fin d, ∑ l ∈ T.getD ij.1 ∅, ∑ r ∈ T.getD ij.2 ∅,
        (treeWordWork (.node i l r)+1)) ≤ d*(4*d)^s*W := by
    intro ij hij
    have hij' := Finset.mem_antidiagonal.mp hij
    have hleft := codeTable_value d k ij.1 (by omega)
    have hright := codeTable_value d k ij.2 (by omega)
    change T.getD ij.1 ∅ = forestCodes d ij.1 at hleft
    change T.getD ij.2 ∅ = forestCodes d ij.2 at hright
    rw [hleft, hright]
    have hb : ∀ i : Fin d, ∀ l ∈ forestCodes d ij.1, ∀ r ∈ forestCodes d ij.2,
        treeWordWork (.node i l r)+1 ≤ W := by
      intro i l hl r hr
      have hl' := EfficientSupports.forest_numNodes hl
      have hr' := EfficientSupports.forest_numNodes hr
      have ht := treeWordWork_le (Tree.node i l r)
      simp only [Tree.numNodes, hl', hr'] at ht
      dsimp [W]
      nlinarith
    calc
      _ ≤ ∑ _i : Fin d, ∑ _l ∈ forestCodes d ij.1, ∑ _r ∈ forestCodes d ij.2, W := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro l hl
        exact Finset.sum_le_sum (fun r hr => hb i l hl r hr)
      _ = d*(forestCodes d ij.1).card*(forestCodes d ij.2).card*W := by simp; ring
      _ ≤ d*(4*d)^ij.1*(4*d)^ij.2*W := by
        gcongr
        · exact card_forestCodes_le d ij.1
        · exact card_forestCodes_le d ij.2
      _ = d*(4*d)^k*W := by rw [mul_assoc d, ← pow_add, hij']
      _ ≤ _ := by
        gcongr
        omega
  have houter : (∑ ij ∈ Finset.antidiagonal k,
      (2*(T.length+1)+ij.1.size+ij.2.size+2+
        ∑ i : Fin d, ∑ l ∈ T.getD ij.1 ∅, ∑ r ∈ T.getD ij.2 ∅,
          (treeWordWork (.node i l r)+1))) ≤
        (s+1)*(4*(s+2)+d*(4*d)^s*W) := by
    calc
      _ ≤ ∑ _ij ∈ Finset.antidiagonal k, (4*(s+2)+d*(4*d)^s*W) := by
        apply Finset.sum_le_sum
        intro ij hij
        have hij' := Finset.mem_antidiagonal.mp hij
        have hi := nat_size_le_succ ij.1; have hj := nat_size_le_succ ij.2
        have hs := hsource ij hij
        have hlen : T.length=k+1 := codeTable_length d k
        omega
      _ = (k+1)*(4*(s+2)+d*(4*d)^s*W) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have hstep := codeStep_eq d k T (fun i hi => codeTable_value d k i hi)
  have hdup : (∑ t ∈ codeStep d T k, ∑ u ∈ codeStep d T k,
      (treeWordWork t+treeWordWork u+1)) ≤
      ((4*d)^(s+1))^2*(2*((2*(s+1)+1)*(d+2))+1) := by
    rw [hstep]
    have hcard : (forestCodes d (k+1)).card ≤ (4*d)^(s+1) :=
      (card_forestCodes_le _ _).trans (Nat.pow_le_pow_right (by omega) (by omega))
    calc
      _ ≤ ∑ _t ∈ forestCodes d (k+1), ∑ _u ∈ forestCodes d (k+1),
          (2*((2*(s+1)+1)*(d+2))+1) := by
        apply Finset.sum_le_sum
        intro t ht
        apply Finset.sum_le_sum
        intro u hu
        have ht' := treeWordWork_le t; have hu' := treeWordWork_le u
        rw [EfficientSupports.forest_numNodes ht] at ht'
        rw [EfficientSupports.forest_numNodes hu] at hu'
        nlinarith
      _ = ((forestCodes d (k+1)).card)^2*(2*((2*(s+1)+1)*(d+2))+1) := by simp; ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hcard 2)
  exact Nat.add_le_add houter hdup

def codeTableBound (d s : ℕ) : ℕ := 1+s*(codeStepBound d s+s+2)

/-- The whole cache is built in polynomial time in its explicit exponential
source-size bound. The table itself contains the original finite forest sets. -/
theorem codeTable_cost_le {d k s : ℕ} (hd : 1 ≤ d) (hk : k ≤ s) :
    (codeTableWithCost d k).2 ≤ 1+k*(codeStepBound d s+s+2) := by
  induction k with
  | zero => simp [codeTableWithCost]
  | succ k ih =>
    have hi := ih (by omega)
    have hs := codeStepWork_le hd (show k ≤ s by omega)
    change (codeTableWithCost d k).2+codeStepWork d (codeTableWithCost d k).1 k+
      (codeTableWithCost d k).1.length+1 ≤ _
    rw [codeTable_length]
    nlinarith

theorem codeTable_cost_bound {d s : ℕ} (hd : 1 ≤ d) :
    (codeTableWithCost d s).2 ≤ codeTableBound d s := codeTable_cost_le hd le_rfl

/-- Materialize the complete occurrence-neighbor table once. The returned
lookup closure captures the stored list, so forest decoding does not rebuild
scope intersections on every edge traversal. -/
def cachedNeighbors {n m : ℕ} (scopes : Fin m → Finset (Fin n)) : Fin m → Finset (Fin m) :=
  let table := List.ofFn (neighbors scopes)
  fun e => table.getD e.val ∅

@[simp] theorem cachedNeighbors_eq {n m : ℕ} (scopes : Fin m → Finset (Fin n)) :
    cachedNeighbors scopes = neighbors scopes := by
  funext e
  simp only [cachedNeighbors]
  rw [List.getD_eq_getElem (l := List.ofFn (neighbors scopes)) (d := ∅)
    (n := e.val) (by simpa using e.isLt)]
  simp

/-- The optimized executor shares the generated cache across every degree. -/
def cachedLogApprox {n m : ℕ} (scopes : Fin m → Finset (Fin n))
    (query : PrimitiveMomentsQ.Queries scopes) (r c s C : ℕ) (τ : ℚ) : ℚ :=
  let N := cachedNeighbors scopes
  let allPairs := cachedSupportPairs N (degreeBound r c) s
  ∑ p ∈ Finset.Icc 1 s, ∑ AB ∈ allPairs.filter (fun AB => AB.1.card ≤ p),
    (-1:ℚ)^(AB.1.card-AB.2.card)*localCoeff scopes query AB.2 p s C τ

@[simp] theorem cachedLogApprox_eq {n m : ℕ} (scopes : Fin m → Finset (Fin n))
    (query : PrimitiveMomentsQ.Queries scopes) (r c s C : ℕ) (τ : ℚ) :
    cachedLogApprox scopes query r c s C τ = logApprox scopes query r c s C τ := by
  simp only [cachedLogApprox, cachedNeighbors_eq, cachedSupportPairs_eq, logApprox, pairs]

/-- An actual executor using the shared labelled-forest cache. Its numerical
answer agrees with the paper's rational algorithm on every input. -/
def cachedRun {n m : ℕ} (fixed : Parameters.Fixed) (scopes : Fin m → Finset (Fin n))
    (query : PrimitiveMomentsQ.Queries scopes) (r c : ℕ) (ε : ℚ) : ℚ :=
  if m=0 then 1 else
    Algorithm.rationalExp (cachedLogApprox scopes query r c
      (Parameters.truncationOrder fixed m ε) fixed.C
      (Parameters.primitiveTolerance fixed m ε)) ε

@[simp] theorem cachedRun_eq {n m : ℕ} (fixed : Parameters.Fixed)
    (scopes : Fin m → Finset (Fin n)) (query : PrimitiveMomentsQ.Queries scopes)
    (r c : ℕ) (ε : ℚ) : cachedRun fixed scopes query r c ε = run fixed scopes query r c ε := by
  simp only [cachedRun, run, cachedLogApprox_eq]

open RationalProgram

/-- Natural rational ceiling returned by the actual signed floor kernel. -/
def ceilKernel (x : ℚ) : ℕ := (-(SchoolbookArithmetic.floorKernel (-x)).1).toNat

@[simp] theorem ceilKernel_value (x : ℚ) : ceilKernel x = ⌈x⌉₊ := by
  rw [ceilKernel, SchoolbookArithmetic.floorKernel_value]
  have hc : ⌈x⌉ = -⌊-x⌋ := by simpa using (Int.ceil_neg (a := -x))
  rw [← hc, Int.ceil_toNat]

/-- Execute parameter arithmetic with the validated binary kernels; the
ceiling/division part of integer control receives the same universal factor. -/
def binaryControlWork (e : Expr) : ℕ :=
  (SchoolbookArithmetic.execute e).2+
    (SchoolbookArithmetic.floorKernel (-e.eval)).2+precisionControl e.eval

lemma rationalBits_neg (q : ℚ) : BitComplexity.rationalBits (-q) = BitComplexity.rationalBits q := by
  simp [BitComplexity.rationalBits]

lemma binaryControlWork_le (e : Expr) : binaryControlWork e ≤ 20000*expressionControlWork e := by
  rw [binaryControlWork, (SchoolbookArithmetic.execute_spec e).2]
  have he := SchoolbookArithmetic.exprBitCost_le e
  have hf := SchoolbookArithmetic.floorKernel_cost_le (-e.eval)
  rw [rationalBits_neg] at hf
  have hc : (BitComplexity.rationalBits e.eval+1)^3 ≤ precisionControl e.eval := by
    dsimp only [precisionControl]
    omega
  unfold expressionControlWork
  nlinarith

/-- The five rational arguments used by growing parameter selection. -/
def inputLogArgument (m : ℕ) (ε : ℚ) : Expr :=
  .node .div (.node .add (.atom (m:ℚ)) (.atom 1)) (.atom ε)

def toleranceExpr (p : Parameters.Fixed) (m s : ℕ) (ε : ℚ) : Expr :=
  .node .div (.atom ε)
    (.node .mul (.node .mul (.node .mul (.atom 3) (.atom (s:ℚ))) (.atom (m:ℚ)))
      (natPower (.atom ((4*p.A0*p.F:ℕ):ℚ)) s))

def levelArgument (p : Parameters.Fixed) (m s : ℕ) (ε : ℚ) : Expr :=
  natPower (.node .div (.node .mul (.atom 2)
    (natPower (.atom ((4*p.C:ℕ):ℚ)) s)) (toleranceExpr p m s ε)) 2

def sampleToleranceExpr (p : Parameters.Fixed) (m s J : ℕ) (ε : ℚ) : Expr :=
  let a : Expr := .node .add (.atom (J:ℚ)) (.atom 1)
  let denominator : Expr := .node .mul
    (.node .mul (.node .mul (.atom 4) (.atom (s:ℚ))) a)
    (.node .mul (natPower (.atom 3) (s-1)) (natPower (.atom (p.C:ℚ)) s))
  .node .min (.node .div (.atom 1) (.node .mul (.atom 2) a))
    (.node .div (toleranceExpr p m s ε) denominator)

def precisionArgument (p : Parameters.Fixed) (m s J : ℕ) (ε : ℚ) : Expr :=
  .node .div (.node .add (.node .mul (.atom 2) (.atom (s:ℚ))) (.atom 1)) (sampleToleranceExpr p m s J ε)

@[simp] theorem inputLogArgument_eval (m : ℕ) (ε : ℚ) :
    (inputLogArgument m ε).eval = ((m+1:ℕ):ℚ)/ε := by
  simp [inputLogArgument, Expr.eval, Op.eval]

@[simp] theorem toleranceExpr_eval (p : Parameters.Fixed) (m : ℕ) (ε : ℚ) :
    (toleranceExpr p m (Parameters.truncationOrder p m ε) ε).eval =
      Parameters.primitiveTolerance p m ε := by
  simp only [toleranceExpr, Expr.eval, Op.eval, natPower_eval, Parameters.primitiveTolerance]

@[simp] theorem levelArgument_eval (p : Parameters.Fixed) (m : ℕ) (ε : ℚ) :
    (levelArgument p m (Parameters.truncationOrder p m ε) ε).eval =
      (2*((4*p.C:ℕ):ℚ)^Parameters.truncationOrder p m ε /
        Parameters.primitiveTolerance p m ε)^2 := by
  simp only [levelArgument, natPower_eval, Expr.eval, Op.eval, toleranceExpr_eval]

@[simp] theorem sampleToleranceExpr_eval (p : Parameters.Fixed) (m J : ℕ) (ε : ℚ) :
    (sampleToleranceExpr p m (Parameters.truncationOrder p m ε) J ε).eval =
      Oracle.primitiveSampleTol (Parameters.truncationOrder p m ε) J p.C
        (Parameters.primitiveTolerance p m ε) := by
  simp only [sampleToleranceExpr, Expr.eval, Op.eval, natPower_eval, toleranceExpr_eval,
    Oracle.primitiveSampleTol]
  push_cast
  ring_nf

@[simp] theorem precisionArgument_eval (p : Parameters.Fixed) (m J : ℕ) (ε : ℚ) :
    (precisionArgument p m (Parameters.truncationOrder p m ε) J ε).eval =
      ((2*Parameters.truncationOrder p m ε+1:ℕ):ℚ)/
        Oracle.primitiveSampleTol (Parameters.truncationOrder p m ε) J p.C
          (Parameters.primitiveTolerance p m ε) := by
  simp only [precisionArgument, Expr.eval, Op.eval, sampleToleranceExpr_eval]
  norm_cast

/-- Explicit atom height budget, depending only polynomially on the input
encoding and the actual growing integer parameters. -/
def parameterHeight (p : Parameters.Fixed) (m s J : ℕ) (ε : ℚ) : ℕ :=
  BitComplexity.rationalBits ε + (3*s*m+1)+(4*s*(J+1)+1)+(2*s+2)+(J+2)+(m+2)+
    (4*p.A0*p.F+1)+(4*p.C+1)+(p.C+1)+10

lemma parameter_atom_height {p : Parameters.Fixed} {m s J : ℕ} {ε : ℚ} :
    height ε ≤ parameterHeight p m s J ε ∧
      height (((3*s*m:ℕ):ℚ)) ≤ parameterHeight p m s J ε ∧
      height (((4*s*(J+1):ℕ):ℚ)) ≤ parameterHeight p m s J ε ∧
      height (((2*s+1:ℕ):ℚ)) ≤ parameterHeight p m s J ε ∧
      height (((J+1:ℕ):ℚ)) ≤ parameterHeight p m s J ε ∧
      height (((m+1:ℕ):ℚ)) ≤ parameterHeight p m s J ε ∧
      height (((4*p.A0*p.F:ℕ):ℚ)) ≤ parameterHeight p m s J ε ∧
      height (((4*p.C:ℕ):ℚ)) ≤ parameterHeight p m s J ε ∧
      height ((p.C:ℚ)) ≤ parameterHeight p m s J ε := by
  have he := PrimitiveInputHeight.height_le_rationalBits ε
  have hn : ∀ v : ℕ, height (v:ℚ) ≤ v+1 := fun v =>
    RationalRecurrenceProgram.height_natCast_le (le_refl v)
  have h₁ := hn (3*s*m)
  have h₂ := hn (4*s*(J+1))
  have h₃ := hn (2*s+1)
  have h₄ := hn (J+1)
  have h₅ := hn (m+1)
  have h₆ := hn (4*p.A0*p.F)
  have h₇ := hn (4*p.C)
  have h₈ := hn p.C
  unfold parameterHeight
  omega

lemma parameterExpr_bounds (p : Parameters.Fixed) (m s J : ℕ) (ε : ℚ) :
    ∀ e ∈ [inputLogArgument m ε, toleranceExpr p m s ε, levelArgument p m s ε,
      sampleToleranceExpr p m s J ε, precisionArgument p m s J ε],
      e.inputHeight ≤ parameterHeight p m s J ε ∧ e.operations ≤ 12*s+40 := by
  have ha := parameter_atom_height (p := p) (m := m) (s := s) (J := J) (ε := ε)
  have hH : 10 ≤ parameterHeight p m s J ε := by unfold parameterHeight; omega
  have hs0 := RationalRecurrenceProgram.height_natCast_le (le_refl s)
  have hm0 := RationalRecurrenceProgram.height_natCast_le (le_refl m)
  have hJ0 := RationalRecurrenceProgram.height_natCast_le (le_refl J)
  have hsH : height (s:ℚ) ≤ parameterHeight p m s J ε := by unfold parameterHeight; omega
  have hmH : height (m:ℚ) ≤ parameterHeight p m s J ε := by unfold parameterHeight; omega
  have hJH : height (J:ℚ) ≤ parameterHeight p m s J ε := by unfold parameterHeight; omega
  have hc3' : height (3:ℚ) ≤ parameterHeight p m s J ε := by
    have hh := RationalRecurrenceProgram.height_natCast_le (j := 3) (s := 3) le_rfl
    norm_num only [Nat.cast_ofNat] at hh
    omega
  have hc4' : height (4:ℚ) ≤ parameterHeight p m s J ε := by
    have hh := RationalRecurrenceProgram.height_natCast_le (j := 4) (s := 4) le_rfl
    norm_num only [Nat.cast_ofNat] at hh
    omega
  have hsmall : ∀ k : ℕ, k ≤ 3 → height (k:ℚ) ≤ parameterHeight p m s J ε := by
    intro k hk
    have hh := RationalRecurrenceProgram.height_natCast_le hk
    omega
  have hc0 := hsmall 0 (by omega)
  have hc1 := hsmall 1 (by omega)
  have hc2 := hsmall 2 (by omega)
  have hc3 := hsmall 3 (by omega)
  have hp : ∀ (q : ℚ) (a : ℕ), height q ≤ parameterHeight p m s J ε →
      (natPower (.atom q) a).inputHeight ≤ parameterHeight p m s J ε := by
    intro q a hq
    exact natPower_inputHeight _ _ (by omega) hq
  have hc2' : height (2:ℚ) ≤ parameterHeight p m s J ε := by
    rw [PrimitiveExpressions.height_two]
    omega
  simp only [height, max_le_iff] at ha hc0 hc1 hc2 hc3 hc2' hc3' hc4' hsH hmH hJH
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  all_goals
    constructor
    · simp only [inputLogArgument, toleranceExpr, levelArgument, sampleToleranceExpr,
        precisionArgument, Expr.inputHeight]
      repeat' apply max_le
      all_goals first
        | omega
        | (norm_num [height]; omega)
        | (apply natPower_inputHeight <;> (first | omega | (simp only [Expr.inputHeight, height, max_le_iff]; omega)))
    · simp only [inputLogArgument, toleranceExpr, levelArgument, sampleToleranceExpr,
        precisionArgument, Expr.operations, natPower_operations]
      omega

/-- Parameter arithmetic and ceil/clog control are charged on their actual
rational arguments, rather than assumed polynomial as an input field. -/
def parameterWork (p : Parameters.Fixed) (m : ℕ) (ε : ℚ) : ℕ :=
  let s := Parameters.truncationOrder p m ε
  let J := Parameters.level p m ε
  ([inputLogArgument m ε, toleranceExpr p m s ε, levelArgument p m s ε,
      sampleToleranceExpr p m s J ε, precisionArgument p m s J ε].map binaryControlWork).sum +
    s.size+m.size+J.size+1

def parameterBound (p : Parameters.Fixed) (m : ℕ) (ε : ℚ) : ℕ :=
  let s := Parameters.truncationOrder p m ε
  let J := Parameters.level p m ε
  5*expressionControlBound (parameterHeight p m s J ε) (12*s+40)+s+m+J+4

theorem parameterWork_le (p : Parameters.Fixed) (m : ℕ) (ε : ℚ) :
    parameterWork p m ε ≤ 20000*parameterBound p m ε := by
  let s := Parameters.truncationOrder p m ε
  let J := Parameters.level p m ε
  have hh := parameterExpr_bounds p m s J ε
  have hsum : ∀ e ∈ [inputLogArgument m ε, toleranceExpr p m s ε, levelArgument p m s ε,
      sampleToleranceExpr p m s J ε, precisionArgument p m s J ε],
      binaryControlWork e ≤ 20000*expressionControlBound (parameterHeight p m s J ε) (12*s+40) := by
    intro e he
    exact (binaryControlWork_le e).trans (Nat.mul_le_mul_left 20000
      (expressionControlWork_le e (hh e he).1 (hh e he).2))
  have hs := List.sum_le_card_nsmul
    ([inputLogArgument m ε, toleranceExpr p m s ε, levelArgument p m s ε,
      sampleToleranceExpr p m s J ε, precisionArgument p m s J ε].map binaryControlWork)
    (20000*expressionControlBound (parameterHeight p m s J ε) (12*s+40)) (by
      intro b hb
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
      exact hsum e he)
  have hs' := nat_size_le_succ s; have hm' := nat_size_le_succ m; have hJ' := nat_size_le_succ J
  simp only [List.length_map, List.length_cons, List.length_nil, Nat.reduceAdd, nsmul_eq_mul] at hs
  change _ ≤ 20000*(5*expressionControlBound (parameterHeight p m s J ε) (12*s+40)+s+m+J+4)
  change ([inputLogArgument m ε, toleranceExpr p m s ε, levelArgument p m s ε,
      sampleToleranceExpr p m s J ε, precisionArgument p m s J ε].map binaryControlWork).sum+
      s.size+m.size+J.size+1 ≤ _
  omega

open SchoolbookArithmetic

lemma rationalBits_nat (a : ℕ) : BitComplexity.rationalBits (a:ℚ) = a.size+2 := by
  simp [BitComplexity.rationalBits]

lemma commonLevel_le {n t J : ℕ} (scopes : Fin t → Finset (Fin n)) (ν : Fin t → ℕ)
    (hν : ∑ i, ν i ≤ J) (v : Fin n) : commonLevels scopes ν v ≤ J := by
  unfold commonLevels
  apply Finset.sup_le
  intro i hi
  split_ifs
  · exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hν
  · omega

/-- Form an actual coarse dyadic coordinate by binary long division followed
by the canonical rational division kernel. Denominator words are constructed
by appending the requested number of binary zero digits. -/
def coordinateWithCost {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (ν : Fin t → ℕ)
    (z : Grid (commonLevels scopes ν)) (i : Fin t) (l : ℕ) (j : Fin (scopes i).card) : ℚ × ℕ :=
  let v := (scopes i).orderEmbOfFin rfl j
  let a := (z v).val
  let b := 2^(commonLevels scopes ν v-l)
  let division := longDivide a b
  let denominator := (2^l:ℕ)
  (kernelValue .div (division.quotient:ℚ) (denominator:ℚ),
    division.bitCost+kernelCost .div (division.quotient:ℚ) (denominator:ℚ)+
      commonLevels scopes ν v+l+2)

@[simp] theorem coordinateWithCost_value {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (ν : Fin t → ℕ) (z : Grid (commonLevels scopes ν)) (i : Fin t) (l : ℕ)
    (j : Fin (scopes i).card) :
    (coordinateWithCost scopes ν z i l j).1 = queryPoint l (localIndex scopes ν z i l) j := by
  unfold coordinateWithCost queryPoint localIndex
  dsimp only
  rw [kernelValue_eq, (longDivide_spec _ _ (by positivity)).1]
  simp [Op.eval]

lemma coordinateWithCost_le {n t J : ℕ} (scopes : Fin t → Finset (Fin n)) (ν : Fin t → ℕ)
    (hν : ∑ i, ν i ≤ J) (z : Grid (commonLevels scopes ν)) (i : Fin t) (l : ℕ)
    (hl : l ≤ J) (j : Fin (scopes i).card) :
    (coordinateWithCost scopes ν z i l j).2 ≤
      6*J*(2*J+2)+10000*(2*J+6)^3+2*J+2 := by
  let v := (scopes i).orderEmbOfFin rfl j
  let a := (z v).val
  let b := 2^(commonLevels scopes ν v-l)
  have hlevel := commonLevel_le scopes ν hν v
  have ha : a.size ≤ J := Nat.size_le.mpr
    ((z v).isLt.trans_le (Nat.pow_le_pow_right (by decide) hlevel))
  have hb : b.size ≤ J+1 := by
    dsimp [b]
    rw [Nat.size_pow]
    omega
  have hd := longDivide_cost_le a b
  have hd' : (longDivide a b).bitCost ≤ 6*J*(2*J+2) :=
    hd.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 6 ha) (by omega))
  have hp : (longDivide a b).quotient.size ≤ J := by
    rw [(longDivide_spec a b (by dsimp [b]; positivity)).1]
    exact (Nat.size_le_size (Nat.div_le_self a b)).trans ha
  have hden : (2^l:ℕ).size ≤ J+1 := by rw [Nat.size_pow]; omega
  have hk := kernelCost_le Op.div ((longDivide a b).quotient:ℚ) ((2^l:ℕ):ℚ)
  rw [rationalBits_nat, rationalBits_nat] at hk
  have hk' : kernelCost Op.div ((longDivide a b).quotient:ℚ) ((2^l:ℕ):ℚ) ≤
      10000*(2*J+6)^3 := hk.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
  change (longDivide a b).bitCost+kernelCost Op.div ((longDivide a b).quotient:ℚ)
    ((2^l:ℕ):ℚ)+commonLevels scopes ν v+l+2 ≤ _
  omega

/-- Actual local-coordinate loops, including the sorted scope index table. -/
def pointWork {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (ν : Fin t → ℕ)
    (z : Grid (commonLevels scopes ν)) (i : Fin t) (l : ℕ) : ℕ :=
  sortCharge (scopes i) indexKey + ∑ j : Fin (scopes i).card,
    ((coordinateWithCost scopes ν z i l j).2+n+1)

def pointBound (n r J : ℕ) : ℕ :=
  r^2*(2*r*(n+2)+6)+r*(6*J*(2*J+2)+10000*(2*J+6)^3+2*J+n+3)

lemma pointWork_le {n t r J : ℕ} (scopes : Fin t → Finset (Fin n))
    (hs : ∀ i, (scopes i).card ≤ r) (ν : Fin t → ℕ) (hν : ∑ i, ν i ≤ J)
    (z : Grid (commonLevels scopes ν)) (i : Fin t) (l : ℕ) (hl : l ≤ J) :
    pointWork scopes ν z i l ≤ pointBound n r J := by
  have hsor := sortCharge_le (scopes i) indexKey (fun v _ => indexKey_bits_le v)
  have hsort : sortCharge (scopes i) indexKey ≤ r^2*(2*r*(n+2)+6) := by
    apply hsor.trans
    exact Nat.mul_le_mul (Nat.pow_le_pow_left (hs i) 2) (by nlinarith [hs i])
  have hsum : (∑ j : Fin (scopes i).card, ((coordinateWithCost scopes ν z i l j).2+n+1)) ≤
      r*(6*J*(2*J+2)+10000*(2*J+6)^3+2*J+n+3) := by
    calc
      _ ≤ ∑ _j : Fin (scopes i).card,
          (6*J*(2*J+2)+10000*(2*J+6)^3+2*J+n+3) :=
        Finset.sum_le_sum (fun j _ => by have hh := coordinateWithCost_le scopes ν hν z i l hl j; omega)
      _ = (scopes i).card*(6*J*(2*J+2)+10000*(2*J+6)^3+2*J+n+3) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (hs i)
  exact Nat.add_le_add hsort hsum

/-- Level maxima are computed by scanning the actual local incidence lists. -/
def commonLevelWork {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (ν : Fin t → ℕ) : ℕ :=
  ∑ v : Fin n, ∑ i : Fin t, (incidenceWork (scopes i) v+(ν i).size+1)

lemma commonLevelWork_le {n t r s J : ℕ} (scopes : Fin t → Finset (Fin n))
    (hs : ∀ i, (scopes i).card ≤ r) (ht : t ≤ s) (ν : Fin t → ℕ) (hν : ∑ i, ν i ≤ J) :
    commonLevelWork scopes ν ≤ n*s*(r*(2*n+2)+J+2) := by
  unfold commonLevelWork
  calc
    _ ≤ ∑ _v : Fin n, ∑ _i : Fin t, (r*(2*n+2)+J+2) := by
      apply Finset.sum_le_sum
      intro v hv
      apply Finset.sum_le_sum
      intro i hi
      have hinc := (incidenceWork_le (scopes i) v).trans (Nat.mul_le_mul_right _ (hs i))
      have hval : ν i ≤ J := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hν
      have hb := nat_size_le_succ (ν i)
      omega
    _ = n*t*(r*(2*n+2)+J+2) := by simp; ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left n ht)

/-- Coordinate and index work inside one actual retained dyadic cell. -/
def cellWork {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (ν : Fin t → ℕ)
    (z : Grid (commonLevels scopes ν)) : ℕ :=
  loopWork Finset.univ indexKey (fun i : Fin t =>
    if ν i=0 then pointWork scopes ν z i 0
    else pointWork scopes ν z i (ν i)+pointWork scopes ν z i (ν i-1))

def cellBound (n r s J : ℕ) : ℕ :=
  s^2*(2*s*(s+2)+6)+s*(s+2+2*pointBound n r J+1)

lemma cellWork_le {n t r s J : ℕ} (scopes : Fin t → Finset (Fin n))
    (hs : ∀ i, (scopes i).card ≤ r) (ht : t ≤ s) (ν : Fin t → ℕ)
    (hν : ∑ i, ν i ≤ J) (z : Grid (commonLevels scopes ν)) :
    cellWork scopes ν z ≤ cellBound n r s J := by
  unfold cellWork
  apply loopWork_le _ _ _ (Q := s) (D := s+2) (W := 2*pointBound n r J)
  · simpa using ht
  · intro i hi
    exact (indexKey_bits_le i).trans (by omega)
  · intro i hi
    have hval : ν i ≤ J := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hν
    have hp := pointWork_le scopes hs ν hν z i (ν i) hval
    have hm := pointWork_le scopes hs ν hν z i (ν i-1) (by omega)
    have hz := pointWork_le scopes hs ν hν z i 0 (by omega)
    split_ifs <;> omega

def levelKey {t : ℕ} (ν : Fin t → ℕ) : List ℕ := List.ofFn ν

lemma levelKey_bits_le {t s J : ℕ} (ht : t ≤ s) (ν : Fin t → ℕ) (hν : ∑ i, ν i ≤ J) :
    keyBits (levelKey ν) ≤ s*(J+2)+1 := by
  apply (keyBits_ofFn_le ν (D := J+1) (fun i => ?_)).trans (by nlinarith)
  have hi : ν i ≤ J := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hν
  have hh := nat_size_le_succ (ν i)
  omega

lemma cellKey_bits_le {n t J : ℕ} (scopes : Fin t → Finset (Fin n))
    (ν : Fin t → ℕ) (hν : ∑ i, ν i ≤ J) (z : Grid (commonLevels scopes ν)) :
    keyBits (gridKey (commonLevels scopes ν) z) ≤ n*(J+2)+1 := by
  apply keyBits_ofFn_le
  intro v
  apply Nat.size_le.mpr
  exact (z v).isLt.trans_le (Nat.pow_le_pow_right (by decide) (by
    have hh := commonLevel_le scopes ν hν v; omega))

/-- Actual level/cell/index/coordinate sources of the quadrature rule. -/
def ruleWork {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (J : ℕ) : ℕ :=
  AntidiagonalCost.boundedWork t J + loopWork (TupleCount.boundedTuples t J) levelKey fun ν =>
    commonLevelWork scopes ν + loopWork Finset.univ (gridKey (commonLevels scopes ν))
      (cellWork scopes ν)

def ruleBound (n r s J : ℕ) : ℕ :=
  let Q := 2^(J+s)
  let G := 2^(r*J)
  let D := n*(J+2)+1
  let W := G^2*(2*G*D+6)+G*(D+cellBound n r s J+1)
  AntidiagonalCost.boundedBound s J +
    (Q^2*(2*Q*(s*(J+2)+1)+6)+Q*(s*(J+2)+1+(n*s*(r*(2*n+2)+J+2)+W)+1))

theorem ruleWork_le {n t r s J : ℕ} (scopes : Fin t → Finset (Fin n))
    (hs : ∀ i, (scopes i).card ≤ r) (ht : t ≤ s) :
    ruleWork scopes J ≤ ruleBound n r s J := by
  unfold ruleWork ruleBound
  dsimp only
  apply Nat.add_le_add (AntidiagonalCost.boundedWork_le ht)
  apply loopWork_le _ _ _ (Q := 2^(J+s)) (D := s*(J+2)+1)
  · rw [TupleCount.card_boundedTuples]
    exact (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide) (by omega))
  · intro ν hν
    exact levelKey_bits_le ht ν (TupleCount.mem_boundedTuples.mp hν)
  · intro ν hν
    have hν' := TupleCount.mem_boundedTuples.mp hν
    apply Nat.add_le_add (commonLevelWork_le scopes hs ht ν hν')
    apply loopWork_le _ _ _ (Q := 2^(r*J)) (D := n*(J+2)+1)
    · simpa using common_grid_card_le scopes hs ν hν'
    · exact fun z _ => cellKey_bits_le scopes ν hν' z
    · exact fun z _ => cellWork_le scopes hs ht ν hν' z

/-- Actual ordered generation of the sparse exponent source. This avoids
choice of a finite-support coordinate bijection inside the execution. -/
def generatedMomentExpr {n m : ℕ} (scopes : Fin m → Finset (Fin n))
    (query : PrimitiveMomentsQ.Queries scopes) (B : Finset (Fin m)) (j s C : ℕ) (τ : ℚ) : Expr :=
  if j=0 then .atom 1 else
    letI := exponentOrder m
    sumSet ((Finset.finAntidiagonal B.card j).image (AntidiagonalCost.exponentOfTuple B))
      (fun d => .node .div (PrimitiveIntegralProgram.sparseExpr scopes query d s C τ)
        (PrimitiveIntegralProgram.factorialWeightExpr d))

@[simp] theorem generatedMomentExpr_eq {n m : ℕ} (scopes : Fin m → Finset (Fin n))
    (query : PrimitiveMomentsQ.Queries scopes) (B : Finset (Fin m)) (j s C : ℕ) (τ : ℚ) :
    generatedMomentExpr scopes query B j s C τ =
      PrimitiveIntegralProgram.momentExpr scopes query B j s C τ := by
  simp only [generatedMomentExpr, PrimitiveIntegralProgram.momentExpr,
    ← AntidiagonalCost.finsuppAntidiag_source]

def generatedLocalProgram {n m : ℕ} (scopes : Fin m → Finset (Fin n))
    (query : PrimitiveMomentsQ.Queries scopes) (B : Finset (Fin m)) (j s C : ℕ) (τ : ℚ) : Expr :=
  RationalRecurrenceProgram.recurrenceExpr (fun i => generatedMomentExpr scopes query B i s C τ) j

@[simp] theorem generatedLocalProgram_eq {n m : ℕ} (scopes : Fin m → Finset (Fin n))
    (query : PrimitiveMomentsQ.Queries scopes) (B : Finset (Fin m)) (j s C : ℕ) (τ : ℚ) :
    generatedLocalProgram scopes query B j s C τ = FPTASProgram.localProgram scopes query B j s C τ := by
  simp only [generatedLocalProgram, FPTASProgram.localProgram, generatedMomentExpr_eq]

/-- The complete arithmetic expression uses the shared support cache. -/
def cachedLogProgram {n m : ℕ} (scopes : Fin m → Finset (Fin n))
    (query : PrimitiveMomentsQ.Queries scopes) (r c s C : ℕ) (τ : ℚ) : Expr :=
  let N := cachedNeighbors scopes
  let allPairs := cachedSupportPairs N (degreeBound r c) s
  sumSet (Finset.Icc 1 s) fun p =>
    letI := pairOrder m
    sumSet (allPairs.filter (fun AB => AB.1.card ≤ p)) fun AB =>
      .node .mul (natPower (.atom (-1)) (AB.1.card-AB.2.card))
        (generatedLocalProgram scopes query AB.2 p s C τ)

@[simp] theorem cachedLogProgram_eq {n m : ℕ} (scopes : Fin m → Finset (Fin n))
    (query : PrimitiveMomentsQ.Queries scopes) (r c s C : ℕ) (τ : ℚ) :
    cachedLogProgram scopes query r c s C τ = FPTASProgram.logProgram scopes query r c s C τ := by
  simp only [cachedLogProgram, cachedNeighbors_eq, cachedSupportPairs_eq, FPTASProgram.logProgram, pairs, generatedLocalProgram_eq]

def cachedRunProgram {n m : ℕ} (p : Parameters.Fixed) (scopes : Fin m → Finset (Fin n))
    (query : PrimitiveMomentsQ.Queries scopes) (r c : ℕ) (ε : ℚ) : Expr :=
  if m=0 then .atom 1 else
    RationalRecurrenceProgram.rationalExpExpr (cachedLogProgram scopes query r c
      (Parameters.truncationOrder p m ε) p.C (Parameters.primitiveTolerance p m ε)) ε

@[simp] theorem cachedRunProgram_eq {n m : ℕ} (p : Parameters.Fixed)
    (scopes : Fin m → Finset (Fin n)) (query : PrimitiveMomentsQ.Queries scopes)
    (r c : ℕ) (ε : ℚ) :
    cachedRunProgram p scopes query r c ε = FPTASProgram.runProgram p scopes query r c ε := by
  simp only [cachedRunProgram, FPTASProgram.runProgram, cachedLogProgram_eq]

/-- Concrete schoolbook execution of the cached program gives the original
algorithm's output; the same expression also inherits all arithmetic bounds. -/
theorem execute_cachedRunProgram_value {n m : ℕ} (p : Parameters.Fixed)
    (scopes : Fin m → Finset (Fin n)) (query : PrimitiveMomentsQ.Queries scopes)
    (r c : ℕ) (ε : ℚ) :
    (execute (cachedRunProgram p scopes query r c ε)).1 = run p scopes query r c ε := by
  rw [(execute_spec _).1, cachedRunProgram_eq, FPTASProgram.runProgram_eval]

/-- Sparse exponent keys are finite lists of their actual coordinates. -/
def exponentKey {m : ℕ} (d : Fin m →₀ ℕ) : List ℕ := List.ofFn (fun e => d e)

lemma exponentKey_bits_le {m s : ℕ} (d : Fin m →₀ ℕ) (hd : d.degree ≤ s) :
    keyBits (exponentKey d) ≤ m*(s+2)+1 := by
  apply keyBits_ofFn_le
  intro e
  have he : d e ≤ s := by
    by_cases hm : e ∈ d.support
    · exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hm).trans hd
    · rw [Finsupp.notMem_support_iff.mp hm]
      omega
  have hh := nat_size_le_succ (d e)
  omega

/-- Discrete work in the actual sparse primitive term. -/
def sparseWork {n m : ℕ} (scopes : Fin m → Finset (Fin n))
    (d : Fin m →₀ ℕ) (J : ℕ) : ℕ :=
  loopWork d.support indexKey (fun e => (d e).size+m+1)+
    ruleWork (fun i : Fin d.support.card => scopes (d.support.orderEmbOfFin rfl i)) J

def sparseBound (n m r s J : ℕ) : ℕ :=
  s^2*(2*s*(m+2)+6)+s*(m+2+(s+m+2)+1)+ruleBound n r s J

lemma sparseWork_le {n m r s J : ℕ} (scopes : Fin m → Finset (Fin n))
    (hs : ∀ e, (scopes e).card ≤ r) (d : Fin m →₀ ℕ) (hd : d.degree ≤ s) :
    sparseWork scopes d J ≤ sparseBound n m r s J := by
  have ht : d.support.card ≤ s := (Support.finsupp_support_card_le_degree d).trans hd
  unfold sparseWork sparseBound
  apply Nat.add_le_add
  · apply loopWork_le _ _ _ ht (fun e _ => indexKey_bits_le e)
    intro e he
    have hval : d e ≤ s := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) he).trans hd
    have hh := nat_size_le_succ (d e)
    omega
  · exact ruleWork_le _ (fun i => hs _) ht

/-- The exact degree-j sparse moment source is enumerated and sorted. -/
def momentWork {n m : ℕ} (scopes : Fin m → Finset (Fin n))
    (B : Finset (Fin m)) (j J : ℕ) : ℕ :=
  if j=0 then 0 else
    AntidiagonalCost.exponentWork B j+
      loopWork (Finset.finsuppAntidiag B j) exponentKey (fun d => sparseWork scopes d J)

def momentBound (n m r s J : ℕ) : ℕ :=
  AntidiagonalCost.exponentBound m s+
    ((4^s)^2*(2*4^s*(m*(s+2)+1)+6)+4^s*(m*(s+2)+1+sparseBound n m r s J+1))

lemma momentWork_le {n m r s j J : ℕ} (scopes : Fin m → Finset (Fin n))
    (hs : ∀ e, (scopes e).card ≤ r) (B : Finset (Fin m)) (hB : B.card ≤ s) (hj : j ≤ s) :
    momentWork scopes B j J ≤ momentBound n m r s J := by
  unfold momentWork
  split_ifs with hj0
  · exact Nat.zero_le _
  · unfold momentBound
    apply Nat.add_le_add (AntidiagonalCost.exponentWork_le B hB hj)
    apply loopWork_le _ _ _ (Q := 4^s) (D := m*(s+2)+1)
    · exact TupleCount.card_finsuppAntidiag_le B hB hj
    · intro d hd
      have hdeg : d.degree ≤ s := by
        have hh := (Finset.mem_finsuppAntidiag'.mp hd).1
        change d.degree=j at hh
        omega
      exact exponentKey_bits_le d hdeg
    · intro d hd
      have hdeg : d.degree ≤ s := by
        have hh := (Finset.mem_finsuppAntidiag'.mp hd).1
        change d.degree=j at hh
        omega
      exact sparseWork_le scopes hs d hdeg

/-- Instrumentation of the same uncached recurrence, with actual moment
values and the source-loop work performed at each repeated call. -/
def localWithDiscrete {n m : ℕ} (scopes : Fin m → Finset (Fin n))
    (query : PrimitiveMomentsQ.Queries scopes) (B : Finset (Fin m)) (j s C : ℕ) (τ : ℚ) : ℚ × ℕ :=
  BitComplexity.rationalLogCoeffQueryCost
    (fun i => (PrimitiveMomentsQ.momentQ scopes query B i s C τ,
      momentWork scopes B i (Oracle.totalLevelChoice s C τ))) j

@[simp] theorem localWithDiscrete_value {n m : ℕ} (scopes : Fin m → Finset (Fin n))
    (query : PrimitiveMomentsQ.Queries scopes) (B : Finset (Fin m)) (j s C : ℕ) (τ : ℚ) :
    (localWithDiscrete scopes query B j s C τ).1 = localCoeff scopes query B j s C τ :=
  BitComplexity.rationalLogCoeffQueryCost_value _ _

lemma localWithDiscrete_work_le {n m r s j C : ℕ} (scopes : Fin m → Finset (Fin n))
    (hs : ∀ e, (scopes e).card ≤ r) (query : PrimitiveMomentsQ.Queries scopes)
    (B : Finset (Fin m)) (hB : B.card ≤ s) (hj : j ≤ s) (τ : ℚ) :
    (localWithDiscrete scopes query B j s C τ).2 ≤
      momentBound n m r s (Oracle.totalLevelChoice s C τ)*2^(s+1) := by
  have h := BitComplexity.rationalLogCoeffQueryCost_queries_le
    (fun i => (PrimitiveMomentsQ.momentQ scopes query B i s C τ,
      momentWork scopes B i (Oracle.totalLevelChoice s C τ))) s j
    (momentBound n m r s (Oracle.totalLevelChoice s C τ)) hj
    (fun i _ hi => momentWork_le scopes hs B hB hi)
  exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega)))

/-- Materialize a binary membership key by scanning the actual stored set. -/
def membershipKeyWork {m : ℕ} (A : Finset (Fin m)) : ℕ :=
  ∑ v : Fin m, (incidenceWork A v+1)

def membershipKeyBound (m : ℕ) : ℕ := m*(m*(2*m+2)+1)

lemma membershipKeyWork_le {m : ℕ} (A : Finset (Fin m)) :
    membershipKeyWork A ≤ membershipKeyBound m := by
  unfold membershipKeyWork membershipKeyBound
  calc
    _ ≤ ∑ _v : Fin m, (m*(2*m+2)+1) := by
      apply Finset.sum_le_sum
      intro v hv
      have hi := incidenceWork_le A v
      have hc : A.card ≤ m := by simpa using Finset.card_le_univ A
      nlinarith
    _ = _ := by simp

/-- Duplicate elimination charges all pairs of original decoded sources,
including different forests which decode to the same vertex set. -/
def candidateDedupWork {m : ℕ} (N : Fin m → Finset (Fin m)) (d k : ℕ) : ℕ :=
  let source := (Finset.univ : Finset (Fin m)) ×ˢ forestCodes d k
  (∑ x ∈ source, membershipKeyWork (vertices (next N d) x.1 x.2))+
    ∑ x ∈ source, ∑ y ∈ source,
      (keyBits (finsetKey (vertices (next N d) x.1 x.2))+
        keyBits (finsetKey (vertices (next N d) y.1 y.2))+1)

lemma candidateDedupWork_le {m d k s : ℕ} (N : Fin m → Finset (Fin m))
    (hd : 1 ≤ d) (hk : k ≤ s) :
    candidateDedupWork N d k ≤ m*(4*d)^s*membershipKeyBound m+
      (m*(4*d)^s)^2*(4*m+3) := by
  let S := (Finset.univ : Finset (Fin m)) ×ˢ forestCodes d k
  have hc : S.card ≤ m*(4*d)^s := by
    simp only [S, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    exact Nat.mul_le_mul_left m ((card_forestCodes_le d k).trans (Nat.pow_le_pow_right (by omega) hk))
  have hk' : (∑ x ∈ S, membershipKeyWork (vertices (next N d) x.1 x.2)) ≤ S.card*membershipKeyBound m := by
    calc
      _ ≤ ∑ _x ∈ S, membershipKeyBound m := Finset.sum_le_sum (fun x _ => membershipKeyWork_le _)
      _ = _ := by simp
  have hp : (∑ x ∈ S, ∑ y ∈ S,
      (keyBits (finsetKey (vertices (next N d) x.1 x.2))+
        keyBits (finsetKey (vertices (next N d) y.1 y.2))+1)) ≤ S.card^2*(4*m+3) := by
    calc
      _ ≤ ∑ _x ∈ S, ∑ _y ∈ S, (4*m+3) := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro y hy
        have hx' := finsetKey_bits_le (vertices (next N d) x.1 x.2)
        have hy' := finsetKey_bits_le (vertices (next N d) y.1 y.2)
        omega
      _ = _ := by simp; ring
  exact Nat.add_le_add (hk'.trans (Nat.mul_le_mul_right _ hc))
    (hp.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hc 2)))

/-- Construct all membership keys in the actual local powerset source. -/
def subsetKeyWork {m : ℕ} (A : Finset (Fin m)) : ℕ :=
  membershipKeyWork A+∑ B ∈ A.powerset, membershipKeyWork B

lemma subsetKeyWork_le {m s : ℕ} (A : Finset (Fin m)) (hA : A.card ≤ s+1) :
    subsetKeyWork A ≤ (1+2^(s+1))*membershipKeyBound m := by
  have hh := Finset.sum_le_sum (s := A.powerset) (fun B _ => membershipKeyWork_le B)
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset] at hh
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hA
  have hm := Nat.mul_le_mul_right (membershipKeyBound m) hp
  unfold subsetKeyWork
  nlinarith [membershipKeyWork_le A]

/-- Prefixes of the canonical scope list are the actual recursive sources
when building its local powerset. Every intermediate subset is charged. -/
def powersetGenerationWork {m : ℕ} (A : Finset (Fin m)) : ℕ :=
  ∑ k ∈ Finset.range (A.card+1),
    ∑ B ∈ (((canonicalList A).take k).toFinset).powerset,
      (keyBits (finsetKey B)+1)

lemma powersetGenerationWork_le {m s : ℕ} (A : Finset (Fin m)) (hA : A.card ≤ s+1) :
    powersetGenerationWork A ≤ (s+2)*2^(s+1)*(2*m+2) := by
  have hpre : ∀ k, (((canonicalList A).take k).toFinset).card ≤ s+1 := by
    intro k
    have hh := List.toFinset_card_le (l := (canonicalList A).take k)
    have hl : ((canonicalList A).take k).length ≤ A.card := by
      rw [List.length_take, canonicalList_length]
      exact Nat.min_le_right _ _
    omega
  unfold powersetGenerationWork
  calc
    _ ≤ ∑ _k ∈ Finset.range (A.card+1), (2^(s+1)*(2*m+2)) := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        _ ≤ ∑ _B ∈ (((canonicalList A).take k).toFinset).powerset, (2*m+2) :=
          Finset.sum_le_sum (fun B _ => by have hb := finsetKey_bits_le B; omega)
        _ = 2^(((canonicalList A).take k).toFinset).card*(2*m+2) := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (hpre k))
    _ = (A.card+1)*2^(s+1)*(2*m+2) := by simp; ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))

/-- The last prefix is the exact original powerset source. -/
lemma powersetGeneration_source {m : ℕ} (A : Finset (Fin m)) :
    (((canonicalList A).take A.card).toFinset).powerset = A.powerset := by
  rw [← canonicalList_length A, List.take_length]
  congr 1
  ext e
  simp

/-- Raw support/subset occurrences retain their forest-size labels, so later
union duplicate checks cannot discard their construction cost. -/
def rawPairSource {m : ℕ} (N : Fin m → Finset (Fin m)) (d s : ℕ) :=
  (Finset.range s).sigma fun k =>
    (candidateSets (next N d) k).sigma fun A => A.powerset

lemma rawPairSource_card {m d s : ℕ} (N : Fin m → Finset (Fin m)) (hd : 1 ≤ d) :
    (rawPairSource N d s).card ≤ s*(m*(4*d)^s)*2^(s+1) := by
  unfold rawPairSource
  rw [Finset.card_sigma]
  calc
    _ ≤ ∑ _k ∈ Finset.range s, (m*(4*d)^s*2^(s+1)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := (Finset.mem_range.mp hk).le
      rw [Finset.card_sigma]
      calc
        _ ≤ ∑ _A ∈ candidateSets (next N d) k, 2^(s+1) := by
          apply Finset.sum_le_sum
          intro A hA
          rw [Finset.card_powerset]
          exact Nat.pow_le_pow_right (by decide) ((candidate_card_le _ hA).trans (by omega))
        _ = (candidateSets (next N d) k).card*2^(s+1) := by simp
        _ ≤ _ := by
          apply Nat.mul_le_mul_right
          have hc : (candidateSets (next N d) k).card ≤ m*(4*d)^k := by
            simpa using card_candidateSets_le (next N d) k
          exact hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hk'))
    _ = _ := by simp; ring

/-- Cross-size source duplicate checks and all local powerset-prefix sources. -/
def finalSupportWork {m : ℕ} (N : Fin m → Finset (Fin m)) (d s : ℕ) : ℕ :=
  (∑ k ∈ Finset.range s, ∑ A ∈ candidateSets (next N d) k, powersetGenerationWork A)+
    ∑ x ∈ rawPairSource N d s, ∑ y ∈ rawPairSource N d s,
      (keyBits (pairKey (x.2.1,x.2.2))+keyBits (pairKey (y.2.1,y.2.2))+1)

def finalSupportBound (m d s : ℕ) : ℕ :=
  s*(m*(4*d)^s)*((s+2)*2^(s+1)*(2*m+2))+
    (s*(m*(4*d)^s)*2^(s+1))^2*(8*m+3)

lemma finalSupportWork_le {m d s : ℕ} (N : Fin m → Finset (Fin m)) (hd : 1 ≤ d) :
    finalSupportWork N d s ≤ finalSupportBound m d s := by
  have hgen : (∑ k ∈ Finset.range s, ∑ A ∈ candidateSets (next N d) k, powersetGenerationWork A) ≤
      s*(m*(4*d)^s)*((s+2)*2^(s+1)*(2*m+2)) := by
    calc
      _ ≤ ∑ _k ∈ Finset.range s, (m*(4*d)^s*((s+2)*2^(s+1)*(2*m+2))) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' := (Finset.mem_range.mp hk).le
        calc
          _ ≤ ∑ _A ∈ candidateSets (next N d) k, ((s+2)*2^(s+1)*(2*m+2)) := by
            apply Finset.sum_le_sum
            intro A hA
            exact powersetGenerationWork_le A ((candidate_card_le _ hA).trans (by omega))
          _ = (candidateSets (next N d) k).card*((s+2)*2^(s+1)*(2*m+2)) := by simp
          _ ≤ _ := by
            apply Nat.mul_le_mul_right
            have hc : (candidateSets (next N d) k).card ≤ m*(4*d)^k := by simpa using card_candidateSets_le (next N d) k
            exact hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hk'))
      _ = _ := by simp; ring
  have hdup : (∑ x ∈ rawPairSource N d s, ∑ y ∈ rawPairSource N d s,
      (keyBits (pairKey (x.2.1,x.2.2))+keyBits (pairKey (y.2.1,y.2.2))+1)) ≤
      (s*(m*(4*d)^s)*2^(s+1))^2*(8*m+3) := by
    calc
      _ ≤ ∑ _x ∈ rawPairSource N d s, ∑ _y ∈ rawPairSource N d s, (8*m+3) := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro y hy
        have hx' := pairKey_bits_le (x.2.1,x.2.2)
        have hy' := pairKey_bits_le (y.2.1,y.2.2)
        omega
      _ = (rawPairSource N d s).card^2*(8*m+3) := by simp; ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (rawPairSource_card N hd) 2)
  exact Nat.add_le_add hgen hdup

/-- The cached support prelude includes all source generation, decoding,
key construction and deduplication before degree filtering. -/
def supportPreludeWork {m : ℕ} (N : Fin m → Finset (Fin m)) (d s : ℕ) : ℕ :=
  (codeTableWithCost d s).2+
    ∑ k ∈ Finset.range s, (supportSizeWork N d k+candidateDedupWork N d k+
      ∑ A ∈ candidateSets (next N d) k, subsetKeyWork A)

def supportPreludeBound (m d s : ℕ) : ℕ :=
  codeTableBound d s+s*(supportSizeBound m d s+
    (m*(4*d)^s*membershipKeyBound m+(m*(4*d)^s)^2*(4*m+3))+
      m*(4*d)^s*((1+2^(s+1))*membershipKeyBound m))

lemma supportPreludeWork_le {m d s : ℕ} (N : Fin m → Finset (Fin m)) (hd : 1 ≤ d) :
    supportPreludeWork N d s ≤ supportPreludeBound m d s := by
  have ht := codeTable_cost_bound (s := s) hd
  have hsum : (∑ k ∈ Finset.range s, (supportSizeWork N d k+candidateDedupWork N d k+
      ∑ A ∈ candidateSets (next N d) k, subsetKeyWork A)) ≤
      s*(supportSizeBound m d s+
        (m*(4*d)^s*membershipKeyBound m+(m*(4*d)^s)^2*(4*m+3))+
          m*(4*d)^s*((1+2^(s+1))*membershipKeyBound m)) := by
    calc
      _ ≤ ∑ _k ∈ Finset.range s,
          (supportSizeBound m d s+
            (m*(4*d)^s*membershipKeyBound m+(m*(4*d)^s)^2*(4*m+3))+
              m*(4*d)^s*((1+2^(s+1))*membershipKeyBound m)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' := (Finset.mem_range.mp hk).le
        have hsize := supportSizeWork_le N hd hk'
        have hdup := candidateDedupWork_le N hd hk'
        have hkeys : (∑ A ∈ candidateSets (next N d) k, subsetKeyWork A) ≤
            m*(4*d)^s*((1+2^(s+1))*membershipKeyBound m) := by
          calc
            _ ≤ ∑ _A ∈ candidateSets (next N d) k, ((1+2^(s+1))*membershipKeyBound m) := by
              apply Finset.sum_le_sum
              intro A hA
              exact subsetKeyWork_le A ((candidate_card_le _ hA).trans (by omega))
            _ = (candidateSets (next N d) k).card*((1+2^(s+1))*membershipKeyBound m) := by simp
            _ ≤ _ := by
              have hcount0 : (candidateSets (next N d) k).card ≤ m*(4*d)^k := by
                simpa only [Fintype.card_fin] using card_candidateSets_le (next N d) k
              exact Nat.mul_le_mul_right _ (hcount0.trans
                (Nat.mul_le_mul_left m (Nat.pow_le_pow_right (show 0 < 4*d by omega) hk')))
        omega
      _ = _ := by simp
  exact Nat.add_le_add ht hsum

/-- Degree filtering reads every generated support, even those rejected. -/
def filterWork {m : ℕ} (S : Finset (Finset (Fin m) × Finset (Fin m))) (p : ℕ) : ℕ :=
  ∑ AB ∈ S, (AB.1.card+p.size+1)

/-- Complete support extraction trace of the cached executor, including the
actual uncached moment calls in every retained local recurrence. -/
def logWork {n m : ℕ} (scopes : Fin m → Finset (Fin n))
    (query : PrimitiveMomentsQ.Queries scopes) (r c s C : ℕ) (τ : ℚ) : ℕ :=
  let N := cachedNeighbors scopes
  let allPairs := cachedSupportPairs N (degreeBound r c) s
  graphWork scopes+(supportPreludeWork N (degreeBound r c) s+
      finalSupportWork N (degreeBound r c) s)+
    loopWork (Finset.Icc 1 s) (fun p => [p]) (fun p =>
      filterWork allPairs p+loopWork (allPairs.filter (fun AB => AB.1.card ≤ p)) pairKey
        (fun AB => membershipKeyWork AB.1+membershipKeyWork AB.2+
          (localWithDiscrete scopes query AB.2 p s C τ).2+AB.1.card+1))

def logBound (n m r c s J : ℕ) : ℕ :=
  let d := degreeBound r c
  let Q := m*(8*d)^s
  let W := 2*membershipKeyBound m+momentBound n m r s J*2^(s+1)+s+1
  graphWorkBound n m r+(supportPreludeBound m d s+finalSupportBound m d s)+
    (s^2*(2*s*(s+3)+6)+s*(s+3+
      (Q*(2*s+2)+(Q^2*(2*Q*(4*m+1)+6)+Q*(4*m+1+W+1)))+1))
where
  graphWorkBound (n m r : ℕ) := m*m*(2*m+2+r*r*(2*n+2))

/-- The main control trace is bounded by polynomial expressions and fixed
bases raised to the actual s,J, with no global powerset or tuple box. -/
theorem logWork_le {n m r c s C : ℕ} (scopes : Fin m → Finset (Fin n))
    (hs : ∀ e, (scopes e).card ≤ r) (query : PrimitiveMomentsQ.Queries scopes) (τ : ℚ) :
    logWork scopes query r c s C τ ≤ logBound n m r c s (Oracle.totalLevelChoice s C τ) := by
  unfold logWork
  rw [cachedNeighbors_eq]
  let d := degreeBound r c
  let S := cachedSupportPairs (neighbors scopes) d s
  let Q := m*(8*d)^s
  let J := Oracle.totalLevelChoice s C τ
  have hd : 1 ≤ d := le_max_left _ _
  have hS : S = supportPairs (neighbors scopes) d s := cachedSupportPairs_eq _ _ _
  have hcard : S.card ≤ Q := by rw [hS]; exact supportPairs_count _ hd
  have hsub : ∀ AB ∈ S, AB.2 ⊆ AB.1 ∧ AB.1.card ≤ s := by
    intro AB hAB
    rw [hS] at hAB
    have hh := (mem_supportPairs _ AB.1 AB.2).mp hAB
    exact ⟨hh.2, support_card_le _ hh.1⟩
  have hpwork : ∀ p ∈ Finset.Icc 1 s,
      filterWork S p+loopWork (S.filter (fun AB => AB.1.card ≤ p)) pairKey
        (fun AB => membershipKeyWork AB.1+membershipKeyWork AB.2+
          (localWithDiscrete scopes query AB.2 p s C τ).2+AB.1.card+1) ≤
        Q*(2*s+2)+(Q^2*(2*Q*(4*m+1)+6)+Q*(4*m+1+
          (2*membershipKeyBound m+momentBound n m r s J*2^(s+1)+s+1)+1)) := by
    intro p hp
    have hp' := Finset.mem_Icc.mp hp
    have hf : filterWork S p ≤ Q*(2*s+2) := by
      have hbit := nat_size_le_succ p
      unfold filterWork
      calc
        _ ≤ ∑ _AB ∈ S, (2*s+2) := Finset.sum_le_sum (fun AB hAB => by
          have hh := (hsub AB hAB).2; omega)
        _ = S.card*(2*s+2) := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ hcard
    apply Nat.add_le_add hf
    apply loopWork_le _ _ _ (Q := Q) (D := 4*m+1)
    · exact (Finset.card_filter_le _ _).trans hcard
    · exact fun AB _ => pairKey_bits_le AB
    · intro AB hAB
      have hb := hsub AB (Finset.mem_filter.mp hAB).1
      have hB : AB.2.card ≤ s := (Finset.card_le_card hb.1).trans hb.2
      have hl := localWithDiscrete_work_le (C := C) scopes hs query AB.2 hB hp'.2 τ
      change (localWithDiscrete scopes query AB.2 p s C τ).2 ≤ momentBound n m r s J*2^(s+1) at hl
      have ha := membershipKeyWork_le AB.1
      have hb' := membershipKeyWork_le AB.2
      omega
  have ho := loopWork_le (Finset.Icc 1 s) (fun p : ℕ => [p]) _
    (Q := s) (D := s+3) (by simp) (by
      intro p hp
      have hp' := (Finset.mem_Icc.mp hp).2
      have hb := nat_size_le_succ p
      simp only [keyBits, List.length_singleton, List.map_singleton, List.sum_singleton]
      omega) hpwork
  have hg := graphWork_le scopes hs
  have hp := supportPreludeWork_le (s := s) (neighbors scopes) hd
  have hfinal := finalSupportWork_le (s := s) (neighbors scopes) hd
  change graphWork scopes+(supportPreludeWork (neighbors scopes) d s+
    finalSupportWork (neighbors scopes) d s)+_ ≤ _
  unfold logBound logBound.graphWorkBound
  dsimp only
  simpa only [d, Q, J] using Nat.add_le_add (Nat.add_le_add hg (Nat.add_le_add hp hfinal)) ho

/-- The final scaling control reads the computed logarithm, whose encoding is
bounded from the actual preceding expression, rather than from its magnitude. -/
def expScaleArgument (L : ℚ) : Expr :=
  .node .mul (.atom 2) (.node .max (.atom L) (.node .sub (.atom 0) (.atom L)))

def expDegreeArgument (ε : ℚ) (h : ℕ) : Expr :=
  .node .div (.node .mul (.atom 12) (PrimitiveExpressions.twoPower h)) (.atom ε)

@[simp] theorem expScaleArgument_eval (L : ℚ) : (expScaleArgument L).eval = 2*|L| := by
  simp only [expScaleArgument, Expr.eval, Op.eval, zero_sub, ← abs_eq_max_neg]

@[simp] theorem expDegreeArgument_eval (ε : ℚ) (h : ℕ) :
    (expDegreeArgument ε h).eval = 1/(ε/(12*(2:ℚ)^h)) := by
  simp only [expDegreeArgument, Expr.eval, Op.eval, PrimitiveExpressions.twoPower_eval]
  by_cases he : ε=0
  · simp [he]
  · field_simp

/-- Arithmetic and integer selection of the actual scaling exponent and
Taylor degree, after the logarithm has been computed. -/
def expSelectionWork (L ε : ℚ) : ℕ :=
  binaryControlWork (expScaleArgument L)+
    binaryControlWork (expDegreeArgument ε (Algorithm.exponentialScale L))+
      BitComplexity.rationalBits L+BitComplexity.rationalBits ε+1

def expSelectionBound (H h : ℕ) : ℕ :=
  2*expressionControlBound (H+20) (h+8)+4*H+3

lemma rationalBits_le_height (q : ℚ) : BitComplexity.rationalBits q ≤ 2*height q+1 := by
  unfold BitComplexity.rationalBits height
  omega

lemma expSelectionWork_le {L ε : ℚ} {H : ℕ} (hL : height L ≤ H) (hε : height ε ≤ H) :
    expSelectionWork L ε ≤ 20000*expSelectionBound H (Algorithm.exponentialScale L) := by
  have h2 := PrimitiveExpressions.height_two
  have h0 : height (0:ℚ) ≤ 1 := by simp [height]
  have h12 : height (12:ℚ) ≤ 13 := by
    exact RationalRecurrenceProgram.height_natCast_le (j := 12) (s := 12) le_rfl
  have hs : (expScaleArgument L).inputHeight ≤ H+20 := by
    simp only [expScaleArgument, Expr.inputHeight]
    rw [h2]
    exact max_le (by omega) (max_le (by omega) (max_le (by omega) (by omega)))
  have hd : (expDegreeArgument ε (Algorithm.exponentialScale L)).inputHeight ≤ H+20 := by
    apply max_le
    · apply max_le
      · exact h12.trans (by omega)
      · exact (PrimitiveExpressions.twoPower_inputHeight _).trans (by omega)
    · exact hε.trans (by omega)
  have hsc := expressionControlWork_le (expScaleArgument L) hs
    (P := Algorithm.exponentialScale L+8) (by simp [expScaleArgument, Expr.operations])
  have hdc := expressionControlWork_le (expDegreeArgument ε (Algorithm.exponentialScale L)) hd
    (P := Algorithm.exponentialScale L+8) (by simp [expDegreeArgument, Expr.operations, PrimitiveExpressions.twoPower_operations])
  have hsc' := (binaryControlWork_le (expScaleArgument L)).trans (Nat.mul_le_mul_left 20000 hsc)
  have hdc' := (binaryControlWork_le (expDegreeArgument ε (Algorithm.exponentialScale L))).trans
    (Nat.mul_le_mul_left 20000 hdc)
  have hbL := rationalBits_le_height L
  have hbε := rationalBits_le_height ε
  unfold expSelectionWork expSelectionBound
  omega

/-- Actual encoding-height budget of the computed logarithm, from the
preceding program and the original effective-access assumption. -/
def logHeightBound {n m : ℕ} (p : Parameters.Fixed) (r c A degree L : ℕ) (ε : ℚ) : ℕ :=
  let s := Parameters.truncationOrder p m ε
  let J := Parameters.level p m ε
  let P := Parameters.precision p m ε
  let M := FPTASProgram.logNodes m r c s P J
  PrimitiveInputHeight.inputBound A degree L r J P s*(M+1)+2*M

/-- Complete discrete trace of the cached arithmetic executor. Parameter
selection and AST construction are included; oracle evaluation time is the
separate original-access trace supplied by `FPTASOracleTime`. -/
def completeDiscreteWork {n m : ℕ} (p : Parameters.Fixed) (scopes : Fin m → Finset (Fin n))
    (query : PrimitiveMomentsQ.Queries scopes) (r c : ℕ) (ε : ℚ) : ℕ :=
  if m=0 then 1 else
    let s := Parameters.truncationOrder p m ε
    let τ := Parameters.primitiveTolerance p m ε
    let L := cachedLogApprox scopes query r c s p.C τ
    parameterWork p m ε+logWork scopes query r c s p.C τ+expSelectionWork L ε+
      (cachedRunProgram p scopes query r c ε).operations+1

/-- Numerical bound for every actual non-oracle discrete control stage. -/
def completeDiscreteBound {n m : ℕ} (p : Parameters.Fixed) (scopes : Fin m → Finset (Fin n))
    (query : PrimitiveMomentsQ.Queries scopes) (r c A degree L : ℕ) (ε : ℚ) : ℕ :=
  let s := Parameters.truncationOrder p m ε
  let J := Parameters.level p m ε
  let T := cachedLogApprox scopes query r c s p.C (Parameters.primitiveTolerance p m ε)
  20000*parameterBound p m ε+logBound n m r c s J+
    20000*expSelectionBound (logHeightBound (n := n) (m := m) p r c A degree L ε+
      BitComplexity.rationalBits ε+1) (Algorithm.exponentialScale T)+
      FPTASProgram.runNodeBound p scopes query r c ε+1

/-- All control bounds are derived for the actual computed values and oracle
answers. No running-time or answer-size conclusion is assumed as a certificate. -/
theorem completeDiscreteWork_le {n m r c A degree L : ℕ} (p : Parameters.Fixed)
    (scopes : Fin m → Finset (Fin n)) (hs : ∀ e, (scopes e).card ≤ r)
    (Ψ : (i : Fin m) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin m → ℕ)
    (O : (i : Fin m) → EffectiveAccess.Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (hlabels : ∀ i, labelBits i ≤ L) (ε : ℚ) :
    completeDiscreteWork p scopes (fun i => (O i).valueOracle.query) r c ε ≤
      completeDiscreteBound p scopes (fun i => (O i).valueOracle.query) r c A degree L ε := by
  by_cases hm : m=0
  · simp only [completeDiscreteWork, if_pos hm]
    unfold completeDiscreteBound
    exact Nat.le_add_left 1 _
  let query : PrimitiveMomentsQ.Queries scopes := fun i => (O i).valueOracle.query
  let s := Parameters.truncationOrder p m ε
  let τ := Parameters.primitiveTolerance p m ε
  let J := Parameters.level p m ε
  let P := Parameters.precision p m ε
  let T := FPTASProgram.logProgram scopes query r c s p.C τ
  let M := FPTASProgram.logNodes m r c s P J
  have ht := T.height_le
  have hop : T.operations ≤ M := FPTASProgram.logProgram_operations (c := c) scopes hs query τ
  have hin : T.inputHeight ≤ PrimitiveInputHeight.inputBound A degree L r J P s :=
    FPTASProgram.logProgram_inputHeight scopes hs Ψ labelBits O hlabels τ
  have hheight : height T.eval ≤ logHeightBound (n := n) (m := m) p r c A degree L ε := by
    apply ht.trans
    unfold logHeightBound
    change T.inputHeight*(T.operations+1)+2*T.operations ≤
      PrimitiveInputHeight.inputBound A degree L r J P s*(M+1)+2*M
    gcongr
  have hLT : cachedLogApprox scopes query r c s p.C τ = T.eval := by
    rw [cachedLogApprox_eq]
    exact (FPTASProgram.logProgram_eval _ _ _ _ _ _ _).symm
  have he := expSelectionWork_le (L := T.eval) (ε := ε)
    (H := logHeightBound (n := n) (m := m) p r c A degree L ε+BitComplexity.rationalBits ε+1)
    (hheight.trans (by omega))
    ((PrimitiveInputHeight.height_le_rationalBits ε).trans (by omega))
  have hp := parameterWork_le p m ε
  have hl := logWork_le (s := s) (c := c) (C := p.C) scopes hs query τ
  have hn := FPTASProgram.runProgram_operations_le (c := c) p scopes hs query ε
  rw [← cachedRunProgram_eq] at hn
  change completeDiscreteWork p scopes query r c ε ≤ completeDiscreteBound p scopes query r c A degree L ε
  unfold completeDiscreteWork
  rw [if_neg hm]
  unfold completeDiscreteBound
  change parameterWork p m ε+logWork scopes query r c s p.C τ+
      expSelectionWork (cachedLogApprox scopes query r c s p.C τ) ε+
      (cachedRunProgram p scopes query r c ε).operations+1 ≤ _
  rw [← hLT] at he
  change logWork scopes query r c s p.C τ ≤ logBound n m r c s J at hl
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hp hl) he) hn) 1

/-- The implemented answer is produced by the exact schoolbook executor on
the cached program. Its trace includes its actual discrete construction. -/
def implementedRun {n m : ℕ} (p : Parameters.Fixed) (scopes : Fin m → Finset (Fin n))
    (query : PrimitiveMomentsQ.Queries scopes) (r c : ℕ) (ε : ℚ) : ℚ × ℕ :=
  let execution := execute (cachedRunProgram p scopes query r c ε)
  (execution.1, execution.2+completeDiscreteWork p scopes query r c ε)

@[simp] theorem implementedRun_value {n m : ℕ} (p : Parameters.Fixed)
    (scopes : Fin m → Finset (Fin n)) (query : PrimitiveMomentsQ.Queries scopes)
    (r c : ℕ) (ε : ℚ) : (implementedRun p scopes query r c ε).1 = run p scopes query r c ε :=
  execute_cachedRunProgram_value p scopes query r c ε

end Paper08.FPTASDiscreteCost

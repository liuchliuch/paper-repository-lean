import SemidegreeExt.ConstructionAlgorithm
import SemidegreeExt.FlowCost
open Finset
namespace SemidegreeExt.ConstructionAlgorithm
open FlowAlgorithm

/-- Source edges, all possible left-right pairs, and sink edges form an explicit
edge envelope. Positive-capacity arcs are a subset of this O(dn) envelope. -/
def edgeEnvelope (n d : ℕ) : Finset (Vertex n d × Vertex n d) :=
  ((univ : Finset (Fin d)).image fun i => (source n d,left (n := n) i)) ∪
  (((univ : Finset (Fin d)).product (univ : Finset (Fin n))).image fun e => (left (n := n) e.1,right (d := d) e.2)) ∪
  ((univ : Finset (Fin n)).image fun j => (right (d := d) j,sink n d))

def positiveEdges (n d c : ℕ) : Finset (Vertex n d × Vertex n d) :=
  univ.filter fun e => 0 < capacity n d c e.1 e.2

lemma positiveEdges_subset (n d c : ℕ) : positiveEdges n d c ⊆ edgeEnvelope n d := by
  intro e he
  have hpos := (mem_filter.mp he).2
  obtain ⟨u,v⟩ := e
  cases u with
  | inl a =>
    cases v with
    | inl b => simp [capacity] at hpos
    | inr v =>
      cases v with
      | inl i =>
        have ha : a=0 := by by_contra h; simp [capacity,h] at hpos
        subst a
        simp [edgeEnvelope,source,left]
      | inr j => simp [capacity] at hpos
  | inr u =>
    cases u with
    | inl i =>
      cases v with
      | inl a => simp [capacity] at hpos
      | inr v =>
        cases v with
        | inl i' => simp [capacity] at hpos
        | inr j => simp [edgeEnvelope,left,right]
    | inr j =>
      cases v with
      | inl a =>
        have ha : a=1 := by by_contra h; simp [capacity,h] at hpos
        subst a
        simp [edgeEnvelope,right,sink]
      | inr v => cases v <;> simp [capacity] at hpos

lemma edgeEnvelope_count (n d : ℕ) : (edgeEnvelope n d).card ≤ d+d*n+n := by
  unfold edgeEnvelope
  have h1 := card_image_le (s := (univ : Finset (Fin d))) (f := fun i => (source n d,left (n := n) i))
  have h2 := card_image_le (s := (univ : Finset (Fin d)).product (univ : Finset (Fin n))) (f := fun e : Fin d × Fin n => (left (n := n) e.1,right (d := d) e.2))
  have h3 := card_image_le (s := (univ : Finset (Fin n))) (f := fun j => (right (d := d) j,sink n d))
  have h12 := card_union_le ((univ : Finset (Fin d)).image fun i => (source n d,left (n := n) i))
    (((univ : Finset (Fin d)).product (univ : Finset (Fin n))).image fun e => (left (n := n) e.1,right (d := d) e.2))
  have hall := card_union_le
    (((univ : Finset (Fin d)).image fun i => (source n d,left (n := n) i)) ∪
      (((univ : Finset (Fin d)).product (univ : Finset (Fin n))).image fun e => (left (n := n) e.1,right (d := d) e.2)))
    ((univ : Finset (Fin n)).image fun j => (right (d := d) j,sink n d))
  have hprod : ((univ : Finset (Fin d)).product (univ : Finset (Fin n))).card = d*n := by
    change ((univ : Finset (Fin d)) ×ˢ (univ : Finset (Fin n))).card = _
    simp
  simp only [card_univ,Fintype.card_fin,hprod] at h1 h2 h3
  omega

/-- The explicit network has O(n) vertices and O(dn) positive-capacity edges. -/
theorem network_size (n d c : ℕ) (hd : 1 ≤ d) (hdn : d < n) :
    Fintype.card (Vertex n d) ≤ 3*n ∧ (positiveEdges n d c).card ≤ 3*d*n := by
  constructor
  · rw [vertex_count]
    omega
  · have h := (card_le_card (positiveEdges_subset n d c)).trans (edgeEnvelope_count n d)
    have hdn0 : 1 ≤ n := by omega
    have h1 : d ≤ d*n := by nlinarith
    have h2 : n ≤ d*n := by nlinarith
    nlinarith

/-- Reading the integer matrix along every candidate original arc, with its
actual elementary evaluation charge. The result is a list of distinct arcs,
so no parallel-arc repair or hidden search is needed. -/
def collectForwardCost {n d : ℕ} (updates : List (Vertex n d × Vertex n d)) :
    List (Fin n × Fin n) → List (Fin n × Fin n) × ℕ
  | [] => ([],1)
  | e::es =>
    let rest := collectForwardCost updates es
    if hi : e.1.val < d then
      let z := evalCost updates (left ⟨e.1.val,hi⟩) (right e.2)
      if z.1=1 then (e::rest.1,rest.2+z.2+5) else (rest.1,rest.2+z.2+5)
    else (rest.1,rest.2+3)

lemma collectForward_mem {n d : ℕ} (updates : List (Vertex n d × Vertex n d))
    (xs : List (Fin n × Fin n)) (e : Fin n × Fin n) :
    e ∈ (collectForwardCost updates xs).1 ↔ e ∈ xs ∧
      ∃ hi : e.1.val < d, applyRoute (fun _ _ => 0) updates (left ⟨e.1.val,hi⟩) (right e.2)=1 := by
  induction xs with
  | nil => simp [collectForwardCost]
  | cons a xs ih =>
    simp only [collectForwardCost]
    split_ifs with ha hz
    · simp only [List.mem_cons,ih]
      constructor
      · rintro (rfl | ⟨h,hh⟩)
        · exact ⟨Or.inl rfl,ha,by simpa only [evalCost_value] using hz⟩
        · exact ⟨Or.inr h,hh⟩
      · rintro ⟨rfl | h,hh⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h,hh⟩
    · simp only [ih,List.mem_cons]
      constructor
      · rintro ⟨h,hh⟩; exact ⟨Or.inr h,hh⟩
      · rintro ⟨rfl | h,hh⟩
        · obtain ⟨_,hh⟩ := hh
          exact (hz (by simpa only [evalCost_value] using hh)).elim
        · exact ⟨h,hh⟩
    · simp only [ih,List.mem_cons]
      constructor
      · rintro ⟨h,hh⟩; exact ⟨Or.inr h,hh⟩
      · rintro ⟨rfl | h,hh⟩
        · exact (ha hh.1).elim
        · exact ⟨h,hh⟩

lemma collectForward_bound {n d : ℕ} (updates : List (Vertex n d × Vertex n d))
    (xs : List (Fin n × Fin n)) :
    (collectForwardCost updates xs).2 ≤ xs.length*(10*updates.length+10)+1 := by
  induction xs with
  | nil => simp [collectForwardCost]
  | cons e es ih =>
    simp only [collectForwardCost]
    split_ifs <;> simp only [evalCost_cost,List.length_cons] <;> nlinarith

/-- Executable output and word-operation count for constructing all forward arcs. -/
def construct (n d c : ℕ) : List (Fin n × Fin n) × ℕ :=
  let z := runCost (capacity n d c) (source n d) (sink n d) (demandTotal d)
  let arcs := collectForwardCost z.1 (pairs (V := Fin n))
  (arcs.1,z.2+arcs.2)

lemma construct_eq_forward (n d c : ℕ) :
    (construct n d c).1.toFinset = computedForward n d c := by
  ext e
  simp only [construct,List.mem_toFinset,collectForward_mem,mem_pairs,true_and,
    runCost_refines,program_refines,computedForward,mem_filter]
  have hu : e ∈ ((univ : Finset (Fin n)).product (univ : Finset (Fin n))) := by
    change e ∈ ((univ : Finset (Fin n)) ×ˢ (univ : Finset (Fin n)))
    simp
  simp only [hu,true_and]
  split_ifs with hi
  · simp [hi,computedFlow]
  · simp [hi]

/-- Explicit polynomial, including construction of the output list. -/
def constructionBudget (N R n : ℕ) := workBudget N R+n^2*(10*(R*N)+10)+1

lemma construct_cost_bound (n d c : ℕ) :
    (construct n d c).2 ≤ constructionBudget (d+n+2) (demandTotal d) n := by
  have hr := runCost_bound (capacity n d c) (source n d) (sink n d) (demandTotal d) (demandTotal d) (le_refl _)
  have hl : (runCost (capacity n d c) (source n d) (sink n d) (demandTotal d)).1.length ≤ demandTotal d*(d+n+2) := by
    rw [runCost_refines]
    simpa only [vertex_count] using program_length (capacity n d c) (source n d) (sink n d) (demandTotal d)
  have ho := collectForward_bound (runCost (capacity n d c) (source n d) (sink n d) (demandTotal d)).1 (pairs (V := Fin n))
  rw [pairs_length,Fintype.card_fin] at ho
  simp only [vertex_count] at hr
  dsimp only [construct]
  unfold constructionBudget workBudget
  have hmul := Nat.mul_le_mul_left (n^2) (Nat.add_le_add_right (Nat.mul_le_mul_left 10 hl) 10)
  omega

/-- Bounded integer search for C; no real square-root computation is executed. -/
def thresholdCost (n d : ℕ) : Option ℕ × ℕ :=
  scanCost (fun c => (decide (d*(d+1)+c*(c+1) ≤ 2*c*n),10)) (List.range (d+1))

lemma thresholdCost_correct (n d : ℕ) (hd : d < n) :
    (thresholdCost n d).1 = some (C n d) ∧ (thresholdCost n d).2 ≤ 11*(d+1)+1 := by
  constructor
  · rw [thresholdCost,scanCost_value,List.find?_eq_some_iff_getElem]
    refine ⟨by simpa using C_spec n d hd, C n d,?_,?_,?_⟩
    · simpa only [List.length_range] using Nat.lt_succ_of_le (C_le_d n d hd)
    · simp
    · intro j hj
      have hnot : ¬ d*(d+1)+j*(j+1) ≤ 2*j*n := fun h =>
        (not_le_of_gt hj) (C_is_least n d hd h)
      simp [hnot]
  · have h := scanCost_bound (fun c : ℕ => (decide (d*(d+1)+c*(c+1) ≤ 2*c*n),10)) (List.range (d+1)) 10 (fun _ => le_refl _)
    simpa [thresholdCost,Nat.mul_comm] using h
/-- Backward completion is a fixed explicit formula; it performs no search. -/
def completeForward (n d : ℕ) (F : Finset (Fin n × Fin n)) : Digraph (Fin n) :=
  ⟨fun i j => (i,j) ∈ F ∨ j.val < min i.val d⟩

lemma completeForward_correct (n d : ℕ) (hn : 0 < n) (hd : d < n)
    (F : Finset (Fin n × Fin n))
    (hF : ∀ i j, (i,j) ∈ F → i.val < d ∧ i.val < j.val)
    (hout : ∀ i, i.val < d → (F.filter fun e => e.1=i).card = d-i.val)
    (hin : ∀ j, (F.filter fun e => e.2=j).card ≤ C n d) :
    Loopless (completeForward n d F) ∧ (∀ v, outDeg (completeForward n d F) v = d) ∧
      q (completeForward n d F) = C n d := by
  classical
  let G := completeForward n d F
  have hloop : Loopless G := by
    intro i hi
    rcases hi with hf | hb
    · have := (hF i i hf).2
      omega
    · have := min_le_left i.val d
      omega
  have hrows (i : Fin n) : (F.filter fun e => e.1 = i).card = d - i.val := by
    by_cases hi : i.val < d
    · exact hout i hi
    · have he : F.filter (fun e => e.1 = i) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro e he
        have hh := hF e.1 e.2 (mem_filter.mp he).1
        exact hi ((mem_filter.mp he).2 ▸ hh.1)
      rw [he, card_empty, Nat.sub_eq_zero_of_le (by omega)]
  have hdeg (i : Fin n) : outDeg G i = d := by
    have hforward : (univ.filter fun j : Fin n => (i,j) ∈ F).card =
        (F.filter fun e => e.1 = i).card := by
      apply card_bij (fun j _ => (i,j))
      · intro j hj
        exact mem_filter.mpr ⟨(mem_filter.mp hj).2, rfl⟩
      · intro j _ j' _ he
        exact congrArg Prod.snd he
      · rintro ⟨i',j⟩ he
        obtain rfl := (mem_filter.mp he).2
        exact ⟨j, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp he).1⟩, rfl⟩
    have hback : (univ.filter fun j : Fin n => j.val < min i.val d).card = min i.val d := by
      have hmin : min i.val d < n := (min_le_left _ _).trans_lt i.isLt
      have he : (univ.filter fun j : Fin n => j.val < min i.val d) = Iio (⟨min i.val d, hmin⟩ : Fin n) := by
        ext j
        simp only [mem_filter, mem_univ, true_and, mem_Iio]
        rfl
      rw [he, Fin.card_Iio]
    have hdis : Disjoint (univ.filter fun j : Fin n => (i,j) ∈ F)
        (univ.filter fun j : Fin n => j.val < min i.val d) := by
      apply disjoint_left.mpr
      intro j hj hb
      have hh := (hF i j (mem_filter.mp hj).2).2
      have hb' := (mem_filter.mp hb).2
      have := min_le_left i.val d
      omega
    have heq : univ.filter (G.Adj i) =
        (univ.filter fun j : Fin n => (i,j) ∈ F) ∪
        (univ.filter fun j : Fin n => j.val < min i.val d) := by
      ext j
      simp only [mem_filter, mem_union, mem_univ, true_and]
      rfl
    calc
      outDeg G i = ((univ.filter fun j : Fin n => (i,j) ∈ F) ∪
          (univ.filter fun j : Fin n => j.val < min i.val d)).card := by
        unfold outDeg
        congr 1
      _ = d := by
        rw [card_union_of_disjoint hdis, hforward, hrows, hback]
        omega
  refine ⟨hloop, hdeg, le_antisymm ?_ (C_le_q n d hn hd G hloop (fun i => (hdeg i).ge))⟩
  unfold q
  apply Finset.sup_le
  intro S hS
  have hs : S.Nonempty := (mem_filter.mp hS).2
  let j := S.max' hs
  have hj : j ∈ S := max'_mem S hs
  have hinc : inDegOn G S j ≤ (F.filter fun e => e.2 = j).card := by
    unfold inDegOn
    apply card_le_card_of_injOn (fun i : Fin n => (i,j))
    · intro i hi
      simp only [Finset.mem_coe, mem_filter] at hi
      have hai : G.Adj i j := hi.2
      have hij : i ≤ j := le_max' S i hi.1
      have hf : (i,j) ∈ F := by
        rcases hai with hf | hb
        · exact hf
        · have := min_le_left i.val d
          have hij' : i.val ≤ j.val := hij
          omega
      exact mem_filter.mpr ⟨hf, rfl⟩
    · intro i _ i' _ he
      exact congrArg Prod.fst he
  have hsemi : minSemiDegOn G S ≤ inDegOn G S j := by
    rw [minSemiDegOn, dif_pos hs]
    exact (Finset.inf'_le (semiDegOn G S) hj).trans (min_le_right _ _)
  exact hsemi.trans (hinc.trans (hin j))

/-- Complete executable construction, including the bounded integer threshold search. -/
def solve (n d : ℕ) : List (Fin n × Fin n) × ℕ :=
  let tc := thresholdCost n d
  let z := construct n d (tc.1.getD 0)
  (z.1,tc.2+z.2)

def outputGraph (n d : ℕ) : Digraph (Fin n) :=
  let arcs := (solve n d).1
  ⟨fun i j => (i,j) ∈ arcs ∨ j.val < min i.val d⟩

lemma solve_eq_forward (n d : ℕ) (hd : d < n) :
    (solve n d).1.toFinset = computedForward n d (C n d) := by
  simp only [solve,(thresholdCost_correct n d hd).1,Option.getD_some]
  exact construct_eq_forward n d (C n d)

/-- The actual executable output is an extremal graph, not merely an existence
witness or an algorithm carrying the desired conclusion as an assumption. -/
theorem outputGraph_correct (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    Loopless (outputGraph n d) ∧ (∀ v, outDeg (outputGraph n d) v = d) ∧
      q (outputGraph n d) = C n d := by
  have heq : outputGraph n d = completeForward n d (computedForward n d (C n d)) := by
    ext i j
    change ((i,j) ∈ (solve n d).1 ∨ _) ↔ _
    rw [← List.mem_toFinset,solve_eq_forward n d hd]
    rfl
  rw [heq]
  obtain ⟨hF,hout,hin⟩ := computedForward_correct n d (C n d) hd (C_spec n d hd)
  exact completeForward_correct n d hn hd _ hF hout hin

lemma constructionBudget_mono {N M R S n : ℕ} (hNM : N ≤ M) (hRS : R ≤ S) :
    constructionBudget N R n ≤ constructionBudget M S n := by
  unfold constructionBudget workBudget searchBudget
  gcongr

lemma demandTotal_le_square (n d : ℕ) (hd : d < n) : demandTotal d ≤ n^2 := by
  have h := demandTotal_doubled d
  have hprod : d*(d+1) ≤ n*n := by gcongr <;> omega
  nlinarith

/-- A single-variable explicit polynomial upper bound for all computed work.
The extra n^4 term allows materializing the complete adjacency matrix from the
returned forward-arc list and fixed backward rule. -/
def polynomialBudget (n : ℕ) : ℕ :=
  constructionBudget (3*n) (n^2) n + 11*(n+1)+1+n^4

/-- Actual construction cost is bounded by an explicit degree-eight polynomial.
The model charges primitive vertex/word comparisons, integer arithmetic,
list inspections, allocation and route/output copying; no residual oracle is assumed. -/
theorem solve_polynomial_cost (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    (solve n d).2 ≤ polynomialBudget n := by
  have ht := (thresholdCost_correct n d hd).2
  have hc := construct_cost_bound n d (C n d)
  have hN : d+n+2 ≤ 3*n := by omega
  have hR := demandTotal_le_square n d hd
  have hp := constructionBudget_mono (n := n) hN hR
  dsimp only [solve]
  rw [(thresholdCost_correct n d hd).1,Option.getD_some]
  unfold polynomialBudget
  omega

/-- Every stage up to the full integral value is valid, with unit increases.
This gives the original upper bound d(d+1)/2 on integer augmentations. -/
theorem augmentation_bound (n d c : ℕ) (hd : d < n)
    (hc : d*(d+1)+c*(c+1) ≤ 2*c*n) :
    ∀ k ≤ d*(d+1)/2,
      Valid (capacity n d c) (source n d) (sink n d)
        (run (capacity n d c) (source n d) (sink n d) k) ∧
      divergence (run (capacity n d c) (source n d) (sink n d) k) (source n d) = k := by
  obtain ⟨F,hF,hout,hin⟩ := nested_placement n d c hd hc
  have hv : Valid (capacity n d c) (source n d) (sink n d) (witness hd.le F) :=
    ⟨witness_skew hd.le F,witness_bounded hd.le F hF hout hin,witness_conserve hd.le F⟩
  have hval := witness_source_value hd.le F hout
  rw [demandTotal_eq] at hval
  exact run_correct (by simp [source,sink]) hv _ hval

/-- The complete algorithmic assertion in S3.p13, for the original threshold. -/
theorem polynomial_construction (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    Loopless (outputGraph n d) ∧ (∀ v, outDeg (outputGraph n d) v = d) ∧
    q (outputGraph n d) = C n d ∧ (solve n d).2 ≤ polynomialBudget n ∧
    demandTotal d = d*(d+1)/2 := by
  obtain ⟨hl,hdeg,hq⟩ := outputGraph_correct n d hn hd
  exact ⟨hl,hdeg,hq,solve_polynomial_cost n d hn hd,demandTotal_eq d⟩
/-- Expanded degree-eight polynomial, making the complexity class explicit. -/
lemma polynomialBudget_expanded (n : ℕ) :
    polynomialBudget n = 810*n^8+405*n^6+651*n^5+55*n^4+51*n^3+21*n^2+11*n+14 := by
  unfold polynomialBudget constructionBudget workBudget searchBudget
  ring

lemma polynomialBudget_le (n : ℕ) (hn : 0 < n) : polynomialBudget n ≤ 2018*n^8 := by
  rw [polynomialBudget_expanded]
  have h1 : n ≤ n^8 := by simpa only [pow_one] using pow_le_pow_right₀ (by omega : 1 ≤ n) (show 1 ≤ 8 by omega)
  have h2 := pow_le_pow_right₀ (by omega : 1 ≤ n) (show 2 ≤ 8 by omega)
  have h3 := pow_le_pow_right₀ (by omega : 1 ≤ n) (show 3 ≤ 8 by omega)
  have h4 := pow_le_pow_right₀ (by omega : 1 ≤ n) (show 4 ≤ 8 by omega)
  have h5 := pow_le_pow_right₀ (by omega : 1 ≤ n) (show 5 ≤ 8 by omega)
  have h6 := pow_le_pow_right₀ (by omega : 1 ≤ n) (show 6 ≤ 8 by omega)
  have h0 : 1 ≤ n^8 := one_le_pow₀ (by omega)
  omega

/-- Uniform polynomial running-work bound for the actual executable solver. -/
theorem uniform_polynomial_time (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    (solve n d).2 ≤ 2018*n^8 :=
  (solve_polynomial_cost n d hn hd).trans (polynomialBudget_le n hn)

lemma delta_abs_bound {V : Type*} [DecidableEq V] (a b u v : V) :
    |FlowAlgorithm.delta a b u v| ≤ 1 := by
  unfold FlowAlgorithm.delta
  split_ifs <;> norm_num

lemma evalCost_abs_bound {V : Type*} [DecidableEq V] (es : List (V × V)) (u v : V) :
    |(FlowAlgorithm.evalCost es u v).1| ≤ (es.length : ℤ) := by
  induction es with
  | nil => simp [FlowAlgorithm.evalCost]
  | cons e es ih =>
    obtain ⟨a,b⟩ := e
    change |(FlowAlgorithm.evalCost es u v).1 + FlowAlgorithm.delta a b u v| ≤ _
    calc
      _ ≤ |(FlowAlgorithm.evalCost es u v).1| + |FlowAlgorithm.delta a b u v| := abs_add_le _ _
      _ ≤ (es.length : ℤ)+1 := add_le_add ih (delta_abs_bound a b u v)
      _ = _ := by simp

lemma capacity_le_n (n d c : ℕ) (hn : 0 < n) (hd : d ≤ n) (hc : c ≤ n)
    (u v : Vertex n d) : capacity n d c u v ≤ n := by
  rcases u with a | (i | j) <;> rcases v with b | (i' | j') <;>
    simp only [capacity] <;> (first | omega | (split_ifs <;> omega))

/-- All intermediate integer values produced while evaluating any suffix of
the accumulated update program have polynomial magnitude. This rules out an
unbounded-integer oracle hidden inside the word-operation complexity model. -/
theorem intermediate_integer_bound (n d : ℕ) (hn : 0 < n) (hd : d < n)
    (es : List (Vertex n d × Vertex n d))
    (hs : es.IsSuffix (runCost (capacity n d (C n d)) (source n d) (sink n d) (demandTotal d)).1)
    (u v : Vertex n d) :
    |(evalCost es u v).1| ≤ 3*(n : ℤ)^3 ∧ capacity n d (C n d) u v ≤ n := by
  have hl : (runCost (capacity n d (C n d)) (source n d) (sink n d) (demandTotal d)).1.length ≤ demandTotal d*(d+n+2) := by
    rw [runCost_refines]
    simpa only [vertex_count] using program_length (capacity n d (C n d)) (source n d) (sink n d) (demandTotal d)
  have hN : d+n+2 ≤ 3*n := by omega
  have hR := demandTotal_le_square n d hd
  have hprod : demandTotal d*(d+n+2) ≤ 3*n^3 := by
    calc
      _ ≤ n^2*(3*n) := Nat.mul_le_mul hR hN
      _ = _ := by ring
  have hes : es.length ≤ 3*n^3 := hs.length_le.trans (hl.trans hprod)
  refine ⟨(evalCost_abs_bound es u v).trans ?_,capacity_le_n n d _ hn hd.le ((C_le_d n d hd).trans hd.le) u v⟩
  exact_mod_cast hes
lemma collectForward_sublist {n d : ℕ} (updates : List (Vertex n d × Vertex n d))
    (xs : List (Fin n × Fin n)) : (collectForwardCost updates xs).1.Sublist xs := by
  induction xs with
  | nil => exact List.Sublist.refl _
  | cons e es ih =>
    simp only [collectForwardCost]
    split_ifs
    · exact List.Sublist.cons₂ e ih
    · exact List.Sublist.cons e ih
    · exact List.Sublist.cons e ih

lemma construct_nodup (n d c : ℕ) : (construct n d c).1.Nodup := by
  have hp : (pairs (V := Fin n)).Nodup := by
    change ((vertices (V := Fin n)) ×ˢ (vertices (V := Fin n))).Nodup
    exact List.Nodup.product Enumeration.nodup Enumeration.nodup
  exact (collectForward_sublist _ _).nodup hp

/-- The original right vertex numbered 1 has no incoming forward edge and its
sink edge always carries zero, justifying its harmless removal from the network. -/
lemma right_zero_unused (n d c : ℕ) (hn : 0 < n) (f : Matrix (Vertex n d))
    (hf : Valid (capacity n d c) (source n d) (sink n d) f) :
    f (right ⟨0,hn⟩) (sink n d) = 0 := by
  have hzero (i : Fin d) : f (left i) (right (⟨0,hn⟩ : Fin n)) = 0 := by
    have hb := flow_entry_binary hf i (⟨0,hn⟩ : Fin n)
    have hh : ¬i.val < (⟨0,hn⟩ : Fin n).val := by simp
    omega
  have hcons := hf.2.2 (right (⟨0,hn⟩ : Fin n)) (by simp [right,source]) (by simp [right,sink])
  rw [right_divergence hf] at hcons
  simpa only [hzero,sum_const_zero,sub_zero] using hcons
/-- One graph-entry computation, with explicit membership and backward-rule costs. -/
def graphEntryCost {n : ℕ} (d : ℕ) (forward : List (Fin n × Fin n)) (e : Fin n × Fin n) : Bool × ℕ :=
  let z := memCost e forward
  (z.1 || decide (e.2.val < min e.1.val d),z.2+5)

/-- Full executable adjacency-list construction, including every backward arc.
The forward list is computed and cached once before completing the graph. -/
def fullSolve (n d : ℕ) : List (Fin n × Fin n) × ℕ :=
  let forward := solve n d
  let all := filterCost (graphEntryCost d forward.1) (pairs (V := Fin n))
  (all.1,forward.2+all.2+6*n^2+6*n+6)

def fullOutputGraph (n d : ℕ) : Digraph (Fin n) :=
  let arcs := (fullSolve n d).1
  ⟨fun i j => (i,j) ∈ arcs⟩

lemma fullOutputGraph_eq (n d : ℕ) : fullOutputGraph n d = outputGraph n d := by
  ext i j
  simp [fullOutputGraph,fullSolve,filterCost_value,graphEntryCost,memCost_value,outputGraph]

lemma solve_length (n d : ℕ) : (solve n d).1.length ≤ n^2 := by
  dsimp only [solve,construct]
  have h := List.Sublist.length_le (collectForward_sublist
    (runCost (capacity n d ((thresholdCost n d).1.getD 0)) (source n d) (sink n d) (demandTotal d)).1
    (pairs (V := Fin n)))
  simpa only [pairs_length,Fintype.card_fin] using h

/-- Complete graph construction has a uniform degree-eight running-work bound. -/
theorem fullSolve_polynomial_time (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    (fullSolve n d).2 ≤ 2048*n^8 := by
  have hz := uniform_polynomial_time n d hn hd
  have hl := solve_length n d
  have hg (e : Fin n × Fin n) : (graphEntryCost d (solve n d).1 e).2 ≤ 2*n^2+6 := by
    have h := memCost_bound e (solve n d).1
    dsimp only [graphEntryCost]
    omega
  have hf := filterCost_bound (graphEntryCost d (solve n d).1) (pairs (V := Fin n)) (2*n^2+6) hg
  rw [pairs_length,Fintype.card_fin] at hf
  have h2 := pow_le_pow_right₀ (by omega : 1 ≤ n) (show 2 ≤ 8 by omega)
  have h4 := pow_le_pow_right₀ (by omega : 1 ≤ n) (show 4 ≤ 8 by omega)
  have h0 : 1 ≤ n^8 := one_le_pow₀ (by omega)
  have h1 : n ≤ n^8 := by simpa only [pow_one] using pow_le_pow_right₀ (by omega : 1 ≤ n) (show 1 ≤ 8 by omega)
  dsimp only [fullSolve]
  nlinarith

/-- Algorithmic S3.p13 with a complete explicit output adjacency list. -/
theorem full_construction_correct (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    Loopless (fullOutputGraph n d) ∧ (∀ v, outDeg (fullOutputGraph n d) v = d) ∧
    q (fullOutputGraph n d) = C n d ∧ (fullSolve n d).2 ≤ 2048*n^8 ∧
    (fullSolve n d).1.Nodup := by
  have hG := outputGraph_correct n d hn hd
  rw [← fullOutputGraph_eq] at hG
  refine ⟨hG.1,hG.2.1,hG.2.2,fullSolve_polynomial_time n d hn hd,?_⟩
  dsimp only [fullSolve]
  rw [filterCost_value]
  apply List.Nodup.filter
  change ((vertices (V := Fin n)) ×ˢ (vertices (V := Fin n))).Nodup
  exact List.Nodup.product Enumeration.nodup Enumeration.nodup
end SemidegreeExt.ConstructionAlgorithm

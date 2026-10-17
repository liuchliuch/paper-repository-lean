import SemidegreeExt.Main
import SemidegreeExt.FlowAlgorithm
open Finset
namespace SemidegreeExt.ConstructionAlgorithm
open FlowAlgorithm

/-- Source, sink, d left vertices, and n right vertices. The unused right
vertex 0 may be removed; keeping it simplifies zero-based indexing. -/
abbrev Vertex (n d : ℕ) := Fin 2 ⊕ (Fin d ⊕ Fin n)

def source (n d : ℕ) : Vertex n d := .inl 0
def sink (n d : ℕ) : Vertex n d := .inl 1
def left {n d : ℕ} (i : Fin d) : Vertex n d := .inr (.inl i)
def right {n d : ℕ} (j : Fin n) : Vertex n d := .inr (.inr j)

/-- Capacities of the paper's three-layer integral network. -/
def capacity (n d c : ℕ) : Vertex n d → Vertex n d → ℕ
  | .inl a, .inr (.inl i) => if a=0 then d-i.val else 0
  | .inr (.inl i), .inr (.inr j) => if i.val<j.val then 1 else 0
  | .inr (.inr _), .inl b => if b=1 then c else 0
  | _, _ => 0

def demandTotal (d : ℕ) : ℕ := ∑ i : Fin d, (d - i.val)

lemma demandTotal_doubled (d : ℕ) : demandTotal d * 2 = d*(d+1) := by
  unfold demandTotal
  rw [Fin.sum_univ_eq_sum_range]
  exact sum_range_sub_self d

lemma demandTotal_eq (d : ℕ) : demandTotal d = d*(d+1)/2 := by
  have := demandTotal_doubled d
  omega

lemma vertex_count (n d : ℕ) : Fintype.card (Vertex n d) = d+n+2 := by
  simp [Vertex, Fintype.card_sum]
  omega

/-- Direct executable integer-flow construction, independent of the existence
proof: exactly demandTotal(d) computed residual searches starting from zero. -/
def computedFlow (n d c : ℕ) : Matrix (Vertex n d) :=
  run (capacity n d c) (source n d) (sink n d) (demandTotal d)

/-- A forward arc is selected exactly when its unit-capacity edge carries one. -/
def computedForward (n d c : ℕ) : Finset (Fin n × Fin n) :=
  (univ.product univ).filter fun e =>
    if hi : e.1.val < d then
      computedFlow n d c (left ⟨e.1.val,hi⟩) (right e.2) = 1
    else False

/-- Entry of the already proved feasible placement, used only in the correctness
proof. It is never an input or oracle to computedFlow/computedForward. -/
def entry {n d : ℕ} (hd : d ≤ n) (F : Finset (Fin n × Fin n)) (i : Fin d) (j : Fin n) : ℕ :=
  if (Fin.castLE hd i,j) ∈ F then 1 else 0

def row {n d : ℕ} (hd : d ≤ n) (F : Finset (Fin n × Fin n)) (i : Fin d) : ℕ :=
  ∑ j : Fin n, entry hd F i j

def col {n d : ℕ} (hd : d ≤ n) (F : Finset (Fin n × Fin n)) (j : Fin n) : ℕ :=
  ∑ i : Fin d, entry hd F i j

def directedWitness {n d : ℕ} (hd : d ≤ n) (F : Finset (Fin n × Fin n)) : Matrix (Vertex n d)
  | .inl a, .inr (.inl i) => if a=0 then row hd F i else 0
  | .inr (.inl i), .inr (.inr j) => entry hd F i j
  | .inr (.inr j), .inl b => if b=1 then col hd F j else 0
  | _, _ => 0

def witness {n d : ℕ} (hd : d ≤ n) (F : Finset (Fin n × Fin n)) : Matrix (Vertex n d) :=
  fun u v => directedWitness hd F u v - directedWitness hd F v u

lemma witness_skew {n d : ℕ} (hd : d ≤ n) (F : Finset (Fin n × Fin n)) : Skew (witness hd F) := by
  intro u v
  unfold witness
  ring

lemma row_eq {n d : ℕ} (hd : d ≤ n) (F : Finset (Fin n × Fin n)) (i : Fin d) :
    row hd F i = (F.filter fun e => e.1 = Fin.castLE hd i).card := by
  classical
  unfold row entry
  rw [sum_boole]
  apply card_bij (fun j _ => (Fin.castLE hd i,j))
  · intro j hj
    exact mem_filter.mpr ⟨(mem_filter.mp hj).2,rfl⟩
  · intro j _ j' _ h
    exact congrArg Prod.snd h
  · rintro ⟨i',j⟩ he
    have hi : i' = Fin.castLE hd i := (mem_filter.mp he).2
    subst i'
    exact ⟨j,by simpa using (mem_filter.mp he).1,rfl⟩

lemma col_eq {n d : ℕ} (hd : d ≤ n) (F : Finset (Fin n × Fin n))
    (hF : ∀ i j, (i,j) ∈ F → i.val < d) (j : Fin n) :
    col hd F j = (F.filter fun e => e.2 = j).card := by
  classical
  unfold col entry
  rw [sum_boole]
  apply card_bij (fun i _ => (Fin.castLE hd i,j))
  · intro i hi
    exact mem_filter.mpr ⟨(mem_filter.mp hi).2,rfl⟩
  · intro i _ i' _ h
    exact Fin.ext (congrArg (fun e : Fin n × Fin n => e.1.val) h)
  · rintro ⟨i,j'⟩ he
    have hj : j'=j := (mem_filter.mp he).2
    subst j'
    have hi := hF i j (mem_filter.mp he).1
    refine ⟨⟨i.val,hi⟩,?_,?_⟩
    · simpa [Fin.castLE] using (mem_filter.mp he).1
    · ext <;> rfl

lemma witness_conserve {n d : ℕ} (hd : d ≤ n) (F : Finset (Fin n × Fin n))
    (v : Vertex n d) (hvs : v ≠ source n d) (hvt : v ≠ sink n d) :
    divergence (witness hd F) v = 0 := by
  cases v with
  | inl a => fin_cases a <;> simp_all [source,sink]
  | inr v =>
    cases v with
    | inl i => simp [divergence, witness, directedWitness, Vertex, Fintype.sum_sum_type, Fin.sum_univ_two, row]
    | inr j => simp [divergence, witness, directedWitness, Vertex, Fintype.sum_sum_type, Fin.sum_univ_two, col]

lemma witness_source_value {n d : ℕ} (hd : d ≤ n) (F : Finset (Fin n × Fin n))
    (hout : ∀ i, i.val < d → (F.filter fun e => e.1 = i).card = d-i.val) :
    divergence (witness hd F) (source n d) = demandTotal d := by
  have hr (i : Fin d) : row hd F i = d-i.val := (row_eq hd F i).trans (hout _ i.isLt)
  simp [divergence, witness, directedWitness, source, Vertex, Fintype.sum_sum_type, hr, demandTotal]

lemma witness_bounded {n d c : ℕ} (hd : d ≤ n) (F : Finset (Fin n × Fin n))
    (hF : ∀ i j, (i,j) ∈ F → i.val < d ∧ i.val < j.val)
    (hout : ∀ i, i.val < d → (F.filter fun e => e.1 = i).card = d-i.val)
    (hin : ∀ j, (F.filter fun e => e.2 = j).card ≤ c) :
    Bounded (capacity n d c) (witness hd F) := by
  have hr (i : Fin d) : row hd F i = d-i.val := (row_eq hd F i).trans (hout _ i.isLt)
  have hc (j : Fin n) : col hd F j ≤ c := by rw [col_eq hd F (fun i j h => (hF i j h).1)]; exact hin j
  have he (i : Fin d) (j : Fin n) : entry hd F i j ≤ if i.val<j.val then 1 else 0 := by
    unfold entry
    split_ifs with hijF hij hij
    · omega
    · have hh := (hF _ _ hijF).2
      change i.val < j.val at hh
      exact (hij hh).elim
    · omega
    · omega
  intro u v
  cases u with
  | inl a =>
    cases v with
    | inl b => simp [witness,directedWitness,capacity]
    | inr v =>
      cases v with
      | inl i => simp [witness,directedWitness,capacity,hr]
      | inr j => simp [witness,directedWitness,capacity]; split_ifs <;> positivity
  | inr u =>
    cases u with
    | inl i =>
      cases v with
      | inl a => simp [witness,directedWitness,capacity]; split_ifs <;> positivity
      | inr v =>
        cases v with
        | inl i' => simp [witness,directedWitness,capacity]
        | inr j => simpa [witness,directedWitness,capacity] using (show (entry hd F i j : ℤ) ≤ (if i.val<j.val then 1 else 0 : ℕ) by exact_mod_cast he i j)
    | inr j =>
      cases v with
      | inl a =>
        by_cases ha : a=1
        · simpa [witness,directedWitness,capacity,ha] using (show (col hd F j : ℤ) ≤ c by exact_mod_cast hc j)
        · simp [witness,directedWitness,capacity,ha]
      | inr v =>
        cases v with
        | inl i => simp [witness,directedWitness,capacity]
        | inr j' => simp [witness,directedWitness,capacity]

/-- Genuine correctness of the executable zero-flow algorithm on the paper's
network. The Hall theorem is used solely to prove a feasible comparison flow. -/
theorem computedFlow_correct (n d c : ℕ) (hd : d < n)
    (hc : d*(d+1)+c*(c+1) ≤ 2*c*n) :
    Valid (capacity n d c) (source n d) (sink n d) (computedFlow n d c) ∧
    divergence (computedFlow n d c) (source n d) = demandTotal d := by
  obtain ⟨F,hF,hout,hin⟩ := nested_placement n d c hd hc
  have hvalid : Valid (capacity n d c) (source n d) (sink n d) (witness hd.le F) :=
    ⟨witness_skew hd.le F, witness_bounded hd.le F hF hout hin, witness_conserve hd.le F⟩
  exact run_correct (by simp [source,sink]) hvalid (demandTotal d)
    (witness_source_value hd.le F hout) _ (le_refl _)
lemma zero_of_no_cap {n d c : ℕ} {f : Matrix (Vertex n d)}
    (hf : Valid (capacity n d c) (source n d) (sink n d) f)
    (u v : Vertex n d) (huv : capacity n d c u v = 0) (hvu : capacity n d c v u = 0) :
    f u v = 0 := by
  have ha := hf.2.1 u v
  have hb := hf.2.1 v u
  rw [huv] at ha
  rw [hvu] at hb
  have hs := hf.1 u v
  simp only [Nat.cast_zero] at ha hb
  omega

lemma terminal_zero {n d c : ℕ} {f : Matrix (Vertex n d)}
    (hf : Valid (capacity n d c) (source n d) (sink n d) f) (a b : Fin 2) :
    f (.inl a) (.inl b) = 0 := zero_of_no_cap hf _ _ rfl rfl

lemma left_left_zero {n d c : ℕ} {f : Matrix (Vertex n d)}
    (hf : Valid (capacity n d c) (source n d) (sink n d) f) (i i' : Fin d) :
    f (left i) (left i') = 0 := zero_of_no_cap hf _ _ rfl rfl

lemma right_right_zero {n d c : ℕ} {f : Matrix (Vertex n d)}
    (hf : Valid (capacity n d c) (source n d) (sink n d) f) (j j' : Fin n) :
    f (right j) (right j') = 0 := zero_of_no_cap hf _ _ rfl rfl

lemma sink_left_zero {n d c : ℕ} {f : Matrix (Vertex n d)}
    (hf : Valid (capacity n d c) (source n d) (sink n d) f) (i : Fin d) :
    f (sink n d) (left i) = 0 := by
  apply zero_of_no_cap hf <;> simp [capacity,sink,left]

lemma source_right_zero {n d c : ℕ} {f : Matrix (Vertex n d)}
    (hf : Valid (capacity n d c) (source n d) (sink n d) f) (j : Fin n) :
    f (source n d) (right j) = 0 := by
  apply zero_of_no_cap hf <;> simp [capacity,source,right]

lemma source_divergence {n d c : ℕ} {f : Matrix (Vertex n d)}
    (hf : Valid (capacity n d c) (source n d) (sink n d) f) :
    divergence f (source n d) = ∑ i : Fin d, f (source n d) (left i) := by
  unfold divergence
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  have ha (a : Fin 2) : f (source n d) (.inl a) = 0 := terminal_zero hf 0 a
  have hb (j : Fin n) : f (source n d) (.inr (.inr j)) = 0 := source_right_zero hf j
  simp only [ha,hb,sum_const_zero,zero_add,add_zero,left]

lemma left_divergence {n d c : ℕ} {f : Matrix (Vertex n d)}
    (hf : Valid (capacity n d c) (source n d) (sink n d) f) (i : Fin d) :
    divergence f (left i) = -f (source n d) (left i) + ∑ j : Fin n, f (left i) (right j) := by
  unfold divergence
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type,Fin.sum_univ_two]
  have hz := sink_left_zero hf i
  have hls := hf.1 (left i) (source n d)
  have hlt := hf.1 (left i) (sink n d)
  have hall (i' : Fin d) : f (left i) (.inr (.inl i')) = 0 := left_left_zero hf i i'
  change f (left i) (source n d) + f (left i) (sink n d) +
    ((∑ i' : Fin d, f (left i) (.inr (.inl i'))) + ∑ j : Fin n, f (left i) (right j)) = _
  rw [hls,hlt,hz]
  simp only [hall,sum_const_zero,neg_zero,add_zero,zero_add]

lemma right_divergence {n d c : ℕ} {f : Matrix (Vertex n d)}
    (hf : Valid (capacity n d c) (source n d) (sink n d) f) (j : Fin n) :
    divergence f (right j) = f (right j) (sink n d) - ∑ i : Fin d, f (left i) (right j) := by
  unfold divergence
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type,Fin.sum_univ_two]
  have hrs := hf.1 (right j) (source n d)
  have hz := source_right_zero hf j
  have hrr (j' : Fin n) : f (right j) (.inr (.inr j')) = 0 := right_right_zero hf j j'
  have hrl (i : Fin d) : f (right j) (.inr (.inl i)) = -f (left i) (right j) := hf.1 _ _
  change f (right j) (source n d) + f (right j) (sink n d) +
    ((∑ i : Fin d, f (right j) (.inr (.inl i))) + ∑ j' : Fin n, f (right j) (.inr (.inr j'))) = _
  rw [hrs,hz]
  simp only [hrr,hrl,sum_const_zero,sum_neg_distrib,neg_zero,zero_add,add_zero]
  ring

lemma saturated_source {n d c : ℕ} {f : Matrix (Vertex n d)}
    (hf : Valid (capacity n d c) (source n d) (sink n d) f)
    (hval : divergence f (source n d) = demandTotal d) (i : Fin d) :
    f (source n d) (left i) = d-i.val := by
  have hsum : (∑ i : Fin d, f (source n d) (left i)) = ∑ i : Fin d, ((d-i.val : ℕ) : ℤ) := by
    rw [← source_divergence hf,hval]
    simp only [demandTotal,Nat.cast_sum]
  have hb (i : Fin d) (_ : i ∈ (univ : Finset (Fin d))) :
      f (source n d) (left i) ≤ ((d-i.val : ℕ) : ℤ) := by
    simpa only [capacity,source,left,if_pos rfl] using hf.2.1 (source n d) (left i)
  have heq := (sum_eq_sum_iff_of_le hb).mp hsum i (mem_univ _)
  rw [Nat.cast_sub (by omega)] at heq
  exact heq

lemma flow_entry_binary {n d c : ℕ} {f : Matrix (Vertex n d)}
    (hf : Valid (capacity n d c) (source n d) (sink n d) f) (i : Fin d) (j : Fin n) :
    0 ≤ f (left i) (right j) ∧ f (left i) (right j) ≤ 1 ∧
    (f (left i) (right j) = 1 → i.val < j.val) := by
  have hpos : f (right j) (left i) ≤ 0 := by
    simpa only [capacity,right,left,Nat.cast_zero] using hf.2.1 (right j) (left i)
  have hup : f (left i) (right j) ≤ ((if i.val<j.val then 1 else 0 : ℕ) : ℤ) :=
    hf.2.1 (left i) (right j)
  have hsk := hf.1 (left i) (right j)
  by_cases hij : i.val < j.val <;> simp only [hij,if_true,if_false,Nat.cast_one,Nat.cast_zero] at hup <;> omega

/-- The arc set computed by integer augmentation meets every row demand and
column capacity, and contains only the allowed forward unit-capacity pairs. -/
theorem computedForward_correct (n d c : ℕ) (hd : d < n)
    (hc : d*(d+1)+c*(c+1) ≤ 2*c*n) :
    (∀ i j, (i,j) ∈ computedForward n d c → i.val < d ∧ i.val < j.val) ∧
    (∀ i, i.val < d → ((computedForward n d c).filter fun e => e.1=i).card = d-i.val) ∧
    (∀ j, ((computedForward n d c).filter fun e => e.2=j).card ≤ c) := by
  classical
  obtain ⟨hf,hval⟩ := computedFlow_correct n d c hd hc
  let f := computedFlow n d c
  change Valid (capacity n d c) (source n d) (sink n d) f at hf
  change divergence f (source n d) = demandTotal d at hval
  have hmem (i j : Fin n) : (i,j) ∈ computedForward n d c ↔
      ∃ hi : i.val < d, f (left ⟨i.val,hi⟩) (right j) = 1 := by
    simp only [computedForward,mem_filter,mem_product,mem_univ,true_and]
    split_ifs with hi
    · simp [hi,f]
    · simp [hi]
  have hrow (i : Fin d) : (∑ j : Fin n, f (left i) (right j)) = ((d-i.val : ℕ) : ℤ) := by
    have hcons := hf.2.2 (left i) (by simp [left,source]) (by simp [left,sink])
    rw [left_divergence hf,saturated_source hf hval] at hcons
    have hcast : ((d-i.val : ℕ) : ℤ) = (d : ℤ)-i.val := by rw [Nat.cast_sub (by omega)]
    rw [hcast]
    omega
  have hcol (j : Fin n) : (∑ i : Fin d, f (left i) (right j)) ≤ c := by
    have hcons := hf.2.2 (right j) (by simp [right,source]) (by simp [right,sink])
    rw [right_divergence hf] at hcons
    have hb : f (right j) (sink n d) ≤ (c : ℤ) := by
      simpa [capacity,right,sink] using hf.2.1 (right j) (sink n d)
    omega
  have hbool (i : Fin d) (j : Fin n) :
      f (left i) (right j) = if f (left i) (right j) = 1 then 1 else 0 := by
    have h := flow_entry_binary hf i j
    split_ifs <;> omega
  refine ⟨?_,?_,?_⟩
  · intro i j hij
    obtain ⟨hi,hij'⟩ := (hmem i j).mp hij
    exact ⟨hi,(flow_entry_binary hf ⟨i.val,hi⟩ j).2.2 hij'⟩
  · intro i hi
    have hcard : ((computedForward n d c).filter fun e => e.1=i).card =
        (univ.filter fun j : Fin n => f (left ⟨i.val,hi⟩) (right j)=1).card := by
      symm
      apply card_bij (fun j _ => (i,j))
      · intro j hj
        exact mem_filter.mpr ⟨(hmem i j).mpr ⟨hi,(mem_filter.mp hj).2⟩,rfl⟩
      · intro j _ j' _ he
        exact congrArg Prod.snd he
      · rintro ⟨i',j⟩ he
        have hi' : i'=i := (mem_filter.mp he).2
        subst i'
        obtain ⟨_,hh⟩ := (hmem i j).mp (mem_filter.mp he).1
        exact ⟨j,mem_filter.mpr ⟨mem_univ _,hh⟩,rfl⟩
    rw [hcard]
    have heq : (∑ j : Fin n, if f (left ⟨i.val,hi⟩) (right j)=1 then (1 : ℤ) else 0) = ((d-i.val : ℕ) : ℤ) :=
      (sum_congr rfl (fun j _ => hbool ⟨i.val,hi⟩ j)).symm.trans (hrow ⟨i.val,hi⟩)
    rw [sum_boole] at heq
    exact_mod_cast heq
  · intro j
    have hcard : ((computedForward n d c).filter fun e => e.2=j).card =
        (univ.filter fun i : Fin d => f (left i) (right j)=1).card := by
      symm
      apply card_bij (fun i _ => (Fin.castLE hd.le i,j))
      · intro i hi
        apply mem_filter.mpr
        refine ⟨(hmem _ j).mpr ?_,rfl⟩
        exact ⟨i.isLt,(mem_filter.mp hi).2⟩
      · intro i _ i' _ he
        exact Fin.ext (congrArg (fun e : Fin n × Fin n => e.1.val) he)
      · rintro ⟨i,j'⟩ he
        have hj : j'=j := (mem_filter.mp he).2
        subst j'
        obtain ⟨hi,hh⟩ := (hmem i j).mp (mem_filter.mp he).1
        exact ⟨⟨i.val,hi⟩,mem_filter.mpr ⟨mem_univ _,hh⟩,by ext <;> rfl⟩
    rw [hcard]
    have heq : (∑ i : Fin d, if f (left i) (right j)=1 then (1 : ℤ) else 0) ≤ (c : ℤ) :=
      (sum_congr rfl (fun i _ => hbool i j)).symm.le.trans (hcol j)
    rw [sum_boole] at heq
    exact_mod_cast heq
end SemidegreeExt.ConstructionAlgorithm

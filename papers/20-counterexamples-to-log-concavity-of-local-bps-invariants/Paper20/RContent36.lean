import Paper20.FastQ36
import Paper20.HilbertJobsProof
import Paper20.PartitionFinite
import Paper20.PartitionShift

namespace Paper20.RContent36
open Paper20.HilbertJobs
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

abbrev State := List (ℕ × List ℤ)

def addVector (xs ys : List ℤ) : List ℤ :=
  List.ofFn (fun i : Fin 23 => xs.getD i.val 0+ys.getD i.val 0)

theorem addVector_getD (xs ys : List ℤ) (i : ℕ) (hi : i < 23) :
    (addVector xs ys).getD i 0 = xs.getD i 0+ys.getD i 0 := by
  have hlen : (addVector xs ys).length=23 := by rw [addVector,List.length_ofFn]
  rw [List.getD_eq_getElem _ _ (by omega)]
  change (List.ofFn (fun j : Fin 23 => xs.getD j.val 0+ys.getD j.val 0))[i] = _
  rw [List.getElem_ofFn]

def query (c : ℕ) : State → ℕ → ℤ
  | [], _ => 0
  | (k,v)::xs, i => (if k=c then v.getD i 0 else 0)+query c xs i

def update (c : ℕ) (v : List ℤ) : State → State
  | [] => [(c,v)]
  | (k,w)::xs => if k=c then (k,addVector w v)::xs else (k,w)::update c v xs

theorem query_update (xs : State) (c : ℕ) (v : List ℤ) (target i : ℕ) (hi : i < 23) :
    query target (update c v xs) i = query target xs i+
      if c=target then v.getD i 0 else 0 := by
  induction xs with
  | nil => simp [query,update]
  | cons p xs ih =>
    rcases p with ⟨k,w⟩
    by_cases hk : k=c <;> by_cases ht : k=target <;> by_cases hc : c=target <;>
      simp_all only [update,query,hk,ht,hc,↓reduceIte,addVector_getD _ _ i hi,
        add_assoc,add_comm,add_left_comm,zero_add,add_zero,not_true_eq_false,not_false_eq_true] <;> omega

def content (ps : List ℕ) : ℕ := (contentOf ps).natAbs

def weightedValues (ps : List ℕ) : List ℤ :=
  (FastR36.values (hooksOf ps) (partsEvenHooks ps) 22).map
    (fun z => (((dimOf 36 ps)^2:ℕ):ℤ)*z)

theorem weightedValues_getD (ps : List ℕ) (i : ℕ) :
    (weightedValues ps).getD i 0 =
      (((dimOf 36 ps)^2:ℕ):ℤ)*(FastR36.values (hooksOf ps) (partsEvenHooks ps) 22).getD i 0 := by
  unfold weightedValues
  simp only [List.getD_eq_getD_getElem?,List.getElem?_map]
  cases he : (FastR36.values (hooksOf ps) (partsEvenHooks ps) 22)[i]? <;> simp

def addPart (xs : State) (ps : List ℕ) : State := update (content ps) (weightedValues ps) xs
def aggregate (pss : List (List ℕ)) : State := pss.foldl addPart []

theorem fold_query (pss : List (List ℕ)) (xs : State) (c i : ℕ) (hi : i < 23) :
    query c (pss.foldl addPart xs) i = query c xs i+
      (pss.map (fun ps => if content ps=c then (weightedValues ps).getD i 0 else 0)).sum := by
  induction pss generalizing xs with
  | nil => simp
  | cons ps pss ih =>
    rw [List.foldl_cons,ih,addPart,query_update _ _ _ _ _ hi]
    simp only [List.map_cons,List.sum_cons]
    omega

theorem aggregate_query (pss : List (List ℕ)) (c i : ℕ) (hi : i < 23) :
    query c (aggregate pss) i =
      (pss.map (fun ps => if content ps=c then (weightedValues ps).getD i 0 else 0)).sum := by
  simpa only [aggregate,query,zero_add] using fold_query pss [] c i hi

def merge (xs ys : State) : State := xs.foldl (fun acc p => update p.1 p.2 acc) ys

theorem query_merge (xs ys : State) (c i : ℕ) (hi : i < 23) :
    query c (merge xs ys) i = query c xs i+query c ys i := by
  induction xs generalizing ys with
  | nil => simp [merge,query]
  | cons p xs ih =>
    rcases p with ⟨k,v⟩
    change query c (merge xs (update k v ys)) i = _
    rw [ih,query_update _ _ _ _ _ hi]
    simp only [query]
    omega

def combine (xs : List State) : State := xs.foldr merge []

theorem query_combine (xs : List State) (c i : ℕ) (hi : i < 23) :
    query c (combine xs) i = (xs.map (fun s => query c s i)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change query c (merge x (combine xs)) i = _
    rw [query_merge _ _ _ _ hi,ih]
    rfl

/-- A certificate states every content-specific scaled coefficient of the
complete actual subtree, with no selected-partition or coefficient premise. -/
def Correct (j : Job) (s : State) : Prop :=
  ∀ c i, i < 23 → query c s i =
    ((parts j).map (fun ps => if content ps=c then (weightedValues ps).getD i 0 else 0)).sum

theorem correct_aggregate (j : Job) : Correct j (aggregate (parts j)) := by
  intro c i hi
  exact aggregate_query _ c i hi

theorem correct_leaf (j : Job) (s : State) (h : aggregate (parts j)=s) : Correct j s := by
  rw [← h]
  exact correct_aggregate j

theorem correct_children (j : Job) (hf : 0 < j.fuel) (hn : j.rem ≠ 0)
    (vs : List State) (hv : List.Forall₂ Correct (children j) vs) : Correct j (combine vs) := by
  intro c i hi
  rw [query_combine _ _ _ hi]
  have hsum : ∀ (js : List Job) (ss : List State), List.Forall₂ Correct js ss →
      (ss.map (fun s => query c s i)).sum =
        (js.map (fun k => ((parts k).map (fun ps =>
          if content ps=c then (weightedValues ps).getD i 0 else 0)).sum)).sum := by
    intro js ss h
    induction h with
    | nil => rfl
    | cons hhead htail ih =>
      simp only [List.map_cons,List.sum_cons,hhead c i hi,ih]
  rw [hsum _ _ hv,← parts_children j hf hn,List.map_flatMap,Paper20.sum_flatMap_int]

def root : Job := ⟨[],36,36,37⟩

theorem parts_root : parts root = partitionsOf 36 := by
  change (partitionsCappedAux 37 36 36).map (fun ps => ([]:List ℕ)++ps) = partitionsOf 36
  rw [show (fun ps : List ℕ => ([]:List ℕ)++ps)=id from rfl,List.map_id]
  rfl

theorem content_bound {ps : List ℕ} (hp : ps ∈ partitionsOf 36) : content ps ≤ 630 := by
  let p := Part.ofMem ps hp
  have h1 := p.nuOf_le
  have h2 := p.transpose.nuOf_le
  have hc := p.contentOf_eq_nu_difference
  have hb : ((contentOf p.parts).natAbs:ℤ) ≤ (Nat.choose 36 2:ℕ) := by
    rw [← Int.abs_eq_natAbs]
    apply abs_le.mpr
    constructor <;> omega
  change (contentOf ps).natAbs ≤ 630
  have : (contentOf ps).natAbs ≤ Nat.choose 36 2 := by exact_mod_cast hb
  exact this

end
end Paper20.RContent36

import Paper20.FastHilbert

/-! Exact subtrees of the original partition recursion. A job carries only
input parameters. It carries no asserted result or mathematical assumption. -/
namespace Paper20.HilbertJobs

structure Job where
  pre : List ℕ
  cap : ℕ
  rem : ℕ
  fuel : ℕ
  deriving DecidableEq, BEq, Repr

def parts (j : Job) : List (List ℕ) :=
  (partitionsCappedAux j.fuel j.cap j.rem).map (fun tail => j.pre++tail)

def value (j : Job) : List ℕ :=
  (parts j).foldl (FastHilbert.addPart 43 1 903) (List.replicate 904 0)

def children (j : Job) : List Job :=
  match j.fuel with
  | 0 => []
  | fuel+1 => if j.rem = 0 then [] else
      (List.range' 1 (min j.rem j.cap)).reverse.map (fun a =>
        ⟨j.pre++[a], a, j.rem-a, fuel⟩)

def combine (vs : List (List ℕ)) : List ℕ :=
  vs.foldl (List.zipWith Nat.add) (List.replicate 904 0)

def root : Job := ⟨[],43,43,44⟩

end Paper20.HilbertJobs

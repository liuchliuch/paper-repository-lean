import Paper20.PartitionTranspose

namespace Paper20.Part
noncomputable section
set_option maxHeartbeats 1000000

def ofMem {n : ℕ} (ps : List ℕ) (hp : ps ∈ partitionsOf n) : Part n where
  parts := ps
  sorted := ((Paper20.mem_partitionsOf n ps).mp hp).2.1
  pos := fun a ha => (((Paper20.mem_partitionsOf n ps).mp hp).2.2 a ha).1
  sum_eq := ((Paper20.mem_partitionsOf n ps).mp hp).1

/-- The abstract mathematical partition type is exactly the complete
executable enumeration, not a separately selected list of shapes. -/
def enumerationEquiv (n : ℕ) : Part n ≃ {ps : List ℕ // ps ∈ partitionsOf n} where
  toFun p := ⟨p.parts,p.mem_partitionsOf⟩
  invFun p := ofMem p.val p.property
  left_inv p := ext_parts rfl
  right_inv p := Subtype.ext rfl

instance fintype (n : ℕ) : Fintype (Part n) :=
  Fintype.ofEquiv {ps : List ℕ // ps ∈ partitionsOf n} (enumerationEquiv n).symm

theorem sum_over_partitions {M : Type*} [AddCommMonoid M] (n : ℕ) (f : List ℕ → M) :
    ∑ p : Part n, f p.parts = ((partitionsOf n).map f).sum := by
  classical
  have he := Fintype.sum_equiv (enumerationEquiv n) (fun p => f p.parts)
    (fun p => f p.val) (by intro p; rfl)
  rw [he]
  have hd := nodup_partitionsOf n
  rw [← List.sum_toFinset f hd]
  apply Finset.sum_bij (fun p _ => p.val)
  · intro p hp; simpa using p.property
  · intro p hp q hq he; exact Subtype.ext he
  · intro ps hps
    exact ⟨⟨ps,by simpa using hps⟩,Finset.mem_univ _,rfl⟩
  · intro p hp; rfl

end
end Paper20.Part

import Paper29.BlockDesign
import Paper29.HardTranscript

noncomputable section
open scoped BigOperators Classical
namespace Paper29

/-- Updating one embedded response changes exactly its corresponding pool row. -/
theorem extend_update {I J R : Type} [DecidableEq I] [DecidableEq J]
    (f : I → J) (hf : Function.Injective f) (y : I → R) (pad : J → R) (a : I) (v : R) :
    Function.extend f (Function.update y a v) pad =
      Function.update (Function.extend f y pad) (f a) v := by
  funext j
  by_cases hj : ∃ b,f b=j
  · obtain ⟨b,rfl⟩ := hj
    simp only [hf.extend_apply]
    by_cases hb : b=a
    · subst b; simp
    · have hfb : f b≠f a := fun h => hb (hf h)
      simp [Function.update_of_ne hb,Function.update_of_ne hfb,hf.extend_apply]
  · have hja : j≠f a := fun h => hj ⟨a,h.symm⟩
    rw [Function.extend_apply' _ _ _ hj,Function.update_of_ne hja,
      Function.extend_apply' _ _ _ hj]

namespace HardDistribution

def poolBits {n r N : ℕ} (hblocks : r*N ≤ n) (y : Bits r N) : Fin n → Bool :=
  Function.extend (blockRow hblocks) y (fun _ => false)

theorem poolBits_blockRow {n r N : ℕ} (hN : 0 < N) (hblocks : r*N ≤ n)
    (y : Bits r N) (a : Fin r × Fin N) : poolBits hblocks y (blockRow hblocks a)=y a :=
  (blockRow_injective hN hblocks).extend_apply _ _ _

theorem poolBits_update {n r N : ℕ} (hN : 0 < N) (hblocks : r*N ≤ n)
    (y : Bits r N) (a : Fin r × Fin N) (v : Bool) :
    poolBits hblocks (Function.update y a v)=Function.update (poolBits hblocks y) (blockRow hblocks a) v :=
  extend_update _ (blockRow_injective hN hblocks) y _ a v

theorem poolBits_padded {n r N : ℕ} (hblocks : r*N ≤ n) (y : Bits r N) (i : Fin n)
    (hi : ¬∃ a,blockRow hblocks a=i) : poolBits hblocks y i=false :=
  Function.extend_apply' _ _ _ hi

/-- The finite pool alphabet represents the exact original real hard response,
including every padded zero row. -/
theorem longResponse_poolBits {n r N : ℕ} (hN : 0 < N) (hblocks : r*N ≤ n) (y : Bits r N) :
    longResponse (n:=n) y = fun i => 4*bit (poolBits hblocks y i) := by
  funext i
  by_cases hi : i.val<r*N
  · obtain ⟨a,_,ha⟩ := Finset.mem_image.mp ((mem_blockRow_image hN hblocks i).2 hi)
    subst i
    rw [poolBits_blockRow hN]
    simp only [longResponse,dif_pos hi,dif_pos hN,blockRow_div hN,blockRow_mod]
  · have hn : ¬∃ a,blockRow hblocks a=i := by
      rintro ⟨a,ha⟩
      exact hi ((mem_blockRow_image hN hblocks i).1 (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,ha⟩))
    rw [poolBits_padded hblocks y i hn]
    simp [longResponse,hi,bit]

end HardDistribution
namespace Transcript.Law

variable {Ω A B C E : Type} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C] [Fintype E]

theorem Independent.map_left (P : Law Ω) (X : Ω → A) (Y : Ω → E) (f : A → B)
    (h : P.Independent X Y) : P.Independent (fun ω => f (X ω)) Y := by
  intro b e
  have hj := P.sum_mass_mul (fun ω => (X ω,Y ω))
    (fun z : A × E => if (f z.1,z.2)=(b,e) then (1:ℝ) else 0)
  have hm := P.sum_mass_mul X (fun a => if f a=b then (1:ℝ) else 0)
  unfold Independent at *
  simp only [mass,Prod.mk.injEq] at ⊢
  simp only [mul_ite,mul_one,mul_zero,Fintype.sum_prod_type,Prod.mk.injEq] at hj hm
  rw [← hj]
  simp only [ite_and]
  simp_rw [h]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [← hm,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp [mass]

theorem information_const (P : Law Ω) (X : Ω → A) (b : B) :
    P.information X (fun _ => b)=0 := by
  apply P.information_zero_of_independent
  intro a c
  by_cases hc : b=c
  · subst c
    simp only [mass,Prod.mk.injEq,and_true,if_true,P.total,mul_one]
  · simp [mass,hc]

end Transcript.Law
end Paper29

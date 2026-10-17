import UniformBorderRank.FdRank

/-! Elementary CP/border rank operations used in Sections 2--4. -/
noncomputable section
namespace UniformBorderRank
open Finset

lemma cpRankLe_zero {N : ℕ} {d : Fin N → ℕ} : cpRankLe (0 : Coeffs d) 0 := by
  refine ⟨Fin.elim0, (fun j => j.elim0), ?_⟩
  intro u
  simp

lemma borderRankLe_zero {N : ℕ} {d : Fin N → ℕ} : borderRankLe (0 : Coeffs d) 0 :=
  borderRankLe_of_cpRankLe cpRankLe_zero

lemma isProduct_smul {N : ℕ} {d : Fin N → ℕ} (hN : 0 < N)
    {T : Coeffs d} (c : ℂ) (hT : isProduct T) : isProduct (c • T) := by
  classical
  obtain ⟨v, hv⟩ := hT
  refine ⟨fun i a => if i = (⟨0, hN⟩ : Fin N) then c * v i a else v i a, ?_⟩
  intro u
  change c * T u = _
  rw [hv]
  exact prod_scalar_absorb ⟨0, hN⟩ (fun i => v i (u i)) c

lemma isProduct_zero {N : ℕ} {d : Fin N → ℕ} (hN : 0 < N) :
    isProduct (0 : Coeffs d) := by
  have h : isProduct (fun _ : (∀ i, Fin (d i)) => (1 : ℂ)) :=
    ⟨fun _ _ => 1, by simp⟩
  simpa using isProduct_smul hN 0 h

lemma cpRankLe_add {N : ℕ} {d : Fin N → ℕ} {T U : Coeffs d} {a b : ℕ}
    (hT : cpRankLe T a) (hU : cpRankLe U b) : cpRankLe (T + U) (a + b) := by
  obtain ⟨t, ht, hts⟩ := hT
  obtain ⟨u, hu, hus⟩ := hU
  refine ⟨Fin.addCases t u, ?_, ?_⟩
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro j; simpa using ht j
    · intro j; simpa using hu j
  · intro idx
    rw [Fin.sum_univ_add]
    simp [hts idx, hus idx]

lemma borderRankLe_add {N : ℕ} {d : Fin N → ℕ} {T U : Coeffs d} {a b : ℕ}
    (hT : borderRankLe T a) (hU : borderRankLe U b) : borderRankLe (T + U) (a + b) := by
  obtain ⟨t, ht, htl⟩ := hT
  obtain ⟨u, hu, hul⟩ := hU
  exact ⟨fun n => t n + u n, fun n => cpRankLe_add (ht n) (hu n),
    fun idx => (htl idx).add (hul idx)⟩

lemma cpRankLe_smul {N : ℕ} {d : Fin N → ℕ} (hN : 0 < N)
    {T : Coeffs d} {a : ℕ} (c : ℂ) (hT : cpRankLe T a) : cpRankLe (c • T) a := by
  obtain ⟨t, ht, hts⟩ := hT
  refine ⟨fun j => c • t j, fun j => isProduct_smul hN c (ht j), ?_⟩
  intro idx
  simpa only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum] using congrArg (c * ·) (hts idx)

lemma borderRankLe_smul {N : ℕ} {d : Fin N → ℕ} (hN : 0 < N)
    {T : Coeffs d} {a : ℕ} (c : ℂ) (hT : borderRankLe T a) : borderRankLe (c • T) a := by
  obtain ⟨t, ht, htl⟩ := hT
  exact ⟨fun n => c • t n, fun n => cpRankLe_smul hN c (ht n),
    fun idx => (htl idx).const_mul c⟩

lemma cpRankLe_mono {N : ℕ} {d : Fin N → ℕ} (hN : 0 < N)
    {T : Coeffs d} {a b : ℕ} (hab : a ≤ b) (hT : cpRankLe T a) : cpRankLe T b := by
  have hz : cpRankLe (0 : Coeffs d) (b - a) :=
    ⟨fun _ => 0, fun _ => isProduct_zero hN, by simp⟩
  have h := cpRankLe_add hT hz
  simpa only [add_zero, Nat.add_sub_of_le hab] using h

lemma borderRankLe_mono {N : ℕ} {d : Fin N → ℕ} (hN : 0 < N)
    {T : Coeffs d} {a b : ℕ} (hab : a ≤ b) (hT : borderRankLe T a) : borderRankLe T b := by
  obtain ⟨t, ht, htl⟩ := hT
  exact ⟨t, fun n => cpRankLe_mono hN hab (ht n), htl⟩

lemma borderRankLe_finset_sum {N : ℕ} {d : Fin N → ℕ} {ι : Type*}
    (S : Finset ι) (T : ι → Coeffs d) (b : ι → ℕ)
    (h : ∀ i ∈ S, borderRankLe (T i) (b i)) :
    borderRankLe (∑ i ∈ S, T i) (∑ i ∈ S, b i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using borderRankLe_zero (d := d)
  | @insert i S hi ih =>
    simpa only [sum_insert hi] using borderRankLe_add (h i (mem_insert_self _ _))
      (ih (fun j hj => h j (mem_insert_of_mem hj)))

end UniformBorderRank

import Paper14.ReturnGeometry
import Paper14.RectangleCount
import Paper14.ReturnCombinatorics

open Set Function
namespace Paper14
noncomputable section

lemma hMap_smul (t c : ℝ) (v : ℝ × ℝ) : hMap t (c • v) = c • hMap t v := by
  ext <;> simp [hMap] <;> ring

/-- The horocycle basis change preserves actual lattice primitivity. -/
lemma hMap_primitive {x : ℝ × ℝ} (hx : x ∈ Omega) (n : ℕ) {v : ℝ × ℝ}
    (hv : IsPrimitiveVec x v) : IsPrimitiveVec (B^[n] x) (hMap (H n x) v) := by
  refine ⟨?_,?_,?_⟩
  · rw [← hMap_H_lattice hx n]
    exact ⟨v,hv.1,rfl⟩
  · intro hz
    apply hv.2.1
    apply hMap_injective (H n x)
    simpa [hMap] using hz
  · intro k w hw heq
    rw [← hMap_H_lattice hx n] at hw
    obtain ⟨z,hz,rfl⟩ := hw
    have hvz : v = (k : ℝ) • z := by
      apply hMap_injective (H n x)
      rw [hMap_smul]
      exact heq
    rcases hv.2.2 k z hz hvz with hk | hz0
    · exact Or.inl hk
    · exact Or.inr (by simp [hz0,hMap])

/-- The unique primitive positive horizontal vector in a section lattice. -/
lemma primitive_horizontal {x : ℝ × ℝ} (hx : x ∈ Omega) {u : ℝ}
    (hu : 0 < u) (hv : IsPrimitiveVec x (u,0)) : u = x.1 := by
  obtain ⟨p,q,hp,hq⟩ := mem_Lambda.mp hv.1
  have hq0 : q = 0 := by
    have h : (q : ℝ) = 0 := (div_eq_zero_iff.mp hq.symm).resolve_right hx.1.ne'
    exact_mod_cast h
  simp only [hq0,Int.cast_zero,zero_mul,add_zero] at hp
  have hw : (x.1,0) ∈ Lambda x := ⟨1,0,by ext <;> simp⟩
  have heq : (u,0) = (p : ℝ) • (x.1,(0 : ℝ)) := by ext <;> simp [hp]
  have hw0 : (x.1,0) ≠ (0 : ℝ × ℝ) := by
    intro hz
    exact hx.1.ne' (congrArg Prod.fst hz)
  have hk : |p| = 1 := (hv.2.2 p (x.1,0) hw heq).resolve_right hw0
  have hp0 : (0 : ℝ) < p := by nlinarith [hx.1]
  have hpn : (0 : ℤ) ≤ p := by exact_mod_cast hp0.le
  rw [abs_of_nonneg hpn] at hk
  simpa [hk] using hp

lemma H_strictMono {x : ℝ × ℝ} (hx : x ∈ Omega) : StrictMono (fun n => H n x) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [H_succ]
  exact lt_add_of_pos_right _ (tau_pos (B_iterate_mem hx n))

/-- Every primitive point in the positive unit strip appears as the
horizontal primitive vector at an ordinary BCZ return. -/
theorem primitive_vector_return {x : ℝ × ℝ} (hx : x ∈ Omega) {u v : ℝ}
    (hv : IsPrimitiveVec x (u,v)) (hu : 0 < u) (hu1 : u ≤ 1) (hvp : 0 < v) :
    ∃ N : ℕ, 0 < N ∧ H N x = v / u ∧ (B^[N] x).1 = u := by
  let t := v / u
  have ht : 0 < t := div_pos hvp hu
  have hex : ∃ N : ℕ, t ≤ H N x := by
    obtain ⟨N,hN⟩ := exists_nat_gt t
    exact ⟨N,hN.le.trans (H_ge_nat hx N)⟩
  letI : DecidablePred (fun N : ℕ => t ≤ H N x) := Classical.decPred _
  let N := Nat.find hex
  have hN : t ≤ H N x := Nat.find_spec hex
  have hpre : ∀ k < N, H k x < t := by
    intro k hk
    exact lt_of_not_ge (Nat.find_min hex hk)
  have hN0 : 0 < N := by
    by_contra h
    have hz : N = 0 := by omega
    simp only [hz,H,Finset.range_zero,Finset.sum_empty] at hN
    exact not_le_of_gt ht hN
  have hvt : v = t * u := by dsimp [t]; field_simp
  have heqTime : H N x = t := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hN0.ne'
    have hprev := hpre k (by omega)
    have hvec : hMap (H k x) (u,v) ∈ Lambda (B^[k] x) := by
      rw [← hMap_H_lattice hx k]
      exact ⟨(u,v),hv.1,rfl⟩
    have hvheight : 0 < (hMap (H k x) (u,v)).2 := by
      change 0 < v - H k x * u
      rw [hvt]
      nlinarith
    have hmin := lattice_minimum_slope (B_iterate_mem hx k) hvec hu hu1 hvheight
    change tau (B^[k] x) * u ≤ v - H k x * u at hmin
    rw [hvt] at hmin
    have hroof : tau (B^[k] x) ≤ t - H k x := by nlinarith
    apply le_antisymm ?_ hN
    rw [hk,H_succ]
    linarith
  refine ⟨N,hN0,heqTime,?_⟩
  have hp := hMap_primitive hx N hv
  have hz : hMap (H N x) (u,v) = (u,0) := by
    ext <;> simp [hMap,heqTime,hvt]
  rw [hz] at hp
  exact (primitive_horizontal (B_iterate_mem hx N) hu hp).symm

/-- Zero excess forces every ordinary time up to the return time to lie
in the smaller section, provided all induced returns exist. -/
lemma zero_excess_all_mem {A : Type*} (T : A → A) (Y : Set A) {n : ℕ} {x : A}
    (hx : x ∈ Y)
    (hret : ∀ i, ∃ k, 0 < k ∧ T^[k] ((inducedMap T Y)^[i] x) ∈ Y)
    (hR : Rn T Y n x = n) : ∀ k ≤ n, T^[k] x ∈ Y := by
  have htime : ∀ i < n, firstReturnTime T Y ((inducedMap T Y)^[i] x) = 1 := by
    intro i hi
    have hpos : ∀ j ∈ Finset.range n, 1 ≤ firstReturnTime T Y ((inducedMap T Y)^[j] x) := by
      intro j hj
      exact (firstReturn_spec (hret j)).1
    have hsum : (∑ j ∈ Finset.range n, firstReturnTime T Y ((inducedMap T Y)^[j] x)) =
        ∑ j ∈ Finset.range n, 1 := by simpa [Rn] using hR
    exact ((Finset.sum_eq_sum_iff_of_le hpos).mp hsum.symm i (Finset.mem_range.mpr hi)).symm
  have hsteps : ∀ k ≤ n, T^[k] x = (inducedMap T Y)^[k] x := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [iterate_succ_apply', ih (by omega),iterate_succ_apply',inducedMap,htime k (by omega)]
      rfl
  intro k hk
  rw [hsteps k hk]
  cases k with
  | zero => exact hx
  | succ k => simpa only [iterate_succ_apply' ,inducedMap] using (firstReturn_spec (hret k)).2

/-- Every point of the smaller section has a genuine future return. -/
lemma bcz_Yr_return_exists {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {x : ℝ × ℝ} (hx : x ∈ Yr r) : ∃ k, 0 < k ∧ B^[k] x ∈ Yr r := by
  let z := phiRInv r x
  have hz : z ∈ Omega := phiRInv_mem_Omega hr hr1 hx
  have heq : phiR r z = x := phiR_phiRInv hr hr1 hx
  have ht := (phiR_first_return_point hr hr1 hz).2
  change H (firstReturnTime B (Yr r) (phiR r z)) (phiR r z) = r⁻¹^2 * tau z at ht
  have htpos : 0 < r⁻¹^2 * tau z := mul_pos (sq_pos_of_pos (inv_pos.mpr hr)) (tau_pos hz)
  have hp : 0 < firstReturnTime B (Yr r) (phiR r z) := by
    by_contra h
    have hz0 : firstReturnTime B (Yr r) (phiR r z) = 0 := by omega
    rw [hz0] at ht
    simp only [H,Finset.range_zero,Finset.sum_empty] at ht
    linarith
  have hc := (phiR_first_return_point hr hr1 hz).1
  change inducedMap B (Yr r) (phiR r z) = phiR r (B z) at hc
  refine ⟨firstReturnTime B (Yr r) (phiR r z),hp,?_⟩
  rw [← heq]
  change inducedMap B (Yr r) (phiR r z) ∈ Yr r
  rw [hc]
  exact phiR_mem_Yr hr hr1 (B_mem_Omega hz)

/-- A primitive vector in the strip omitted by `Y_r` rules out zero excess
as soon as its slope is before the accumulated induced roof time. -/
theorem primitive_vector_forces_excess {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {n : ℕ} {x : ℝ × ℝ} (hx : x ∈ Yr r) {u v : ℝ}
    (hv : IsPrimitiveVec x (u,v)) (hru : r < u) (hu1 : u ≤ 1) (hvp : 0 < v)
    (hslope : v / u < Hr r n x) : Rn B (Yr r) n x ≠ n := by
  obtain ⟨N,hN0,hNt,hNu⟩ := primitive_vector_return hx.1 hv (hr.trans hru) hu1 hvp
  have hN : N < Rn B (Yr r) n x := by
    apply (H_strictMono hx.1).lt_iff_lt.mp
    simpa only [hNt,Hr] using hslope
  intro hzero
  have hret : ∀ i, ∃ k, 0 < k ∧ B^[k] ((inducedMap B (Yr r))^[i] x) ∈ Yr r := by
    intro i
    apply bcz_Yr_return_exists hr hr1
    induction i with
    | zero => exact hx
    | succ i ih =>
      simpa only [iterate_succ_apply',inducedMap] using
        (firstReturn_spec (bcz_Yr_return_exists hr hr1 ih)).2
  have hmem := zero_excess_all_mem B (Yr r) hx hret hzero N (by omega)
  exact not_le_of_gt hru (hNu ▸ hmem.2)

/-- The actual event inclusion in paper S4.Ex45. -/
theorem zero_excess_subset_void_or_short_roof {n : ℕ} {α : ℝ}
    (hn : 0 < n) (hαn : α / n < 1)
    (hr : (2 : ℝ) / 3 < 1 - α / n) (hr1 : 1 - α / n < 1) :
    {x ∈ Yr (1 - α / n) | Rn B (Yr (1 - α / n)) n x = n} ⊆
      {x | ZCount n α x = 0} ∪ {x | Hr (1 - α / n) n x ≤ 3 * n} := by
  intro x hx
  by_cases hZ : ZCount n α x = 0
  · exact Or.inl hZ
  by_cases hroof : Hr (1 - α / n) n x ≤ 3 * n
  · exact Or.inr hroof
  exfalso
  have hex := mt (ZCount_eq_zero_iff hx.1.1 hαn).mpr hZ
  push_neg at hex
  obtain ⟨p,q,hu,hu1,hv,hvn,hcop⟩ := hex
  let u := (q : ℝ) * x.2 - (p : ℝ) * x.1
  let v := (q : ℝ) / x.1
  have hprim : IsPrimitiveVec x (u,v) := by
    have h := (primitiveIffCoprime x.1 x.2 hx.1.1 (-p) q).mpr hcop.neg_left
    simpa only [Int.cast_neg,neg_mul,neg_add_eq_sub,add_comm] using h
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hslope : v / u < Hr (1 - α / n) n x := by
    apply lt_trans ((div_lt_iff₀ hu0).mpr (show v < (3 * n) * u by
      dsimp [u,v] at *
      nlinarith))
    exact lt_of_not_ge hroof
  exact primitive_vector_forces_excess (by linarith) hr1 hx.1 hprim hu hu1 hv hslope hx.2

end
end Paper14

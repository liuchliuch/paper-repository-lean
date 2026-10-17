import Paper14.SelfInductionMeasure
import Paper14.MapBCZ
import Paper14.Kac

/-! Lattice return geometry used to prove the remaining part of Lemma 2. -/
open Set Function
namespace Paper14
noncomputable section

lemma hMap_add (u v : ℝ) (x : ℝ × ℝ) :
    hMap (u + v) x = hMap u (hMap v x) := by
  ext <;> simp [hMap] <;> ring

lemma hMap_zero (x : ℝ × ℝ) : hMap 0 x = x := by ext <;> simp [hMap]

lemma hMap_injective (u : ℝ) : Injective (hMap u) := by
  apply LeftInverse.injective (f := hMap u) (g := hMap (-u))
  intro x
  rw [← hMap_add, neg_add_cancel, hMap_zero]

lemma hMap_image_add (u v : ℝ) (S : Set (ℝ × ℝ)) :
    hMap u '' (hMap v '' S) = hMap (u + v) '' S := by
  rw [image_image]
  congr 1
  funext x
  exact (hMap_add u v x).symm

/-- The basis change (7), as equality of the actual lattice sets. -/
lemma hMap_tau_lattice {a b : ℝ} (hx : (a, b) ∈ Omega) :
    hMap (tau (a, b)) '' Lambda (a, b) = Lambda (B (a, b)) := by
  have ha : a ≠ 0 := hx.1.ne'
  have hb : b ≠ 0 := hx.2.2.1.ne'
  let k : ℤ := ⌊(1 + a) / b⌋
  ext v
  constructor
  · rintro ⟨w, ⟨p, q, rfl⟩, rfl⟩
    refine ⟨q + k * p, -p, ?_⟩
    ext <;> simp [hMap, tau, B, k, Int.cast_add, Int.cast_mul, Int.cast_neg]
    · ring
    · field_simp [ha, hb]
      ring
  · rintro ⟨p, q, rfl⟩
    refine ⟨(((-q : ℤ) : ℝ) * a + ((p + k * q : ℤ) : ℝ) * b,
      ((p + k * q : ℤ) : ℝ) / a), ⟨-q, p + k * q, rfl⟩, ?_⟩
    ext <;> simp [hMap, tau, B, k, Int.cast_add, Int.cast_mul, Int.cast_neg]
    · ring
    · field_simp [ha, hb]
      ring

/-- Diagonal scaling and the change of the second basis vector in (2). -/
lemma gMap_lattice {r a b : ℝ} (hr : r ≠ 0) (ha : a ≠ 0) :
    gMap r '' Lambda (a, b) = Lambda (phiR r (a, b)) := by
  let j := phiJ r a b
  ext v
  constructor
  · rintro ⟨w, ⟨p, q, rfl⟩, rfl⟩
    refine ⟨p - q * j, q, ?_⟩
    ext <;> simp [gMap, phiR, j, Int.cast_sub, Int.cast_mul]
    · ring
    · field_simp [hr, ha]
  · rintro ⟨p, q, rfl⟩
    refine ⟨(((p + q * j : ℤ) : ℝ) * a + (q : ℝ) * b, (q : ℝ) / a),
      ⟨p + q * j, q, rfl⟩, ?_⟩
    ext <;> simp [gMap, phiR, j, Int.cast_add, Int.cast_mul]
    · ring
    · field_simp [hr, ha]

/-- Parameters in the Farey triangle are determined by their lattice. -/
lemma Lambda_injective_on : InjOn Lambda Omega := by
  rintro ⟨a,b⟩ hx ⟨s,t⟩ hy heq
  have ha : 0 < a := hx.1
  have hs : 0 < s := hy.1
  have hhorizontal {a b s t : ℝ} (ha : 0 < a) (hs : 0 < s)
      (heq : Lambda (a,b) = Lambda (s,t)) : s ≤ a := by
    have hv : (a, 0) ∈ Lambda (s,t) := by
      rw [← heq]
      exact ⟨1,0,by ext <;> simp⟩
    obtain ⟨p,q,hp,hq⟩ := mem_Lambda.mp hv
    have hq0 : q = 0 := by
      have h : (q : ℝ) = 0 := (div_eq_zero_iff.mp hq.symm).resolve_right hs.ne'
      exact_mod_cast h
    simp only [hq0, Int.cast_zero, zero_mul, add_zero] at hp
    have hp0 : (0 : ℝ) < p := by nlinarith
    have hp1 : (1 : ℤ) ≤ p := by
      have : (0 : ℤ) < p := by exact_mod_cast hp0
      omega
    have hp1r : (1 : ℝ) ≤ p := by exact_mod_cast hp1
    nlinarith
  have has : a = s := le_antisymm (hhorizontal hs ha heq.symm) (hhorizontal ha hs heq)
  subst s
  have hv : (b, 1 / a) ∈ Lambda (a,t) := by
    rw [← heq]
    exact ⟨0,1,by ext <;> simp⟩
  obtain ⟨p,q,hp,hq⟩ := mem_Lambda.mp hv
  have hq1 : q = 1 := by
    have h : (q : ℝ) = 1 := (div_left_inj' ha.ne').mp hq.symm
    exact_mod_cast h
  simp only [hq1, Int.cast_one, one_mul] at hp
  have hb1 := hx.2.2.2.1
  have ht1 := hy.2.2.2.1
  have hab := hx.2.2.2.2
  have hat := hy.2.2.2.2
  have hpgt : (-1 : ℝ) < p := by nlinarith
  have hplt : (p : ℝ) < 1 := by nlinarith
  have hp0 : p = 0 := by
    have hlo : (-1 : ℤ) < p := by exact_mod_cast hpgt
    have hhi : p < (1 : ℤ) := by exact_mod_cast hplt
    omega
  simp only [hp0, Int.cast_zero, zero_mul, zero_add] at hp
  exact Prod.ext rfl hp

/-- Any positive-height vector in the unit horizontal strip has slope at
least the roof time. Primitivity is not needed for this lower bound. -/
lemma lattice_minimum_slope {a b u v : ℝ} (hx : (a,b) ∈ Omega)
    (hv : (u,v) ∈ Lambda (a,b)) (hu : 0 < u) (hu1 : u ≤ 1) (hvp : 0 < v) :
    tau (a,b) * u ≤ v := by
  obtain ⟨p,q,hpu,hqv⟩ := mem_Lambda.mp hv
  have ha : 0 < a := hx.1
  have hb : 0 < b := hx.2.2.1
  have hq0 : (0 : ℝ) < q := by rw [hqv] at hvp; exact (div_pos_iff_of_pos_right ha).mp hvp
  have hq1 : (1 : ℤ) ≤ q := by
    have : (0 : ℤ) < q := by exact_mod_cast hq0
    omega
  have hq1r : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hp0 : p ≤ 0 := by
    by_contra hp
    have hp1 : (1 : ℤ) ≤ p := by omega
    have hp1r : (1 : ℝ) ≤ p := by exact_mod_cast hp1
    have hab := hx.2.2.2.2
    nlinarith
  have hpr : (p : ℝ) ≤ 0 := by exact_mod_cast hp0
  have huq : u ≤ (q : ℝ) * b := by nlinarith
  rw [tau, hqv]
  apply (le_div_iff₀ ha).mpr
  have hcancel : (1 / (a * b) * u) * a = u / b := by field_simp [ha.ne', hb.ne']
  rw [hcancel]
  exact (div_le_iff₀ hb).mpr huq

lemma B_iterate_mem {x : ℝ × ℝ} (hx : x ∈ Omega) (n : ℕ) : B^[n] x ∈ Omega := by
  induction n with
  | zero => exact hx
  | succ n ih => simpa only [iterate_succ_apply'] using B_mem_Omega ih

lemma H_succ (n : ℕ) (x : ℝ × ℝ) : H (n + 1) x = H n x + tau (B^[n] x) := by
  exact Finset.sum_range_succ _ _

lemma H_add (m n : ℕ) (x : ℝ × ℝ) : H (m + n) x = H m x + H n (B^[m] x) := by
  unfold H
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.add_comm m i, iterate_add_apply]

lemma tau_ge_one {x : ℝ × ℝ} (hx : x ∈ Omega) : 1 ≤ tau x := by
  have hp : 0 < x.1 * x.2 := mul_pos hx.1 hx.2.2.1
  have hm : x.1 * x.2 ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hx.2.1 hx.2.2.2.1 hx.2.2.1.le (by norm_num : (0 : ℝ) ≤ 1)
  exact (one_le_div hp).mpr hm

lemma H_ge_nat {x : ℝ × ℝ} (hx : x ∈ Omega) (n : ℕ) : (n : ℝ) ≤ H n x := by
  induction n with
  | zero => simp [H]
  | succ n ih =>
    rw [H_succ, Nat.cast_add, Nat.cast_one]
    exact add_le_add ih (tau_ge_one (B_iterate_mem hx n))

lemma hMap_H_lattice {x : ℝ × ℝ} (hx : x ∈ Omega) (n : ℕ) :
    hMap (H n x) '' Lambda x = Lambda (B^[n] x) := by
  induction n with
  | zero => simpa only [H, Finset.range_zero, Finset.sum_empty, iterate_zero, id_eq] using
      (show hMap 0 '' Lambda x = Lambda x by simpa only [hMap_zero] using (Set.image_id (Lambda x)))
  | succ n ih =>
    rw [H_succ, add_comm, ← hMap_image_add, ih]
    simpa only [iterate_succ_apply'] using hMap_tau_lattice (B_iterate_mem hx n)

lemma hMap_scaled_lattice {r a b : ℝ} (hr : r ≠ 0) (ha : a ≠ 0) (u : ℝ) :
    hMap u '' Lambda (phiR r (a,b)) =
      gMap r '' (hMap (r^2 * u) '' Lambda (a,b)) := by
  rw [← gMap_lattice hr ha, image_image, image_image]
  congr 1
  funext v
  exact hMap_gMap u r hr v

/-- No horizontal vector of length at most `r` can occur before the
scaled first return time. -/
lemma scaled_horizontal_time_lower {r a b u s : ℝ}
    (hr : 0 < r) (hx : (a,b) ∈ Omega) (hu : 0 < u) (hs : 0 < s) (hsr : s ≤ r)
    (hv : (s,0) ∈ hMap u '' Lambda (phiR r (a,b))) :
    tau (a,b) ≤ r^2 * u := by
  rw [← gMap_lattice hr.ne' hx.1.ne'] at hv
  obtain ⟨v, ⟨z,hz,rfl⟩, heq⟩ := hv
  have hfst : r * z.1 = s := congrArg Prod.fst heq
  have hsnd : r⁻¹ * z.2 - u * (r * z.1) = 0 := congrArg Prod.snd heq
  have hz1 : 0 < z.1 := by nlinarith
  have hz1r : z.1 ≤ 1 := by nlinarith
  have hz2 : z.2 = r^2 * u * z.1 := by
    calc z.2 = r * (r⁻¹ * z.2) := by field_simp
         _ = r * (u * (r * z.1)) := by rw [sub_eq_zero.mp hsnd]
         _ = r^2 * u * z.1 := by ring
  have hz2p : 0 < z.2 := by rw [hz2]; positivity
  have hmin := lattice_minimum_slope hx hz hz1 hz1r hz2p
  rw [hz2] at hmin
  exact (mul_le_mul_iff_of_pos_right hz1).mp hmin

/-- The first return of `phiR r x` to `Y_r`, with its actual accumulated roof time. -/
theorem phiR_first_return {r a b : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hx : (a,b) ∈ Omega) :
    inducedMap B (Yr r) (phiR r (a,b)) = phiR r (B (a,b)) ∧
    H (firstReturnTime B (Yr r) (phiR r (a,b))) (phiR r (a,b)) = r⁻¹^2 * tau (a,b) := by
  let y := phiR r (a,b)
  let t := r⁻¹^2 * tau (a,b)
  have hy : y ∈ Omega := phiR_mem_Omega hr hr1 hx
  have ht : 0 < t := mul_pos (sq_pos_of_pos (inv_pos.mpr hr)) (tau_pos hx)
  have hscale : r^2 * t = tau (a,b) := by dsimp [t]; field_simp
  let v := gMap r (b, 1/a)
  have hv : v ∈ Lambda y := by
    rw [← gMap_lattice hr.ne' hx.1.ne']
    exact ⟨(b,1/a), ⟨0,1,by ext <;> simp⟩, rfl⟩
  have hvp : 0 < v.1 := mul_pos hr hx.2.2.1
  have hvle : v.1 ≤ 1 := by
    change r * b ≤ 1
    calc r * b ≤ r * 1 := mul_le_mul_of_nonneg_left hx.2.2.2.1 hr.le
         _ ≤ 1 := by simpa using hr1.le
  have hvt : v.2 = t * v.1 := by
    dsimp [v,gMap,t,tau]
    field_simp [hr.ne',hx.1.ne',hx.2.2.1.ne']
  have hex : ∃ N : ℕ, t ≤ H N y := by
    obtain ⟨N,hN⟩ := exists_nat_gt t
    exact ⟨N,hN.le.trans (H_ge_nat hy N)⟩
  letI : DecidablePred (fun N : ℕ => t ≤ H N y) := Classical.decPred _
  let N := Nat.find hex
  have hN : t ≤ H N y := Nat.find_spec hex
  have hpre : ∀ k < N, H k y < t := by
    intro k hk
    exact lt_of_not_ge (Nat.find_min hex hk)
  have hN0 : 0 < N := by
    by_contra h
    have hz : N = 0 := by omega
    simp only [hz,H,Finset.range_zero,Finset.sum_empty] at hN
    exact not_le_of_gt ht hN
  have heqTime : H N y = t := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hN0.ne'
    have hprev := hpre k (by omega)
    have hvec : hMap (H k y) v ∈ Lambda (B^[k] y) := by
      rw [← hMap_H_lattice hy k]
      exact ⟨v,hv,rfl⟩
    have hvheight : 0 < (hMap (H k y) v).2 := by
      change 0 < v.2 - H k y * v.1
      rw [hvt]
      nlinarith
    have hmin := lattice_minimum_slope (B_iterate_mem hy k) hvec hvp hvle hvheight
    change tau (B^[k] y) * v.1 ≤ v.2 - H k y * v.1 at hmin
    rw [hvt] at hmin
    have hroof : tau (B^[k] y) ≤ t - H k y := by nlinarith
    apply le_antisymm ?_ hN
    rw [hk,H_succ]
    linarith
  have hsmall : ∀ k, 0 < k → k < N → B^[k] y ∉ Yr r := by
    intro k hk0 hkN hmem
    have hstate := B_iterate_mem hy k
    have hs : 0 < (B^[k] y).1 := hstate.1
    have hsr : (B^[k] y).1 ≤ r := hmem.2
    have htime : 0 < H k y := lt_of_lt_of_le (by exact_mod_cast hk0) (H_ge_nat hy k)
    have hvec : ((B^[k] y).1,0) ∈ hMap (H k y) '' Lambda y := by
      rw [hMap_H_lattice hy k]
      exact ⟨1,0,by ext <;> simp⟩
    have hlow := scaled_horizontal_time_lower hr hx htime hs hsr hvec
    have hhigh := mul_lt_mul_of_pos_left (hpre k hkN) (sq_pos_of_pos hr)
    rw [hscale] at hhigh
    exact not_lt_of_ge hlow hhigh
  have hend : B^[N] y = phiR r (B (a,b)) := by
    apply Lambda_injective_on (B_iterate_mem hy N) (phiR_mem_Omega hr hr1 (B_mem_Omega hx))
    rw [← hMap_H_lattice hy N, heqTime]
    change hMap t '' Lambda (phiR r (a,b)) = _
    rw [hMap_scaled_lattice hr.ne' hx.1.ne',hscale,hMap_tau_lattice hx,
      gMap_lattice hr.ne' (B_mem_Omega hx).1.ne']
    rfl
  have hendmem : B^[N] y ∈ Yr r := by rw [hend]; exact phiR_mem_Yr hr hr1 (B_mem_Omega hx)
  have hreturn : firstReturnTime B (Yr r) y = N := by
    have hle := firstReturn_le hN0 hendmem
    have hs := firstReturn_spec (T := B) (Y := Yr r) (x := y) ⟨N,hN0,hendmem⟩
    apply le_antisymm hle
    by_contra hlt
    exact hsmall _ hs.1 (by omega) hs.2
  exact ⟨by change B^[firstReturnTime B (Yr r) y] y = _; rw [hreturn]; exact hend,
    by change H (firstReturnTime B (Yr r) y) y = t; rw [hreturn,heqTime]⟩

lemma phiR_first_return_point {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {x : ℝ × ℝ} (hx : x ∈ Omega) :
    inducedMap B (Yr r) (phiR r x) = phiR r (B x) ∧
    H (firstReturnTime B (Yr r) (phiR r x)) (phiR r x) = r⁻¹^2 * tau x := by
  cases x with
  | mk a b => exact phiR_first_return hr hr1 hx

lemma H_succ_left (n : ℕ) (x : ℝ × ℝ) : H (n + 1) x = tau x + H n (B x) := by
  simpa only [Nat.add_comm 1 n, H, Finset.range_one, Finset.sum_singleton, iterate_zero,
    id_eq, iterate_one] using H_add 1 n x

/-- Equation (3) for the actual accumulated ordinary roof time to the
`n`th induced return. -/
theorem phiR_time_scaling {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∀ n : ℕ, ∀ x ∈ Omega, Hr r n (phiR r x) = r⁻¹^2 * H n x := by
  intro n
  induction n with
  | zero => intro x hx; simp [Hr,Rn,H]
  | succ n ih =>
    intro x hx
    have hfirst := phiR_first_return_point hr hr1 hx
    unfold Hr
    rw [Rn_succ_left,H_add]
    change H (firstReturnTime B (Yr r) (phiR r x)) (phiR r x) +
      Hr r n (inducedMap B (Yr r) (phiR r x)) = _
    rw [hfirst.1,hfirst.2,ih (B x) (B_mem_Omega hx),H_succ_left]
    ring

/-- The full, pointwise conjugacy conclusion of Lemma 2. -/
theorem Lemma2Conjugacy : Lemma2ConjugacyStatement := by
  intro r hr hr1 x hx
  exact (phiR_first_return_point hr hr1 hx).1

/-- The full induced time-scaling conclusion of Lemma 2. -/
theorem Lemma2TimeScaling : Lemma2TimeScalingStatement := by
  intro r hr hr1
  exact phiR_time_scaling hr hr1

/-- Lemma 2, with all source conclusions and no added mathematical premise. -/
theorem Lemma2 : Lemma2Statement := by
  intro r hr hr1
  obtain ⟨hmap,hleft,hright⟩ := Lemma2Bijection r hr hr1
  refine ⟨hmap,hleft,hright,measurePreserving_phiR r hr hr1,?_,?_,phiR_tendstoInMeasure⟩
  · filter_upwards [ae_mem_Omega] with x hx
    exact (phiR_first_return_point hr hr1 hx).1
  · intro n
    filter_upwards [ae_mem_Omega] with x hx
    exact phiR_time_scaling hr hr1 n x hx

end
end Paper14

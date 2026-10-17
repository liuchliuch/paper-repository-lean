import Paper14.PrimitiveReturns

open Set Function
open Classical
namespace Paper14
noncomputable section

/-- Every ordinary return supplies its actual primitive lattice vector at time zero. -/
lemma ordinary_return_primitive {x : ℝ × ℝ} (hx : x ∈ Omega) (j : ℕ) :
    IsPrimitiveVec x ((B^[j] x).1,H j x*(B^[j] x).1) := by
  let y := B^[j] x
  let v : ℝ × ℝ := (y.1,H j x*y.1)
  have hy : y ∈ Omega := B_iterate_mem hx j
  have hprim : IsPrimitiveVec y (y.1,0) := by
    simpa using (primitiveIffCoprime y.1 y.2 hy 1 0).mpr isCoprime_one_left
  have heq : hMap (H j x) v = (y.1,0) := by ext <;> simp [v,hMap]
  have hv : v ∈ Lambda x := by
    have hh : hMap (H j x) v ∈ hMap (H j x) '' Lambda x := by
      rw [hMap_H_lattice hx j,heq]
      exact hprim.1
    obtain ⟨w,hw,hwv⟩ := hh
    have hwveq : w=v := hMap_injective (H j x) hwv
    exact hwveq ▸ hw
  refine ⟨hv,?_,?_⟩
  · intro hz
    have hh := congrArg Prod.fst hz
    exact hy.1.ne' hh
  · intro k w hw hvw
    have hwm : hMap (H j x) w ∈ Lambda y := by
      rw [← hMap_H_lattice hx j]
      exact ⟨w,hw,rfl⟩
    change v = (k : ℝ) • w at hvw
    have heqm : (y.1,0) = (k : ℝ) • hMap (H j x) w := by
      rw [← heq,hvw,hMap_smul]
    rcases hprim.2.2 k (hMap (H j x) w) hwm heqm with hk | hw0
    · exact Or.inl hk
    · right
      apply hMap_injective (H j x)
      simpa [hMap] using hw0

/-- An omitted return before the roof bound is represented in the actual F_2 finite box. -/
theorem ordinary_outside_F2_pair {x : ℝ × ℝ} {r : ℝ} (hx : x ∈ Yr r)
    {n j : ℕ} (hj : 0 < j) (hjN : j ≤ Rn B (Yr r) n x)
    (hout : B^[j] x ∉ Yr r) (hroof : Hr r n x < 4*(n : ℝ))
    (hr0 : 0 < r) {α : ℝ} (hr : r=1-α/(n : ℝ)) (hε : α/(n : ℝ) < 1) :
    ∃ pr : ℤ × ℤ,
      pr ∈ (Finset.Icc (-(4*(2*n) : ℤ)) (4*(2*n)) ×ˢ Finset.Icc (1 : ℤ) (2*(2*n))).filter
        (fun pr => inZRect (2*n) ((2*α)/(2*n : ℕ)) x pr.1 pr.2) ∧
      H j x = ((pr.2 : ℝ)/x.1)/((pr.2 : ℝ)*x.2-(pr.1 : ℝ)*x.1) := by
  classical
  let u := (B^[j] x).1
  let v := H j x*u
  have hy := B_iterate_mem hx.1 j
  have hu0 : 0 < u := hy.1
  have hu1 : u ≤ 1 := hy.2.1
  have hru : r < u := lt_of_not_ge (fun hu => hout ⟨hy,hu⟩)
  have hH0 : 0 < H j x := by simpa [H] using (H_strictMono hx.1 hj)
  have hHN : H j x ≤ Hr r n x := (H_strictMono hx.1).monotone hjN
  have hv0 : 0 < v := mul_pos hH0 hu0
  have hvn : v ≤ 4*(n : ℝ) := by
    have hh : v ≤ H j x := mul_le_of_le_one_right hH0.le hu1
    linarith
  have hprim : IsPrimitiveVec x (u,v) := ordinary_return_primitive hx.1 j
  obtain ⟨p,q,hp,hq⟩ := mem_Lambda.mp hprim.1
  replace hp := hp.symm
  replace hq := hq.symm
  have hvec : ((p : ℝ)*x.1+(q : ℝ)*x.2,(q : ℝ)/x.1) = (u,v) := Prod.ext hp hq
  have hcop : IsCoprime p q := (primitiveIffCoprime x.1 x.2 hx.1 p q).mp (by rw [hvec]; exact hprim)
  have hueq : (q : ℝ)*x.2-((-p : ℤ) : ℝ)*x.1 = u := by push_cast; linarith [hp]
  have hq0 : 0 < q := by
    have hh : (0 : ℝ) < q := by
      have he : (q : ℝ) = v*x.1 := by rw [← hq]; field_simp [hx.1.1.ne']
      rw [he]
      exact mul_pos hv0 hx.1.1
    exact_mod_cast hh
  have hqn : (q : ℝ) ≤ 4*(n : ℝ) := by
    have he : (q : ℝ) = v*x.1 := by rw [← hq]; field_simp [hx.1.1.ne']
    rw [he]
    exact (mul_le_of_le_one_right hv0.le hx.1.2.1).trans hvn
  have heps : (2*α)/(2*n : ℕ) = α/(n : ℝ) := by push_cast; field_simp
  have hrect : inZRect (2*n) ((2*α)/(2*n : ℕ)) x (-p) q := by
    rw [heps]
    refine ⟨hq0,?_,?_,?_,?_,?_,hcop.neg_left⟩
    · push_cast; linarith
    · rw [hueq,← hr]; exact hru
    · rw [hueq]; exact hu1
    · rw [hq]; exact hv0
    · rw [hq]; push_cast; linarith
  have hb := rectangle_coeff_bounds hx.1 hε (by rw [hueq,← hr]; exact hru)
    (by rw [hueq]; exact hu1) (by rw [hq]; exact hv0) (n := 2*n) (by rw [hq]; push_cast; linarith)
  refine ⟨(-p,q),?_,?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨?_,hrect⟩
    simp only [Finset.mem_product,Finset.mem_Icc]
    push_cast at hb ⊢
    constructor <;> constructor <;> omega
  · rw [hueq,hq]
    dsimp [v]
    field_simp [hu0.ne']

end
end Paper14

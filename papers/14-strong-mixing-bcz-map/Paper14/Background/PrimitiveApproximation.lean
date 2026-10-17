import Paper14.Background.SL2Integer
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

open Set Filter Topology
open scoped Matrix
namespace Paper14.Background
noncomputable section

/-- An irrational rotation approaches an integer from below at arbitrarily
large positive times. -/
theorem irrational_positive_remainder {ξ ε : ℝ} (hξ : Irrational ξ) (hε : 0<ε) (N : ℕ) :
    ∃ n : ℕ,N≤n ∧ ∃ p : ℤ,0<(p : ℝ)-(n : ℝ)*ξ ∧ (p : ℝ)-(n : ℝ)*ξ<ε := by
  let a : AddCircle (1 : ℝ) := (-ξ : ℝ)
  have hd : DenseRange (fun k : ℤ => k • a) := by
    apply AddCircle.denseRange_zsmul_coe_iff.mpr
    simpa using hξ.neg
  let v : AddCircle (1 : ℝ) := ((ε/2 : ℝ) : AddCircle (1 : ℝ))
  have hv : MapClusterPt v atTop (fun n : ℕ => n • a) := by
    apply (mapClusterPt_atTop_nsmul_tfae v a).out 3 0 |>.mp
    rw [hd.closure_range]
    trivial
  let U : Set (AddCircle (1 : ℝ)) := (QuotientAddGroup.mk : ℝ → AddCircle (1 : ℝ)) '' Ioo 0 ε
  have hU : IsOpen U := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hvU : v∈U := ⟨ε/2,by constructor <;> linarith,rfl⟩
  obtain ⟨n,hn,hnu⟩ := frequently_atTop.mp (hv.frequently (hU.mem_nhds hvU)) N
  obtain ⟨u,hu,hun⟩ := hnu
  have heq : (QuotientAddGroup.mk ((n : ℝ)*(-ξ)) : AddCircle (1 : ℝ))=QuotientAddGroup.mk u := by
    change (u : AddCircle (1 : ℝ))=n • ((-ξ : ℝ) : AddCircle (1 : ℝ)) at hun
    rw [← AddCircle.coe_nsmul] at hun
    simpa only [nsmul_eq_mul] using hun.symm
  obtain ⟨p,hp⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp heq)
  have hpu : (p : ℝ)-(n : ℝ)*ξ=u := by
    simp only [zsmul_eq_mul,mul_one] at hp
    nlinarith [hp]
  exact ⟨n,hn,p,by linarith [hu.1],by linarith [hu.2]⟩

/-- Primitive coefficients can be extracted without losing a strict positive
horizontal bound or the sign of the vertical coordinate. -/
theorem primitive_coefficients_of_short_vector {a b c d : ℝ} {p q : ℤ}
    (hp : 0<(p : ℝ)*a+(q : ℝ)*b)
    (hp1 : (p : ℝ)*a+(q : ℝ)*b≤1)
    (hv : (p : ℝ)*c+(q : ℝ)*d<0) :
    ∃ p' q' : ℤ,Int.gcd p' q'=1 ∧
      0<(p' : ℝ)*a+(q' : ℝ)*b ∧ (p' : ℝ)*a+(q' : ℝ)*b≤1 ∧
      (p' : ℝ)*c+(q' : ℝ)*d<0 := by
  have hg : 0<Int.gcd p q := by
    by_contra h
    have h0 : Int.gcd p q=0 := by omega
    have hz := Int.gcd_eq_zero_iff.mp h0
    simp [hz.1,hz.2] at hp
  obtain ⟨p',q',hcop,hp',hq'⟩ := Int.exists_gcd_one hg
  let k : ℝ := Int.gcd p q
  have hk : 0<k := by dsimp [k]; exact_mod_cast hg
  have hk1 : 1≤k := by dsimp [k]; exact_mod_cast (show 1≤Int.gcd p q by omega)
  have heqp : (p : ℝ)=(p' : ℝ)*k := by dsimp [k]; exact_mod_cast hp'
  have heqq : (q : ℝ)=(q' : ℝ)*k := by dsimp [k]; exact_mod_cast hq'
  rw [heqp,heqq] at hp hp1 hv
  refine ⟨p',q',hcop,?_,?_,?_⟩
  · nlinarith
  · have hpos : 0<(p' : ℝ)*a+(q' : ℝ)*b := by nlinarith
    nlinarith
  · nlinarith


/-- Every matrix whose top-row slope is irrational has a primitive lattice
vector in the positive unit strip below the horizontal axis. -/
theorem sl_exists_short_negative_column (g : SL2R) (ha : 0<g 0 0)
    (hξ : Irrational (g 0 1/g 0 0)) :
    ∃ γ : SL2Z,0<(g*slIntegerEmbedding γ) 0 0 ∧
      (g*slIntegerEmbedding γ) 0 0≤1 ∧ (g*slIntegerEmbedding γ) 1 0<0 := by
  obtain ⟨N,hN⟩ := exists_nat_gt |g 1 0|
  obtain ⟨n,hn,p,hp,hp1⟩ := irrational_positive_remainder hξ (one_div_pos.mpr ha) N
  let u : ℝ := (p : ℝ)*g 0 0-(n : ℝ)*g 0 1
  have huEq : u=g 0 0*((p : ℝ)-(n : ℝ)*(g 0 1/g 0 0)) := by
    dsimp [u]
    field_simp [ha.ne']
  have hu : 0<u := by rw [huEq]; exact mul_pos ha hp
  have hu1 : u≤1 := by
    rw [huEq]
    have h := mul_lt_mul_of_pos_left hp1 ha
    have hc : g 0 0*(1/g 0 0)=1 := by field_simp
    linarith
  have hnc : |g 1 0|<(n : ℝ) := hN.trans_le (by exact_mod_cast hn)
  have hcu : g 1 0*u≤|g 1 0| :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hu.le).trans
      (mul_le_of_le_one_right (abs_nonneg _) hu1)
  have hd : g 0 0*g 1 1-g 0 1*g 1 0=1 := by simpa only [Matrix.det_fin_two] using g.property
  have hvEq : g 0 0*((p : ℝ)*g 1 0-(n : ℝ)*g 1 1)=g 1 0*u-(n : ℝ) := by
    dsimp [u]
    linear_combination -(n : ℝ)*hd
  have hv : (p : ℝ)*g 1 0+((-(n : ℤ) : ℤ) : ℝ)*g 1 1<0 := by
    push_cast
    nlinarith
  have hp0 : 0<(p : ℝ)*g 0 0+((-(n : ℤ) : ℤ) : ℝ)*g 0 1 := by simpa [u] using hu
  have hp01 : (p : ℝ)*g 0 0+((-(n : ℤ) : ℤ) : ℝ)*g 0 1≤1 := by simpa [u] using hu1
  obtain ⟨p',q',hcop,hx,hx1,hy⟩ := primitive_coefficients_of_short_vector hp0 hp01 hv
  let γ : SL2Z := ⟨!![p',-Int.gcdB p' q';q',Int.gcdA p' q'],by
    simp only [Matrix.det_fin_two]
    change p'*Int.gcdA p' q'-(-Int.gcdB p' q')*q'=1
    have hbz := Int.gcd_eq_gcd_ab p' q'
    rw [hcop] at hbz
    norm_num at hbz
    nlinarith⟩
  refine ⟨γ,?_,?_,?_⟩
  all_goals simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals dsimp [slIntegerEmbedding,Matrix.SpecialLinearGroup.map,γ]
  · nlinarith [hx]
  · nlinarith [hx1]
  · nlinarith [hy]

end
end Paper14.Background

import Paper14.Background.SL2FlatMeasure
import Paper14.Background.SL2Integer
import Paper14.ReturnGeometry

open Matrix Set Function
open scoped Matrix MatrixGroups
namespace Paper14
noncomputable section
open Background

/-- The actual lattice spanned by the columns of a unimodular real matrix. -/
def slLattice (g : SL2R) : Set (ℝ × ℝ) :=
  {v | ∃ p q : ℤ,v=((p : ℝ)*g 0 0+(q : ℝ)*g 0 1,(p : ℝ)*g 1 0+(q : ℝ)*g 1 1)}

lemma slLattice_mul_subset (g : SL2R) {h : SL2R} (hh : h∈slIntegerSubgroup) :
    slLattice (g*h) ⊆ slLattice g := by
  obtain ⟨M,rfl⟩ := hh
  rintro v ⟨p,q,rfl⟩
  refine ⟨p*M 0 0+q*M 0 1,p*M 1 0+q*M 1 1,?_⟩
  ext
  all_goals simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals dsimp [slIntegerEmbedding,Matrix.SpecialLinearGroup.map]
  all_goals push_cast
  all_goals ring

lemma slLattice_mul_eq (g : SL2R) {h : SL2R} (hh : h∈slIntegerSubgroup) :
    slLattice (g*h)=slLattice g := by
  apply Subset.antisymm (slLattice_mul_subset g hh)
  simpa only [mul_inv_cancel_right] using slLattice_mul_subset (g*h) (slIntegerSubgroup.inv_mem hh)

lemma slLattice_eq_of_quotient_eq {g h : SL2R}
    (heq : (QuotientGroup.mk g : SL2R ⧸ slIntegerSubgroup)=QuotientGroup.mk h) :
    slLattice g=slLattice h := by
  have hm := slLattice_mul_eq g (QuotientGroup.eq.mp heq)
  simpa only [mul_inv_cancel_left] using hm.symm

lemma quotient_eq_of_slLattice_eq {g h : SL2R} (heq : slLattice g=slLattice h) :
    (QuotientGroup.mk g : SL2R ⧸ slIntegerSubgroup)=QuotientGroup.mk h := by
  have hc (j : Fin 2) : (h 0 j,h 1 j)∈slLattice g := by
    rw [heq]
    fin_cases j
    · exact ⟨1,0,by simp⟩
    · exact ⟨0,1,by simp⟩
  choose p q hpq using hc
  let M : Matrix (Fin 2) (Fin 2) ℝ := !![(p 0 : ℝ),(p 1 : ℝ);(q 0 : ℝ),(q 1 : ℝ)]
  have hM : (g : Matrix (Fin 2) (Fin 2) ℝ)*M=(h : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    have hj := hpq j
    fin_cases i
    · have hx := congrArg Prod.fst hj
      fin_cases j <;> simpa [M,Matrix.mul_apply,Fin.sum_univ_two,mul_comm] using hx.symm
    · have hx := congrArg Prod.snd hj
      fin_cases j <;> simpa [M,Matrix.mul_apply,Fin.sum_univ_two,mul_comm] using hx.symm
  have hInv : ((g⁻¹ : SL2R) : Matrix (Fin 2) (Fin 2) ℝ)*(g : Matrix (Fin 2) (Fin 2) ℝ)=1 := by
    simpa only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_one] using
      congrArg (fun k : SL2R => (k : Matrix (Fin 2) (Fin 2) ℝ)) (inv_mul_cancel g)
  have hγ : (g⁻¹*h : Matrix (Fin 2) (Fin 2) ℝ)=M := by
    change ((g⁻¹ : SL2R) : Matrix (Fin 2) (Fin 2) ℝ)*(h : Matrix (Fin 2) (Fin 2) ℝ)=M
    rw [← hM,← Matrix.mul_assoc,hInv,one_mul]
  apply QuotientGroup.eq.mpr
  apply (mem_slIntegerSubgroup _).mpr
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨p 0,by simpa [M] using congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0) hγ⟩
  · exact ⟨p 1,by simpa [M] using congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) hγ⟩
  · exact ⟨q 0,by simpa [M] using congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 1 0) hγ⟩
  · exact ⟨q 1,by simpa [M] using congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 1 1) hγ⟩

/-- Big-cell matrix coordinates give precisely the actual horocycle lattice
used throughout the paper. -/
lemma slLattice_slChart {z : SL2Coordinates} (hz : z 0≠0) :
    slLattice (slChart z)=hMap (z 2) '' Lambda (z 0,z 1) := by
  ext v
  constructor
  · rintro ⟨p,q,rfl⟩
    refine ⟨((p : ℝ)*z 0+(q : ℝ)*z 1,(q : ℝ)/z 0),⟨p,q,rfl⟩,?_⟩
    ext <;> simp [slChart,hz,hMap,div_eq_mul_inv] <;> ring
  · rintro ⟨w,⟨p,q,rfl⟩,rfl⟩
    refine ⟨p,q,?_⟩
    ext <;> simp [slChart,hz,hMap,div_eq_mul_inv] <;> ring

/-- Distinct points inside one roof interval cannot represent the same lattice. -/
theorem bcz_suspension_quotient_injective
    {x y : ℝ × ℝ} (hx : x∈Omega) (hy : y∈Omega) {s t : ℝ}
    (hs : 0≤s) (hst : s<tau x) (ht : 0≤t) (htt : t<tau y)
    (heq : (QuotientGroup.mk (slChart ![x.1,x.2,s]) : SL2R ⧸ slIntegerSubgroup)=
      QuotientGroup.mk (slChart ![y.1,y.2,t])) : x=y ∧ s=t := by
  have hlat := slLattice_eq_of_quotient_eq heq
  rw [slLattice_slChart (by simpa using hx.1.ne'),slLattice_slChart (by simpa using hy.1.ne')] at hlat
  have hmin {x y : ℝ × ℝ} (hx : x∈Omega) (hy : y∈Omega) {s t : ℝ}
      (hsl : s<t) (hs : 0≤s) (ht : t<tau y)
      (hlat : hMap s '' Lambda x=hMap t '' Lambda y) : False := by
    have hv : hMap s (x.1,0)∈hMap t '' Lambda y := by
      rw [← hlat]
      exact ⟨(x.1,0),⟨1,0,by ext <;> simp⟩,rfl⟩
    obtain ⟨v,hv,hveq⟩ := hv
    have hvec : (x.1,(t-s)*x.1)∈Lambda y := by
      convert hv using 1
      have hh := congrArg (hMap (-t)) hveq
      simp only [← hMap_add,neg_add_cancel,hMap_zero] at hh
      calc
        (x.1,(t-s)*x.1)=hMap (-t+s) (x.1,0) := by ext <;> simp [hMap] <;> ring
        _ = v := hh.symm
    have hvpos : 0<(t-s)*x.1 := mul_pos (sub_pos.mpr hsl) hx.1
    have hh := lattice_minimum_slope hy hvec hx.1 hx.2.1 hvpos
    change tau y*x.1≤(t-s)*x.1 at hh
    nlinarith [hx.1]
  have htime : s=t := by
    rcases lt_trichotomy s t with h | h | h
    · exact False.elim (hmin hx hy h hs htt hlat)
    · exact h
    · exact False.elim (hmin hy hx h ht hst hlat.symm)
  refine ⟨Lambda_injective_on hx hy ?_,htime⟩
  rw [htime] at hlat
  exact (Set.image_injective.mpr (hMap_injective t)) hlat

end
end Paper14

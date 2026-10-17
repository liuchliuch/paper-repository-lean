import Paper20.SeminormalScalars
import Paper20.StandardContents

namespace Paper20.Seminormal
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

section Field
variable {F : Type*} [Field F]

/-- The adjacent-row boundary has the genuine Hecke eigenvalue v. -/
lemma diagonal_row (v x : F) (hv : v≠0) (hx : x≠0) (hv2 : v^2≠1) :
    diagonal v x (v^2*x)=v := by
  have hd : v^2*x-x≠0 := by
    have he : v^2*x-x=(v^2-1)*x := by ring
    rw [he]
    exact mul_ne_zero (sub_ne_zero.mpr hv2) hx
  unfold diagonal
  field_simp [hv,hx,hd,sub_ne_zero.mpr hv2] <;> ring

/-- The adjacent-column boundary has the genuine Hecke eigenvalue -v^-1. -/
lemma diagonal_column (v x : F) (hv : v≠0) (hx : x≠0) (hv2 : v^2≠1) :
    diagonal v (v^2*x) x= -v⁻¹ := by
  have hxy : x≠v^2*x := by
    intro he
    have hd : (v^2-1)*x=0 := by rw [sub_mul,one_mul,← he,sub_self]
    exact (mul_ne_zero (sub_ne_zero.mpr hv2) hx) hd
  have hs := diagonal_sum v x (v^2*x) hxy
  rw [diagonal_row v x hv hx hv2] at hs
  linear_combination hs

/-- The faithful integer-power parameter is in particular neither a zero
nor a root of the exceptional quadratic boundary denominator. -/
lemma parameter_square_ne_one (v : F) (hp : Function.Injective (fun d : ℤ => v^d)) : v^2≠1 := by
  intro he
  have hi : v^(2:ℤ)=v^(0:ℤ) := by simpa only [zpow_ofNat,zpow_zero,pow_zero] using he
  have hn := hp hi
  norm_num at hn

open Paper20.YoungShapes

/-- The boundary diagonal on any actual nonexchangeable adjacent standard
filling is exactly one of the two required one-dimensional eigenvalues. -/
theorem nonexchangeable_diagonal (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d))
    {n : ℕ} {μ : Shape n} (t : StandardFilling μ) (i j : Fin n)
    (hij : j.val=i.val+1) (hn : ¬Exchangeable t i j) :
    diagonal v (v^(2*fillingContent t i)) (v^(2*fillingContent t j))=v ∨
      diagonal v (v^(2*fillingContent t i)) (v^(2*fillingContent t j))= -v⁻¹ := by
  have hv2 := parameter_square_ne_one v hp
  have hc := nonexchangeable_content t i j hij hn
  rcases hc with hc | hc
  · left
    have hy : v^(2*fillingContent t j)=v^2*v^(2*fillingContent t i) := by
      have he : 2*fillingContent t j=(2:ℤ)+2*fillingContent t i := by omega
      rw [he,zpow_add₀ hv,zpow_ofNat]
    rw [hy]
    exact diagonal_row v _ hv (zpow_ne_zero _ hv) hv2
  · right
    have hx : v^(2*fillingContent t i)=v^2*v^(2*fillingContent t j) := by
      have he : 2*fillingContent t i=(2:ℤ)+2*fillingContent t j := by omega
      rw [he,zpow_add₀ hv,zpow_ofNat]
    rw [hx]
    exact diagonal_column v _ hv (zpow_ne_zero _ hv) hv2

/-- The actual one-state boundary obeys the quadratic Hecke relation even
when the off-diagonal standard filling is absent. -/
theorem nonexchangeable_quadratic (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d))
    {n : ℕ} {μ : Shape n} (t : StandardFilling μ) (i j : Fin n)
    (hij : j.val=i.val+1) (hn : ¬Exchangeable t i j) :
    (diagonal v (v^(2*fillingContent t i)) (v^(2*fillingContent t j)))^2=
      (v-v⁻¹)*diagonal v (v^(2*fillingContent t i)) (v^(2*fillingContent t j))+1 := by
  rcases nonexchangeable_diagonal v hv hp t i j hij hn with he | he
  · rw [he]; field_simp <;> ring
  · rw [he]; field_simp <;> ring

end Field
end
end Paper20.Seminormal

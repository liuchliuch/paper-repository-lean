import Mathlib

namespace Paper20.Seminormal
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

section Field
variable {F : Type*} [Field F]

/-- The actual rational seminormal diagonal coefficient, with x,y the
successive Murphy eigenvalues. -/
def diagonal (v x y : F) : F := (v-v⁻¹)*y/(y-x)

def offDiagonal (v x y : F) : F := v-diagonal v x y

lemma diagonal_sum (v x y : F) (hxy : x≠y) :
    diagonal v x y+diagonal v y x=v-v⁻¹ := by
  unfold diagonal
  field_simp [sub_ne_zero.mpr hxy,sub_ne_zero.mpr hxy.symm]
  ring

/-- The quadratic Hecke relation on the genuine two-tableau block. -/
theorem offDiagonal_product (v x y : F) (hv : v≠0) (hxy : x≠y) :
    offDiagonal v x y*offDiagonal v y x=
      1+(v-v⁻¹)*diagonal v x y-diagonal v x y^2 := by
  have hs := diagonal_sum v x y hxy
  have hyx : diagonal v y x=v-v⁻¹-diagonal v x y := by linear_combination hs
  unfold offDiagonal
  rw [hyx]
  field_simp
  ring

/-- The basic three-eigenvalue rational identity underlying the braid
relation. Every denominator is a genuine pairwise eigenvalue difference. -/
theorem diagonal_three (v x y z : F) (hxy : x≠y) (hyz : y≠z) (hxz : x≠z) :
    diagonal v x y*diagonal v y z=
      diagonal v x z*(diagonal v x y+diagonal v y z-(v-v⁻¹)) := by
  unfold diagonal
  field_simp [sub_ne_zero.mpr hxy.symm,sub_ne_zero.mpr hyz.symm,sub_ne_zero.mpr hxz.symm]
  ring

/-- Equality of the two diagonal contributions in the length-three
braid word, derived from the proved two- and three-eigenvalue identities. -/
theorem braid_diagonal (v x y z : F) (hv : v≠0)
    (hxy : x≠y) (hyz : y≠z) (hxz : x≠z) :
    diagonal v x y^2*diagonal v y z+
        offDiagonal v x y*offDiagonal v y x*diagonal v x z=
      diagonal v y z^2*diagonal v x y+
        offDiagonal v y z*offDiagonal v z y*diagonal v x z := by
  rw [offDiagonal_product v x y hv hxy,offDiagonal_product v y z hv hyz]
  linear_combination (norm := ring_nf)
    (diagonal v x y-diagonal v y z)*diagonal_three v x y z hxy hyz hxz

end Field
end
end Paper20.Seminormal

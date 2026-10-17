import Paper20.TableauHeckeBraidFree

namespace Paper20.Seminormal
open Paper20.YoungShapes
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

section Field
variable {F : Type*} [Field F]

lemma diagonal_content_row (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d)) (a b : ℤ) (hc : b-a=1) :
    diagonal v (v^(2*a)) (v^(2*b))=v := by
  have hy : v^(2*b)=v^2*v^(2*a) := by
    have he : 2*b=(2:ℤ)+2*a := by omega
    rw [he,zpow_add₀ hv,zpow_ofNat]
  rw [hy]
  exact diagonal_row v _ hv (zpow_ne_zero _ hv) (parameter_square_ne_one v hp)

lemma diagonal_content_column (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d)) (a b : ℤ) (hc : b-a= -1) :
    diagonal v (v^(2*a)) (v^(2*b))= -v⁻¹ := by
  have hx : v^(2*a)=v^2*v^(2*b) := by
    have he : 2*a=(2:ℤ)+2*b := by omega
    rw [he,zpow_add₀ hv,zpow_ofNat]
  rw [hx]
  exact diagonal_column v _ hv (zpow_ne_zero _ hv) (parameter_square_ne_one v hp)

/-- A forbidden adjacent tableau edge has zero product of its two
oppositely oriented off-diagonal coefficients. This is the boundary
cancellation needed in a length-three braid computation. -/
theorem nonexchangeable_offDiagonal_product (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d))
    {n : ℕ} {μ : Shape n} (t : StandardFilling μ) (i j : Fin n)
    (hij : j.val=i.val+1) (hn : ¬Exchangeable t i j) :
    offDiagonal v (eigenvalue v t i) (eigenvalue v t j)*
      offDiagonal v (eigenvalue v t j) (eigenvalue v t i)=0 := by
  rw [offDiagonal_product v (eigenvalue v t i) (eigenvalue v t j) hv
    (filling_adjacent_eigenvalues_ne v hp t i j hij)]
  have he := nonexchangeable_quadratic v hv hp t i j hij hn
  change (diagonal v (eigenvalue v t i) (eigenvalue v t j))^2=
    (v-v⁻¹)*diagonal v (eigenvalue v t i) (eigenvalue v t j)+1 at he
  linear_combination (norm := ring_nf) -he

/-- When both adjacent exchanges are forbidden, the three actual cells
form a straight chain: the two scalar eigenvalues agree. Mixed row/column
turns would give equal first and third contents, which actual standard
fillings prohibit over three consecutive labels. -/
theorem chain_diagonal_equal (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d))
    {n : ℕ} {μ : Shape n} (t : StandardFilling μ) (i j k : Fin n)
    (hij : j.val=i.val+1) (hjk : k.val=j.val+1)
    (hi : ¬Exchangeable t i j) (hj : ¬Exchangeable t j k) :
    diagonal v (eigenvalue v t i) (eigenvalue v t j)=
      diagonal v (eigenvalue v t j) (eigenvalue v t k) := by
  have h1 := nonexchangeable_content t i j hij hi
  have h2 := nonexchangeable_content t j k hjk hj
  have h3 := (filling_content_triple_ne t i j k hij hjk).2.2
  have hs : fillingContent t j-fillingContent t i=fillingContent t k-fillingContent t j := by omega
  change diagonal v (v^(2*fillingContent t i)) (v^(2*fillingContent t j))=
    diagonal v (v^(2*fillingContent t j)) (v^(2*fillingContent t k))
  rcases h1 with h1 | h1
  · rw [diagonal_content_row v hv hp _ _ h1,
      diagonal_content_row v hv hp _ _ (by omega)]
  · rw [diagonal_content_column v hv hp _ _ h1,
      diagonal_content_column v hv hp _ _ (by omega)]

end Field
end
end Paper20.Seminormal

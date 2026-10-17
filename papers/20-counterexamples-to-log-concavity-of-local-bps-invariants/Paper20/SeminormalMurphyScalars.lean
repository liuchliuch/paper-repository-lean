import Paper20.TableauBraidBoundaryScalars

namespace Paper20.Seminormal
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

section Field
variable {F : Type*} [Field F]

lemma diagonal_weighted_sum (v x y : F) (hxy : x≠y) :
    diagonal v x y*x+diagonal v y x*y=0 := by
  unfold diagonal
  field_simp [sub_ne_zero.mpr hxy,sub_ne_zero.mpr hxy.symm]
  ring

/-- The diagonal coefficient identity in T_i L_i T_i=L_(i+1). -/
theorem murphy_diagonal (v x y : F) (hv : v≠0) (hxy : x≠y) :
    diagonal v x y^2*x+offDiagonal v x y*offDiagonal v y x*y=y := by
  rw [offDiagonal_product v x y hv hxy]
  have ha : diagonal v x y*(y-x)=(v-v⁻¹)*y := by
    unfold diagonal
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr hxy.symm)
  linear_combination (norm := ring_nf) -diagonal v x y*ha

open Paper20.YoungShapes

/-- The same Murphy relation at an actual row/column boundary, where
only a single genuine standard tableau is present. -/
theorem nonexchangeable_murphy (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d))
    {n : ℕ} {μ : Shape n} (t : StandardFilling μ) (i j : Fin n)
    (hij : j.val=i.val+1) (hn : ¬Exchangeable t i j) :
    diagonal v (eigenvalue v t i) (eigenvalue v t j)^2*eigenvalue v t i=eigenvalue v t j := by
  have hc := nonexchangeable_content t i j hij hn
  change diagonal v (v^(2*fillingContent t i)) (v^(2*fillingContent t j))^2*
    v^(2*fillingContent t i)=v^(2*fillingContent t j)
  rcases hc with hc | hc
  · rw [diagonal_content_row v hv hp _ _ hc]
    have he : 2*fillingContent t j=(2:ℤ)+2*fillingContent t i := by omega
    rw [he,zpow_add₀ hv,zpow_ofNat]
  · rw [diagonal_content_column v hv hp _ _ hc]
    have he : 2*fillingContent t i=(2:ℤ)+2*fillingContent t j := by omega
    rw [he,zpow_add₀ hv,zpow_ofNat]
    field_simp <;> ring

end Field
end
end Paper20.Seminormal

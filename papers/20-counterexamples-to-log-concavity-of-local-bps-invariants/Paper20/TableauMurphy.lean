import Paper20.SeminormalMurphyScalars
import Paper20.TableauHeckeBraid

namespace Paper20.Seminormal
open Paper20.YoungShapes
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

section Field
variable {F : Type*} [Field F]

/-- The genuine diagonal operator with the actual content eigenvalues
of the cells in an actual standard Young filling. -/
def murphyDiagonal (v : F) {n : ℕ} {μ : Shape n} (i : Fin n) :
    (StandardFilling μ → F) →ₗ[F] (StandardFilling μ → F) where
  toFun f t := eigenvalue v t i*f t
  map_add' f g := by ext t; simp only [Pi.add_apply]; ring
  map_smul' a f := by ext t; simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring

/-- The exact Murphy conjugation recurrence on actual tableau vectors,
including the actual missing-exchange boundaries. -/
theorem tableauAction_murphy (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d))
    {n : ℕ} {μ : Shape n} (i j : Fin n) (hij : j.val=i.val+1)
    (f : StandardFilling μ → F) :
    tableauAction v i j hij (fun t => eigenvalue v t i*tableauAction v i j hij f t)=
      fun t => eigenvalue v t j*f t := by
  funext t
  by_cases h : Exchangeable t i j
  · let u := exchange t i j hij h
    have hu : Exchangeable u i j := exchange_incomparable t i j hij h
    have huu : exchange u i j hij hu=t := exchange_exchange t i j hij h
    have hxi : eigenvalue v u i=eigenvalue v t j := by
      simp only [u,exchange_eigenvalue,Equiv.swap_apply_left]
    have hxj : eigenvalue v u j=eigenvalue v t i := by
      simp only [u,exchange_eigenvalue,Equiv.swap_apply_right]
    have het (g : StandardFilling μ → F) := tableauAction_valid v i j hij g t h
    have heu (g : StandardFilling μ → F) := tableauAction_valid v i j hij g u hu
    dsimp only [u] at heu huu hxi hxj
    simp only [het,heu,huu,hxi,hxj]
    have hxy : eigenvalue v t i≠eigenvalue v t j := filling_adjacent_eigenvalues_ne v hp t i j hij
    have hs := diagonal_weighted_sum v (eigenvalue v t i) (eigenvalue v t j) hxy
    have hd := murphy_diagonal v (eigenvalue v t i) (eigenvalue v t j) hv hxy
    linear_combination (norm := ring_nf)
      f (exchange t i j hij h)*offDiagonal v (eigenvalue v t i) (eigenvalue v t j)*hs+f t*hd
  · have het (g : StandardFilling μ → F) := tableauAction_invalid v i j hij g t h
    simp only [het]
    have hs := nonexchangeable_murphy v hv hp t i j hij h
    linear_combination (norm := ring_nf) f t*hs

/-- The Murphy recurrence in the actual finite endomorphism algebra:
T_i D_i T_i equals the content diagonal operator D_(i+1). -/
theorem tableauLinear_murphy (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d))
    {n : ℕ} {μ : Shape n} (i j : Fin n) (hij : j.val=i.val+1) :
    tableauLinear (μ:=μ) v i j hij* murphyDiagonal v i*tableauLinear v i j hij=
      murphyDiagonal v j := by
  apply LinearMap.ext
  intro f
  exact tableauAction_murphy v hv hp i j hij f

theorem murphyDiagonal_commute (v : F) {n : ℕ} {μ : Shape n} (i j : Fin n) :
    murphyDiagonal (μ:=μ) v i*murphyDiagonal v j=murphyDiagonal v j*murphyDiagonal v i := by
  apply LinearMap.ext
  intro f
  funext t
  change eigenvalue v t i*(eigenvalue v t j*f t)=eigenvalue v t j*(eigenvalue v t i*f t)
  ring

end Field
end
end Paper20.Seminormal

import Paper20.SeminormalScalars
import Paper20.HeckeRelations

namespace Paper20.Seminormal
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

section Field
variable {I F : Type*} [DecidableEq I] [Field F]

/-- The rational seminormal adjacent exchange action on genuine
permutations of a set of distinct eigenvalues. -/
def action (v : F) (c : I → F) (i j : I) (f : Equiv.Perm I → F) (σ : Equiv.Perm I) : F :=
  diagonal v (c (σ i)) (c (σ j))*f σ+
    offDiagonal v (c (σ i)) (c (σ j))*f (σ*Equiv.swap i j)

/-- The actual permutation exchange action is linear. -/
def actionLinear (v : F) (c : I → F) (i j : I) :
    (Equiv.Perm I → F) →ₗ[F] (Equiv.Perm I → F) where
  toFun := action v c i j
  map_add' f g := by ext σ; simp only [action,Pi.add_apply]; ring
  map_smul' a f := by ext σ; simp only [action,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring

/-- The quadratic Hecke relation for the genuine rational exchange
operator, derived from its actual two-state coefficient computation. -/
theorem action_quadratic (v : F) (hv : v≠0) (c : I → F) (hc : Function.Injective c)
    (i j : I) (hij : i≠j) (f : Equiv.Perm I → F) :
    action v c i j (action v c i j f)=(v-v⁻¹) • action v c i j f+f := by
  funext σ
  have hxy : c (σ i)≠c (σ j) := fun h => hij (σ.injective (hc h))
  have hs := diagonal_sum v (c (σ i)) (c (σ j)) hxy
  have hp := offDiagonal_product v (c (σ i)) (c (σ j)) hv hxy
  simp only [action,Equiv.Perm.mul_apply,Equiv.swap_apply_left,Equiv.swap_apply_right,
    mul_assoc,Equiv.swap_mul_self,mul_one,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  linear_combination (norm := ring_nf)
    (f (σ*Equiv.swap i j))*offDiagonal v (c (σ i)) (c (σ j))*hs+f σ*hp

/-- The full length-three braid relation for the rational eigenvalue
exchange action on actual permutations. This is an operator identity for
all vectors, not a sample matrix or a numeric test. -/
theorem action_braid (v : F) (hv : v≠0) (c : I → F) (hc : Function.Injective c)
    (i j k : I) (hij : i≠j) (hjk : j≠k) (hik : i≠k) (f : Equiv.Perm I → F) :
    action v c i j (action v c j k (action v c i j f))=
      action v c j k (action v c i j (action v c j k f)) := by
  funext σ
  have hxy : c (σ i)≠c (σ j) := fun h => hij (σ.injective (hc h))
  have hyz : c (σ j)≠c (σ k) := fun h => hjk (σ.injective (hc h))
  have hxz : c (σ i)≠c (σ k) := fun h => hik (σ.injective (hc h))
  have hsxy := diagonal_sum v (c (σ i)) (c (σ j)) hxy
  have hsyz := diagonal_sum v (c (σ j)) (c (σ k)) hyz
  have ht := diagonal_three v (c (σ i)) (c (σ j)) (c (σ k)) hxy hyz hxz
  have hd := braid_diagonal v (c (σ i)) (c (σ j)) (c (σ k)) hv hxy hyz hxz
  have hw : Equiv.swap i j*(Equiv.swap j k*Equiv.swap i j)=
      Equiv.swap j k*(Equiv.swap i j*Equiv.swap j k) := by
    simpa only [mul_assoc] using Paper20.HeckeOperators.swap_braid i j k hij hjk hik
  simp only [action,Equiv.Perm.mul_apply,Equiv.swap_apply_left,Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm,
    Equiv.swap_apply_of_ne_of_ne hij hik,
    mul_assoc,Equiv.swap_mul_self,mul_one,hw]
  linear_combination (norm := ring_nf)
    f σ*hd+
    f (σ*Equiv.swap i j)*offDiagonal v (c (σ i)) (c (σ j))*
      (ht+diagonal v (c (σ i)) (c (σ k))*hsxy)-
    f (σ*Equiv.swap j k)*offDiagonal v (c (σ j)) (c (σ k))*
      (ht+diagonal v (c (σ i)) (c (σ k))*hsyz)

/-- Exchanges on disjoint positions commute as actual rational linear
operators, with their eigenvalue arguments tracked under each permutation. -/
theorem action_commute (v : F) (c : I → F) (i j k l : I)
    (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) (f : Equiv.Perm I → F) :
    action v c i j (action v c k l f)=action v c k l (action v c i j f) := by
  funext σ
  have hm : Equiv.swap i j*Equiv.swap k l=Equiv.swap k l*Equiv.swap i j := by
    rw [Equiv.mul_swap_eq_swap_mul,
      Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm,
      Equiv.swap_apply_of_ne_of_ne hil.symm hjl.symm]
  simp only [action,Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm,
    Equiv.swap_apply_of_ne_of_ne hil.symm hjl.symm,
    Equiv.swap_apply_of_ne_of_ne hik hil,
    Equiv.swap_apply_of_ne_of_ne hjk hjl,mul_assoc,hm]
  ring

/-- The rational exchange maps satisfy the quadratic relation as an
identity in the endomorphism algebra itself. -/
theorem actionLinear_quadratic (v : F) (hv : v≠0) (c : I → F)
    (hc : Function.Injective c) (i j : I) (hij : i≠j) :
    (actionLinear v c i j)^2=(v-v⁻¹) • actionLinear v c i j+1 := by
  apply LinearMap.ext
  intro f
  exact action_quadratic v hv c hc i j hij f

end Field
end
end Paper20.Seminormal

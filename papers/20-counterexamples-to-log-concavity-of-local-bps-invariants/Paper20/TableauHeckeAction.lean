import Paper20.SeminormalBoundary

namespace Paper20.Seminormal
open Paper20.YoungShapes
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

section Field
variable {F : Type*} [Field F]

/-- The actual Murphy eigenvalue attached to a standard-tableau cell. -/
def eigenvalue (v : F) {n : ℕ} {μ : Shape n} (t : StandardFilling μ) (i : Fin n) : F :=
  v^(2*fillingContent t i)

/-- The rational seminormal Hecke action on the finite vector space of
actual standard Young fillings. A nonstandard exchange contributes zero. -/
def tableauAction (v : F) {n : ℕ} {μ : Shape n} (i j : Fin n) (hij : j.val=i.val+1)
    (f : StandardFilling μ → F) (t : StandardFilling μ) : F :=
  diagonal v (eigenvalue v t i) (eigenvalue v t j)*f t+
    if h : Exchangeable t i j then
      offDiagonal v (eigenvalue v t i) (eigenvalue v t j)*f (exchange t i j hij h)
    else 0

lemma tableauAction_valid (v : F) {n : ℕ} {μ : Shape n} (i j : Fin n)
    (hij : j.val=i.val+1) (f : StandardFilling μ → F) (t : StandardFilling μ)
    (h : Exchangeable t i j) :
    tableauAction v i j hij f t=
      diagonal v (eigenvalue v t i) (eigenvalue v t j)*f t+
        offDiagonal v (eigenvalue v t i) (eigenvalue v t j)*f (exchange t i j hij h) := by
  simp only [tableauAction,dif_pos h]

lemma tableauAction_invalid (v : F) {n : ℕ} {μ : Shape n} (i j : Fin n)
    (hij : j.val=i.val+1) (f : StandardFilling μ → F) (t : StandardFilling μ)
    (h : ¬Exchangeable t i j) :
    tableauAction v i j hij f t=diagonal v (eigenvalue v t i) (eigenvalue v t j)*f t := by
  simp only [tableauAction,dif_neg h,add_zero]

@[simp] lemma exchange_eigenvalue (v : F) {n : ℕ} {μ : Shape n}
    (t : StandardFilling μ) (i j : Fin n) (hij : j.val=i.val+1)
    (h : Exchangeable t i j) (k : Fin n) :
    eigenvalue v (exchange t i j hij h) k=eigenvalue v t (Equiv.swap i j k) := rfl

/-- The rational operators on actual standard-tableau vectors satisfy
T_i²=(v-v^-1)T_i+1, including both valid two-tableau blocks and the actual
one-tableau row/column boundaries. -/
theorem tableauAction_quadratic (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d))
    {n : ℕ} {μ : Shape n} (i j : Fin n) (hij : j.val=i.val+1)
    (f : StandardFilling μ → F) :
    tableauAction v i j hij (tableauAction v i j hij f)=
      (v-v⁻¹) • tableauAction v i j hij f+f := by
  funext t
  change tableauAction v i j hij (tableauAction v i j hij f) t=
    (v-v⁻¹)*tableauAction v i j hij f t+f t
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
    have hxy := filling_adjacent_eigenvalues_ne v hp t i j hij
    have hs := diagonal_sum v (eigenvalue v t i) (eigenvalue v t j) hxy
    have hprod := offDiagonal_product v (eigenvalue v t i) (eigenvalue v t j) hv hxy
    linear_combination (norm := ring_nf)
      f (exchange t i j hij h)*offDiagonal v (eigenvalue v t i) (eigenvalue v t j)*hs+f t*hprod
  · have het (g : StandardFilling μ → F) := tableauAction_invalid v i j hij g t h
    simp only [het]
    have hs := nonexchangeable_quadratic v hv hp t i j hij h
    change (diagonal v (eigenvalue v t i) (eigenvalue v t j))^2=
      (v-v⁻¹)*diagonal v (eigenvalue v t i) (eigenvalue v t j)+1 at hs
    linear_combination (norm := ring_nf) f t*hs

/-- The genuine rational standard-tableau action as a linear endomorphism
of its actual finite tableau vector space. -/
def tableauLinear (v : F) {n : ℕ} {μ : Shape n} (i j : Fin n) (hij : j.val=i.val+1) :
    (StandardFilling μ → F) →ₗ[F] (StandardFilling μ → F) where
  toFun := tableauAction v i j hij
  map_add' f g := by
    funext t
    by_cases h : Exchangeable t i j
    · simp only [tableauAction,dif_pos h,Pi.add_apply]; ring
    · simp only [tableauAction,dif_neg h,Pi.add_apply]; ring
  map_smul' a f := by
    funext t
    by_cases h : Exchangeable t i j
    · simp only [tableauAction,dif_pos h,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring
    · simp only [tableauAction,dif_neg h,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring

/-- The quadratic relation in the actual finite endomorphism algebra. -/
theorem tableauLinear_quadratic (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d))
    {n : ℕ} {μ : Shape n} (i j : Fin n) (hij : j.val=i.val+1) :
    (tableauLinear (μ:=μ) v i j hij)^2=(v-v⁻¹) • tableauLinear v i j hij+1 := by
  apply LinearMap.ext
  intro f
  exact tableauAction_quadratic v hv hp i j hij f

end Field
end
end Paper20.Seminormal

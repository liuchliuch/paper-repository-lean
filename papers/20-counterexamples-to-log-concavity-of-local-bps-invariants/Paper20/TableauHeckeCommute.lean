import Paper20.TableauHeckeAction
import Paper20.StandardExchangeDisjoint

namespace Paper20.Seminormal
open Paper20.YoungShapes
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- Disjoint adjacent seminormal generators commute on actual standard
Young fillings, with forbidden intermediate exchanges handled explicitly. -/
theorem tableauAction_commute {F : Type*} [Field F] (v : F)
    {n : ℕ} {μ : Shape n} (i j k l : Fin n)
    (hij : j.val=i.val+1) (hkl : l.val=k.val+1)
    (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l)
    (f : StandardFilling μ → F) :
    tableauAction v i j hij (tableauAction v k l hkl f)=
      tableauAction v k l hkl (tableauAction v i j hij f) := by
  funext t
  by_cases hi : Exchangeable t i j
  · by_cases hk : Exchangeable t k l
    · have hk' := (exchangeable_other t i j k l hij hi hik hil hjk hjl).mpr hk
      have hi' := (exchangeable_other t k l i j hkl hk hik.symm hjk.symm hil.symm hjl.symm).mpr hi
      have he := exchange_commute t i j k l hij hkl hik hil hjk hjl hi hk hk' hi'
      simp only [tableauAction,dif_pos hi,dif_pos hk,dif_pos hk',dif_pos hi',
        exchange_eigenvalue,
        Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm,
        Equiv.swap_apply_of_ne_of_ne hil.symm hjl.symm,
        Equiv.swap_apply_of_ne_of_ne hik hil,
        Equiv.swap_apply_of_ne_of_ne hjk hjl,he]
      ring
    · have hk' := (exchangeable_other t i j k l hij hi hik hil hjk hjl).not.mpr hk
      simp only [tableauAction,dif_pos hi,dif_neg hk,dif_neg hk',
        exchange_eigenvalue,
        Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm,
        Equiv.swap_apply_of_ne_of_ne hil.symm hjl.symm]
      ring
  · by_cases hk : Exchangeable t k l
    · have hi' := (exchangeable_other t k l i j hkl hk hik.symm hjk.symm hil.symm hjl.symm).not.mpr hi
      simp only [tableauAction,dif_neg hi,dif_pos hk,dif_neg hi',
        exchange_eigenvalue,
        Equiv.swap_apply_of_ne_of_ne hik hil,
        Equiv.swap_apply_of_ne_of_ne hjk hjl]
      ring
    · simp only [tableauAction,dif_neg hi,dif_neg hk]
      ring

/-- The far-commutation relation in the actual standard-tableau finite
endomorphism algebra. -/
theorem tableauLinear_commute {F : Type*} [Field F] (v : F)
    {n : ℕ} {μ : Shape n} (i j k l : Fin n)
    (hij : j.val=i.val+1) (hkl : l.val=k.val+1)
    (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) :
    tableauLinear (μ:=μ) v i j hij*tableauLinear v k l hkl=
      tableauLinear v k l hkl*tableauLinear v i j hij := by
  apply LinearMap.ext
  intro f
  exact tableauAction_commute v i j k l hij hkl hik hil hjk hjl f

end
end Paper20.Seminormal

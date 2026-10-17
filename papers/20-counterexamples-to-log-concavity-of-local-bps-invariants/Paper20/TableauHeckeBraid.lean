import Paper20.TableauBraidBoundaryScalars

namespace Paper20.Seminormal
open Paper20.YoungShapes
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- The full adjacent braid relation on the actual finite standard Young
filling space. All configurations of comparable cells and forbidden
intermediate exchanges are included. -/
theorem tableauAction_braid {F : Type*} [Field F] (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d))
    {n : ℕ} {μ : Shape n} (i j k : Fin n)
    (hij : j.val=i.val+1) (hjk : k.val=j.val+1) (f : StandardFilling μ → F) :
    tableauAction v i j hij (tableauAction v j k hjk (tableauAction v i j hij f))=
      tableauAction v j k hjk (tableauAction v i j hij (tableauAction v j k hjk f)) := by
  funext t
  have hneij : i≠j := by intro h; have := congrArg Fin.val h; omega
  have hnejk : j≠k := by intro h; have := congrArg Fin.val h; omega
  have hneik : i≠k := by intro h; have := congrArg Fin.val h; omega
  have hct := filling_content_triple_ne t i j k hij hjk
  have hxy := eigenvalue_ne_of_content_ne v hp t i j hct.1
  have hyz := eigenvalue_ne_of_content_ne v hp t j k hct.2.1
  have hxz := eigenvalue_ne_of_content_ne v hp t i k hct.2.2
  have hsxy := diagonal_sum v (eigenvalue v t i) (eigenvalue v t j) hxy
  have hsyz := diagonal_sum v (eigenvalue v t j) (eigenvalue v t k) hyz
  have ht := diagonal_three v (eigenvalue v t i) (eigenvalue v t j) (eigenvalue v t k) hxy hyz hxz
  have hd := braid_diagonal v (eigenvalue v t i) (eigenvalue v t j) (eigenvalue v t k) hv hxy hyz hxz
  by_cases hi : Exchangeable t i j
  · have hix : Exchangeable (exchange t i j hij hi) i j := exchange_incomparable t i j hij hi
    have ha := exchange_exchange t i j hij hi
    by_cases hj : Exchangeable t j k
    · by_cases hac : Exchangeable t i k
      · exact tableauAction_braid_free v hv hp i j k hij hjk f t hi hj hac
      · have hjx : Exchangeable (exchange t j k hjk hj) j k := exchange_incomparable t j k hjk hj
        have hb := exchange_exchange t j k hjk hj
        have hu := (exchangeable_after_first t i j k hij hi hneik hnejk).not.mpr hac
        have hw := (exchangeable_after_second t i j k hjk hj hneij hneik).not.mpr hac
        simp only [tableauAction,dif_pos hi,dif_pos hj,dif_pos hix,dif_pos hjx,
          dif_neg hu,dif_neg hw,ha,hb,exchange_eigenvalue,
          Equiv.swap_apply_left,Equiv.swap_apply_right,
          Equiv.swap_apply_of_ne_of_ne hneik.symm hnejk.symm,
          Equiv.swap_apply_of_ne_of_ne hneij hneik]
        linear_combination (norm := ring_nf)
          f t*hd+
          f (exchange t i j hij hi)*offDiagonal v (eigenvalue v t i) (eigenvalue v t j)*
            (ht+diagonal v (eigenvalue v t i) (eigenvalue v t k)*hsxy)-
          f (exchange t j k hjk hj)*offDiagonal v (eigenvalue v t j) (eigenvalue v t k)*
            (ht+diagonal v (eigenvalue v t i) (eigenvalue v t k)*hsyz)
    · have hz := nonexchangeable_offDiagonal_product v hv hp t j k hjk hj
      simp only [hz,zero_mul,add_zero] at hd
      by_cases hac : Exchangeable t i k
      · have hu := (exchangeable_after_first t i j k hij hi hneik hnejk).mpr hac
        have huv := (exchangeable_after_first_second t i j k hij hjk hi hu hneij hneik hnejk).not.mpr hj
        simp only [tableauAction,dif_pos hi,dif_neg hj,dif_pos hix,dif_pos hu,
          dif_neg huv,ha,exchange_eigenvalue,Equiv.swap_apply_left,Equiv.swap_apply_right,
          Equiv.swap_apply_of_ne_of_ne hneik.symm hnejk.symm,
          Equiv.swap_apply_of_ne_of_ne hneij hneik]
        linear_combination (norm := ring_nf)
          f t*hd+f (exchange t i j hij hi)*offDiagonal v (eigenvalue v t i) (eigenvalue v t j)*
            (ht+diagonal v (eigenvalue v t i) (eigenvalue v t k)*hsxy)
      · have hu := (exchangeable_after_first t i j k hij hi hneik hnejk).not.mpr hac
        simp only [tableauAction,dif_pos hi,dif_neg hj,dif_pos hix,dif_neg hu,ha,
          exchange_eigenvalue,Equiv.swap_apply_left,Equiv.swap_apply_right,
          Equiv.swap_apply_of_ne_of_ne hneik.symm hnejk.symm,
          Equiv.swap_apply_of_ne_of_ne hneij hneik]
        linear_combination (norm := ring_nf)
          f t*hd+f (exchange t i j hij hi)*offDiagonal v (eigenvalue v t i) (eigenvalue v t j)*
            (ht+diagonal v (eigenvalue v t i) (eigenvalue v t k)*hsxy)
  · by_cases hj : Exchangeable t j k
    · have hjx : Exchangeable (exchange t j k hjk hj) j k := exchange_incomparable t j k hjk hj
      have hb := exchange_exchange t j k hjk hj
      have hz := nonexchangeable_offDiagonal_product v hv hp t i j hij hi
      simp only [hz,zero_mul,add_zero] at hd
      by_cases hac : Exchangeable t i k
      · have hw := (exchangeable_after_second t i j k hjk hj hneij hneik).mpr hac
        have hwu := (exchangeable_after_second_first t i j k hij hjk hj hw hneij hneik hnejk).not.mpr hi
        simp only [tableauAction,dif_neg hi,dif_pos hj,dif_pos hjx,dif_pos hw,
          dif_neg hwu,hb,exchange_eigenvalue,Equiv.swap_apply_left,Equiv.swap_apply_right,
          Equiv.swap_apply_of_ne_of_ne hneik.symm hnejk.symm,
          Equiv.swap_apply_of_ne_of_ne hneij hneik]
        linear_combination (norm := ring_nf)
          f t*hd-f (exchange t j k hjk hj)*offDiagonal v (eigenvalue v t j) (eigenvalue v t k)*
            (ht+diagonal v (eigenvalue v t i) (eigenvalue v t k)*hsyz)
      · have hw := (exchangeable_after_second t i j k hjk hj hneij hneik).not.mpr hac
        simp only [tableauAction,dif_neg hi,dif_pos hj,dif_pos hjx,dif_neg hw,hb,
          exchange_eigenvalue,Equiv.swap_apply_left,Equiv.swap_apply_right,
          Equiv.swap_apply_of_ne_of_ne hneik.symm hnejk.symm,
          Equiv.swap_apply_of_ne_of_ne hneij hneik]
        linear_combination (norm := ring_nf)
          f t*hd-f (exchange t j k hjk hj)*offDiagonal v (eigenvalue v t j) (eigenvalue v t k)*
            (ht+diagonal v (eigenvalue v t i) (eigenvalue v t k)*hsyz)
    · have he := chain_diagonal_equal v hv hp t i j k hij hjk hi hj
      simp only [tableauAction,dif_neg hi,dif_neg hj,add_zero]
      rw [he]

/-- The full braid relation in the actual finite endomorphism algebra of
the genuine standard-filling block. -/
theorem tableauLinear_braid {F : Type*} [Field F] (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d))
    {n : ℕ} {μ : Shape n} (i j k : Fin n)
    (hij : j.val=i.val+1) (hjk : k.val=j.val+1) :
    tableauLinear (μ:=μ) v i j hij*tableauLinear v j k hjk*tableauLinear v i j hij=
      tableauLinear v j k hjk*tableauLinear v i j hij*tableauLinear v j k hjk := by
  apply LinearMap.ext
  intro f
  exact tableauAction_braid v hv hp i j k hij hjk f

end
end Paper20.Seminormal

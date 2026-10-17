import Paper20.TableauHeckeCommute
import Paper20.StandardTripleExchange
import Paper20.YoungNearContents

namespace Paper20.Seminormal
open Paper20.YoungShapes
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

lemma eigenvalue_ne_of_content_ne {F : Type*} [Field F] (v : F)
    (hp : Function.Injective (fun d : ℤ => v^d))
    {n : ℕ} {μ : Shape n} (t : StandardFilling μ) (i j : Fin n)
    (hc : fillingContent t i≠fillingContent t j) : eigenvalue v t i≠eigenvalue v t j := by
  intro he
  have hz := hp he
  apply hc
  omega

/-- The full braid identity on an actual standard filling whose three
consecutive cells are pairwise incomparable. All six intermediate fillings
are genuine, and the equality is for every vector in the actual tableau
space. Boundary configurations are a separate remaining obligation. -/
theorem tableauAction_braid_free {F : Type*} [Field F] (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d))
    {n : ℕ} {μ : Shape n} (i j k : Fin n)
    (hij : j.val=i.val+1) (hjk : k.val=j.val+1)
    (f : StandardFilling μ → F) (t : StandardFilling μ)
    (hi : Exchangeable t i j) (hj : Exchangeable t j k) (hik : Exchangeable t i k) :
    tableauAction v i j hij (tableauAction v j k hjk (tableauAction v i j hij f)) t=
      tableauAction v j k hjk (tableauAction v i j hij (tableauAction v j k hjk f)) t := by
  have hneij : i≠j := by intro h; have := congrArg Fin.val h; omega
  have hnejk : j≠k := by intro h; have := congrArg Fin.val h; omega
  have hneik : i≠k := by intro h; have := congrArg Fin.val h; omega
  have hu := (exchangeable_after_first t i j k hij hi hneik hnejk).mpr hik
  have hw := (exchangeable_after_second t i j k hjk hj hneij hneik).mpr hik
  have huv := (exchangeable_after_first_second t i j k hij hjk hi hu hneij hneik hnejk).mpr hj
  have hwu := (exchangeable_after_second_first t i j k hij hjk hj hw hneij hneik hnejk).mpr hi
  have hix : Exchangeable (exchange t i j hij hi) i j := exchange_incomparable t i j hij hi
  have hjx : Exchangeable (exchange t j k hjk hj) j k := exchange_incomparable t j k hjk hj
  have ha := exchange_exchange t i j hij hi
  have hb := exchange_exchange t j k hjk hj
  have hc := exchange_braid t i j k hij hjk hi hj hu hw huv hwu
  simp only [tableauAction,dif_pos hi,dif_pos hj,dif_pos hu,dif_pos hw,
    dif_pos huv,dif_pos hwu,dif_pos hix,dif_pos hjx,ha,hb,hc,
    exchange_eigenvalue,Equiv.swap_apply_left,Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne hneik.symm hnejk.symm,
    Equiv.swap_apply_of_ne_of_ne hneij hneik]
  have hct := filling_content_triple_ne t i j k hij hjk
  have hxy := eigenvalue_ne_of_content_ne v hp t i j hct.1
  have hyz := eigenvalue_ne_of_content_ne v hp t j k hct.2.1
  have hxz := eigenvalue_ne_of_content_ne v hp t i k hct.2.2
  have hsxy := diagonal_sum v (eigenvalue v t i) (eigenvalue v t j) hxy
  have hsyz := diagonal_sum v (eigenvalue v t j) (eigenvalue v t k) hyz
  have ht := diagonal_three v (eigenvalue v t i) (eigenvalue v t j) (eigenvalue v t k) hxy hyz hxz
  have hd := braid_diagonal v (eigenvalue v t i) (eigenvalue v t j) (eigenvalue v t k) hv hxy hyz hxz
  linear_combination (norm := ring_nf)
    f t*hd+
    f (exchange t i j hij hi)*offDiagonal v (eigenvalue v t i) (eigenvalue v t j)*
      (ht+diagonal v (eigenvalue v t i) (eigenvalue v t k)*hsxy)-
    f (exchange t j k hjk hj)*offDiagonal v (eigenvalue v t j) (eigenvalue v t k)*
      (ht+diagonal v (eigenvalue v t i) (eigenvalue v t k)*hsyz)

end
end Paper20.Seminormal

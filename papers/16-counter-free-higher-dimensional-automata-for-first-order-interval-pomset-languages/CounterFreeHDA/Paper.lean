import CounterFreeHDA.Main
import CounterFreeHDA.LatticeExt

/-! Paper-facing proved declarations. See coverage.json for exact gaps.
No abstract language/HDA carrier, first-order=True definition, assumed
language equality, or assumed endpoint criterion is used here. -/

namespace CounterFreeHDA.Paper
universe u v w
open CounterFreeHDA.LowerSetAction

theorem lemma_2_2 {Obj : Type u} {C : FinCat Obj} (ord : C.IsOrdered)
    {S U V W : Obj} (I : Set (C.Hom S U))
    (hI : IsLowerSet (fun x y => ord.homLE x y) I)
    (P : C.Hom U V) (Q : C.Hom V W) :
    act ord I (C.id U) = I ∧
    act ord (act ord I P) Q = act ord I (C.comp P Q) ∧
    (∀ {ι : Type*} (f : ι → Set (C.Hom S U)),
        act ord (⋃ i, f i) P = ⋃ i, act ord (f i) P) ∧
    (∀ {P' Q' : C.Hom U V}, ord.homLE P' Q' → act ord I P' ⊆ act ord I Q') :=
  ⟨act_id ord hI, act_comp ord hI P Q,
    fun {_} f => act_iUnion (f := f) ord P,
    fun {_ _} h => act_mono_arrow ord I h⟩

end CounterFreeHDA.Paper

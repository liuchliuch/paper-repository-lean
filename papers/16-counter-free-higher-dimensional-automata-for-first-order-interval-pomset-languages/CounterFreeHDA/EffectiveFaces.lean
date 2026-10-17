import CounterFreeHDA.Size

namespace CounterFreeHDA.Cubical.Effective
universe u
variable {Lab : Type u} {k : ℕ} [DecidableEq Lab]

def ValidSub (U V : Cube Lab k) (s : Fin V.dim → Fin U.dim ⊕ Bool) : Prop :=
  (∀ i, ∃! j, s j = Sum.inl i) ∧
  (∀ a b i j, a < b → s a = Sum.inl i → s b = Sum.inl j → i < j) ∧
  (∀ j i, s j = Sum.inl i → V.lab j = U.lab i)

instance validSubDecidable (U V : Cube Lab k) (s : Fin V.dim → Fin U.dim ⊕ Bool) :
    Decidable (ValidSub U V s) := by
  unfold ValidSub ExistsUnique
  infer_instance

def faceEquiv (U V : Cube Lab k) : {s : Fin V.dim → Fin U.dim ⊕ Bool // ValidSub U V s} ≃ Face U V where
  toFun s := ⟨s.val,s.property.1,fun h hi hj => s.property.2.1 _ _ _ _ h hi hj,fun {_ _} h => s.property.2.2 _ _ h⟩
  invFun f := ⟨f.sub,⟨f.vars,fun _ _ _ _ h hi hj => f.ordered h hi hj,fun _ _ h => f.labels h⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exhaustive finite face enumeration by testing all substitutions; no
choice-based finite instance is used by the enumerator. -/
def faceFintype (U V : Cube Lab k) : Fintype (Face U V) := Fintype.ofEquiv _ (faceEquiv U V)

def faceDecidableEq (U V : Cube Lab k) : DecidableEq (Face U V) :=
  (show Function.Injective (Face.sub (U := U) (V := V)) from fun _ _ h => Face.ext h).decidableEq

def faceEnum (U V : Cube Lab k) : Finset (Face U V) := @Finset.univ _ (faceFintype U V)

theorem faceEnum_complete (U V : Cube Lab k) (f : Face U V) : f ∈ faceEnum U V := @Finset.mem_univ _ (faceFintype U V) f

end CounterFreeHDA.Cubical.Effective

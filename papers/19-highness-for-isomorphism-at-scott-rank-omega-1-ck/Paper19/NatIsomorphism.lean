import Paper19.NatModel

namespace Paper19

/-- Actual structure isomorphisms on Nat in the fixed finite signature. -/
structure NatIso (M N : NatModel) where
  map : ℕ ≃ ℕ
  index : ∀ x, N.index (map x) = M.index x
  zero : map M.zero = N.zero
  succ : ∀ x, map (M.succ x) = N.succ (map x)
  proj : ∀ x, map (M.proj x) = N.proj (map x)
  level : ∀ x, map (M.level x) = N.level (map x)
  rel : ∀ k x y, N.rel (map k,map x,map y) = M.rel (k,x,y)
  named : map M.named = N.named

namespace PresentationIso
variable {T : Tree} {a b : Bool}

noncomputable def toNatIso (f : PresentationIso T (namedRoot T a) (namedRoot T b)) :
    NatIso (natModel T a) (natModel T b) where
  map := ((carrierEquivNat T).symm.trans f.map).trans (carrierEquivNat T)
  index := by
    intro n
    obtain ⟨x,rfl⟩ := (carrierEquivNat T).surjective n
    apply Bool.eq_iff_iff.mpr
    simpa only [Equiv.trans_apply,Equiv.symm_apply_apply,natModel_index] using f.index x
  zero := by
    simp only [Equiv.trans_apply,natModel_zero,Equiv.symm_apply_apply]
    exact congrArg (carrierEquivNat T) f.zero
  succ := by
    intro n
    obtain ⟨x,rfl⟩ := (carrierEquivNat T).surjective n
    simpa only [Equiv.trans_apply,natModel_succ,Equiv.symm_apply_apply] using
      congrArg (carrierEquivNat T) (f.succ x)
  proj := by
    intro n
    obtain ⟨x,rfl⟩ := (carrierEquivNat T).surjective n
    simpa only [Equiv.trans_apply,natModel_proj,Equiv.symm_apply_apply] using
      congrArg (carrierEquivNat T) (f.proj x)
  level := by
    intro n
    obtain ⟨x,rfl⟩ := (carrierEquivNat T).surjective n
    simpa only [Equiv.trans_apply,natModel_level,Equiv.symm_apply_apply] using
      congrArg (carrierEquivNat T) (f.level x)
  rel := by
    intro k x y
    obtain ⟨k,rfl⟩ := (carrierEquivNat T).surjective k
    obtain ⟨x,rfl⟩ := (carrierEquivNat T).surjective x
    obtain ⟨y,rfl⟩ := (carrierEquivNat T).surjective y
    apply Bool.eq_iff_iff.mpr
    simpa only [Equiv.trans_apply,Equiv.symm_apply_apply,natModel_rel] using f.rel k x y
  named := by
    simp only [Equiv.trans_apply,natModel_named,Equiv.symm_apply_apply]
    exact congrArg (carrierEquivNat T) f.named

end PresentationIso

namespace NatIso
variable {T : Tree} {a b : Bool}

noncomputable def toCarrier (f : NatIso (natModel T a) (natModel T b)) :
    PresentationIso T (namedRoot T a) (namedRoot T b) where
  map := ((carrierEquivNat T).trans f.map).trans (carrierEquivNat T).symm
  index := by
    intro x
    rw [← natModel_index T b _,← natModel_index T a x]
    simpa only [Equiv.trans_apply,Equiv.apply_symm_apply] using
      Bool.eq_iff_iff.mp (f.index (carrierEquivNat T x))
  zero := by
    apply (carrierEquivNat T).injective
    simpa only [Equiv.trans_apply,Equiv.apply_symm_apply,← natModel_zero T a,← natModel_zero T b] using f.zero
  succ := by
    intro x
    apply (carrierEquivNat T).injective
    have h := f.succ (carrierEquivNat T x)
    simp only [natModel_succ] at h
    simpa only [Equiv.trans_apply,Equiv.apply_symm_apply,← natModel_succ T b] using h
  proj := by
    intro x
    apply (carrierEquivNat T).injective
    have h := f.proj (carrierEquivNat T x)
    simp only [natModel_proj] at h
    simpa only [Equiv.trans_apply,Equiv.apply_symm_apply,← natModel_proj T b] using h
  level := by
    intro x
    apply (carrierEquivNat T).injective
    have h := f.level (carrierEquivNat T x)
    simp only [natModel_level] at h
    simpa only [Equiv.trans_apply,Equiv.apply_symm_apply,← natModel_level T b] using h
  rel := by
    intro k x y
    rw [← natModel_rel T b,← natModel_rel T a]
    simpa only [Equiv.trans_apply,Equiv.apply_symm_apply] using
      Bool.eq_iff_iff.mp (f.rel (carrierEquivNat T k) (carrierEquivNat T x) (carrierEquivNat T y))
  named := by
    apply (carrierEquivNat T).injective
    simpa only [Equiv.trans_apply,Equiv.apply_symm_apply,← natModel_named T a,← natModel_named T b] using f.named

end NatIso
end Paper19

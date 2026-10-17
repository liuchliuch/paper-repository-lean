import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! Native homology classes and the exact boundary criterion for a short
complex of integer coefficient chain groups. This is the algebraic final
step of the prescribed filling argument after comparison isomorphisms. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open CategoryTheory
universe v

def concreteHomologyClass (S : ShortComplex AddCommGrpCat.{v}) (x : S.X₂) (hx : S.g x = 0) : S.homology :=
  S.abHomologyIso.inv (QuotientAddGroup.mk (⟨x,hx⟩ : AddMonoidHom.ker S.g.hom))

theorem concreteHomologyClass_eq_zero_iff (S : ShortComplex AddCommGrpCat.{v})
    (x : S.X₂) (hx : S.g x = 0) : concreteHomologyClass S x hx = 0 ↔ ∃ y : S.X₁, S.f y = x := by
  let z : AddMonoidHom.ker S.g.hom := ⟨x,hx⟩
  have hq : (QuotientAddGroup.mk z : (AddMonoidHom.ker S.g.hom) ⧸ AddMonoidHom.range S.abToCycles) = 0 ↔
      ∃ y : S.X₁, S.f y = x := by
    rw [QuotientAddGroup.eq_zero_iff,AddMonoidHom.mem_range]
    constructor
    · rintro ⟨y,hy⟩
      exact ⟨y,congrArg Subtype.val hy⟩
    · rintro ⟨y,hy⟩
      exact ⟨y,Subtype.ext hy⟩
  constructor
  · intro h
    apply hq.mp
    have hh := congrArg S.abHomologyIso.hom h
    simpa only [concreteHomologyClass,Iso.inv_hom_id_apply,map_zero] using hh
  · intro h
    have hz := hq.mpr h
    change S.abHomologyIso.inv (QuotientAddGroup.mk z) = 0
    rw [hz]
    exact map_zero _

theorem concreteHomologyClass_eq_π (S : ShortComplex AddCommGrpCat.{v})
    (x : S.X₂) (hx : S.g x = 0) : concreteHomologyClass S x hx =
      S.homologyπ (S.abCyclesIso.inv ⟨x,hx⟩) := by
  have h := congrArg (fun f : S.abLeftHomologyData.K ⟶ S.homology => f ⟨x,hx⟩)
    S.abLeftHomologyData.π_comp_homologyIso_inv
  exact h

theorem concreteHomologyClass_natural {S T : ShortComplex AddCommGrpCat.{v}}
    (φ : S ⟶ T) (x : S.X₂) (hx : S.g x = 0) :
    ShortComplex.homologyMap φ (concreteHomologyClass S x hx) =
      concreteHomologyClass T (φ.τ₂ x) (by
        have h := congrArg (fun f : S.X₂ ⟶ T.X₃ => f x) φ.comm₂₃
        simpa only [ConcreteCategory.comp_apply,hx,map_zero] using h) := by
  have hTx : T.g (φ.τ₂ x) = 0 := by
    have h := congrArg (fun f : S.X₂ ⟶ T.X₃ => f x) φ.comm₂₃
    simpa only [ConcreteCategory.comp_apply,hx,map_zero] using h
  have hCycles : ShortComplex.cyclesMap φ (S.abCyclesIso.inv ⟨x,hx⟩) =
      T.abCyclesIso.inv ⟨φ.τ₂ x,hTx⟩ := by
    apply (AddCommGrpCat.mono_iff_injective T.iCycles).mp inferInstance
    have h := congrArg (fun f : S.cycles ⟶ T.X₂ => f (S.abCyclesIso.inv ⟨x,hx⟩))
      (ShortComplex.cyclesMap_i φ)
    simp only [ConcreteCategory.comp_apply] at h
    rw [S.abCyclesIso_inv_apply_iCycles ⟨x,hx⟩] at h
    rw [T.abCyclesIso_inv_apply_iCycles ⟨φ.τ₂ x,hTx⟩]
    exact h
  rw [concreteHomologyClass_eq_π,concreteHomologyClass_eq_π]
  have h := congrArg (fun f : S.cycles ⟶ T.homology => f (S.abCyclesIso.inv ⟨x,hx⟩))
    (ShortComplex.homologyπ_naturality φ)
  simpa only [ConcreteCategory.comp_apply,hCycles] using h

theorem prescribed_filling_of_homology_injective {S T : ShortComplex AddCommGrpCat.{v}}
    (φ : S ⟶ T) (hInjective : Function.Injective (ShortComplex.homologyMap φ))
    (z : S.X₂) (hz : S.g z = 0) (hBounds : ∃ D : T.X₁, T.f D = φ.τ₂ z) :
    ∃ Q : S.X₁, S.f Q = z := by
  apply (concreteHomologyClass_eq_zero_iff S z hz).mp
  apply hInjective
  rw [map_zero,concreteHomologyClass_natural]
  exact (concreteHomologyClass_eq_zero_iff T _ _).mpr hBounds

end Paper28

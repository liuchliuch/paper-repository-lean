import Paper18.Category.RepresentationBasic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Module

/-! # The actual two eigenspaces of a complex order-two representation -/
noncomputable section
namespace Paper18.Category.RepresentationZ2
open CategoryTheory
abbrev H := Multiplicative (ZMod 2)
def generator : H := Multiplicative.ofAdd 1
@[simp] theorem generator_sq : generator * generator = 1 := by decide

theorem generator_involution (V : FDRep ℂ H) (v : V) :
    V.ρ generator (V.ρ generator v) = v := by
  have h := congrArg (fun f : V →ₗ[ℂ] V => f v) ((V.ρ).map_mul generator generator)
  simpa only [generator_sq, map_one, Module.End.one_apply, Module.End.mul_apply] using h.symm

def plusSpace (V : FDRep ℂ H) : Submodule ℂ V where
  carrier := {v | V.ρ generator v = v}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    dsimp only [Set.mem_setOf_eq] at hv hw
    change V.ρ generator (v+w) = v+w
    simp only [map_add, hv, hw]
  smul_mem' := by
    intro r v hv
    dsimp only [Set.mem_setOf_eq] at hv
    change V.ρ generator (r • v) = r • v
    simp only [map_smul, hv]

def minusSpace (V : FDRep ℂ H) : Submodule ℂ V where
  carrier := {v | V.ρ generator v = -v}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    dsimp only [Set.mem_setOf_eq] at hv hw
    change V.ρ generator (v+w) = -(v+w)
    simp only [map_add, hv, hw, neg_add]
  smul_mem' := by
    intro r v hv
    dsimp only [Set.mem_setOf_eq] at hv
    change V.ρ generator (r • v) = -(r • v)
    simp only [map_smul, hv, smul_neg]

@[simp] theorem plusSpace_generator (V : FDRep ℂ H) (v : plusSpace V) :
    V.ρ generator v.val = v.val := v.property
@[simp] theorem minusSpace_generator (V : FDRep ℂ H) (v : minusSpace V) :
    V.ρ generator v.val = -v.val := v.property

def plusProjection (V : FDRep ℂ H) : V →ₗ[ℂ] plusSpace V where
  toFun v := ⟨(1/2 : ℂ) • (v + V.ρ generator v), by
    change V.ρ generator ((1/2 : ℂ) • (v + V.ρ generator v)) = _
    simp only [map_smul, map_add, generator_involution]
    rw [add_comm]⟩
  map_add' v w := by apply Subtype.ext; simp only [Submodule.coe_add, map_add, smul_add]; abel
  map_smul' r v := by apply Subtype.ext; simp only [Submodule.coe_smul, RingHom.id_apply, map_smul, smul_add, smul_smul]; ring_nf

def minusProjection (V : FDRep ℂ H) : V →ₗ[ℂ] minusSpace V where
  toFun v := ⟨(1/2 : ℂ) • (v - V.ρ generator v), by
    change V.ρ generator ((1/2 : ℂ) • (v - V.ρ generator v)) = _
    simp only [map_smul, map_sub, generator_involution]
    module⟩
  map_add' v w := by apply Subtype.ext; simp only [Submodule.coe_add, map_add, smul_sub, smul_add]; abel
  map_smul' r v := by apply Subtype.ext; simp only [Submodule.coe_smul, RingHom.id_apply, map_smul, smul_sub, smul_smul]; ring_nf

def eigenspaceEquiv (V : FDRep ℂ H) : (plusSpace V × minusSpace V) ≃ₗ[ℂ] V where
  toFun p := p.1.val + p.2.val
  invFun v := (plusProjection V v, minusProjection V v)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change (1/2 : ℂ) • (p.1.val + p.2.val + V.ρ generator (p.1.val + p.2.val)) = _
      simp only [map_add, plusSpace_generator, minusSpace_generator]
      module
    · apply Subtype.ext
      change (1/2 : ℂ) • (p.1.val + p.2.val - V.ρ generator (p.1.val + p.2.val)) = _
      simp only [map_add, plusSpace_generator, minusSpace_generator]
      module
  right_inv v := by
    change (1/2 : ℂ) • (v + V.ρ generator v) + (1/2 : ℂ) • (v - V.ρ generator v) = v
    module
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]; abel
  map_smul' r p := by simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_add, RingHom.id_apply]

theorem eigenspaceEquiv_generator (V : FDRep ℂ H) (p : plusSpace V × minusSpace V) :
    V.ρ generator (eigenspaceEquiv V p) = eigenspaceEquiv V (p.1, -p.2) := by
  change V.ρ generator (p.1.val + p.2.val) = p.1.val + (-p.2).val
  simp only [map_add, plusSpace_generator, minusSpace_generator, Submodule.coe_neg]

end Paper18.Category.RepresentationZ2

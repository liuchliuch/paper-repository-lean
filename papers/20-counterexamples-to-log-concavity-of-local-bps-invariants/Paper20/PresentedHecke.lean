import Mathlib

namespace Paper20.PresentedHecke
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- The actual type-A Hecke presentation, imposed on the free associative
algebra by the three defining relation families. -/
inductive Relations (R : Type*) [CommRing R] (n : ℕ) (z : R) :
    FreeAlgebra R (Fin (n-1)) → FreeAlgebra R (Fin (n-1)) → Prop
  | quadratic (i : Fin (n-1)) : Relations R n z
      (FreeAlgebra.ι R i*FreeAlgebra.ι R i)
      (algebraMap R _ z*FreeAlgebra.ι R i+1)
  | braid (i j : Fin (n-1)) (h : j.val=i.val+1) : Relations R n z
      (FreeAlgebra.ι R i*FreeAlgebra.ι R j*FreeAlgebra.ι R i)
      (FreeAlgebra.ι R j*FreeAlgebra.ι R i*FreeAlgebra.ι R j)
  | far (i j : Fin (n-1)) (h : i.val+1 < j.val ∨ j.val+1 < i.val) : Relations R n z
      (FreeAlgebra.ι R i*FreeAlgebra.ι R j) (FreeAlgebra.ι R j*FreeAlgebra.ι R i)

/-- The honest quotient by the stated relations, without additional
identifications, dimension assumptions or character axioms. -/
abbrev Presented (R : Type*) [CommRing R] (n : ℕ) (z : R) := RingQuot (Relations R n z)

section Ring
variable (R : Type*) [CommRing R] (n : ℕ) (z : R)

def generator (i : Fin (n-1)) : Presented R n z :=
  RingQuot.mkAlgHom R (Relations R n z) (FreeAlgebra.ι R i)

theorem generator_quadratic (i : Fin (n-1)) :
    generator R n z i^2=z • generator R n z i+1 := by
  have he := RingQuot.mkAlgHom_rel R (Relations.quadratic (R:=R) (n:=n) (z:=z) i)
  simpa only [map_mul,map_add,map_one,AlgHom.commutes,generator,Algebra.smul_def,pow_two] using he

theorem generator_braid (i j : Fin (n-1)) (h : j.val=i.val+1) :
    generator R n z i*generator R n z j*generator R n z i=
      generator R n z j*generator R n z i*generator R n z j := by
  have he := RingQuot.mkAlgHom_rel R (Relations.braid (R:=R) (n:=n) (z:=z) i j h)
  simpa only [map_mul,generator] using he

theorem generator_commute (i j : Fin (n-1)) (h : i.val+1 < j.val ∨ j.val+1 < i.val) :
    generator R n z i*generator R n z j=generator R n z j*generator R n z i := by
  have he := RingQuot.mkAlgHom_rel R (Relations.far (R:=R) (n:=n) (z:=z) i j h)
  simpa only [map_mul,generator] using he

variable {A : Type*} [Ring A] [Algebra R A]

/-- The universal property of the genuine presentation: any actual
family satisfying all three Hecke relations gives an algebra homomorphism. -/
def lift (f : Fin (n-1) → A)
    (hq : ∀ i, f i^2=z • f i+1)
    (hb : ∀ i j, j.val=i.val+1 → f i*f j*f i=f j*f i*f j)
    (hf : ∀ i j, i.val+1 < j.val ∨ j.val+1 < i.val → f i*f j=f j*f i) :
    Presented R n z →ₐ[R] A :=
  RingQuot.liftAlgHom R ⟨FreeAlgebra.lift R f,by
    intro x y h
    cases h with
    | quadratic i =>
      simpa only [map_mul,map_add,map_one,AlgHom.commutes,FreeAlgebra.lift_ι_apply,
        Algebra.smul_def,pow_two] using hq i
    | braid i j hij =>
      simpa only [map_mul,FreeAlgebra.lift_ι_apply] using hb i j hij
    | far i j hij =>
      simpa only [map_mul,FreeAlgebra.lift_ι_apply] using hf i j hij⟩

@[simp] theorem lift_generator (f : Fin (n-1) → A)
    (hq : ∀ i, f i^2=z • f i+1)
    (hb : ∀ i j, j.val=i.val+1 → f i*f j*f i=f j*f i*f j)
    (hf : ∀ i j, i.val+1 < j.val ∨ j.val+1 < i.val → f i*f j=f j*f i) (i : Fin (n-1)) :
    lift R n z f hq hb hf (generator R n z i)=f i := by
  rw [lift,generator,RingQuot.liftAlgHom_mkAlgHom_apply,FreeAlgebra.lift_ι_apply]

end Ring
end
end Paper20.PresentedHecke

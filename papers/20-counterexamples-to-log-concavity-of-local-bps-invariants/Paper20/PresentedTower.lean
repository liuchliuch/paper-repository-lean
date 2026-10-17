import Paper20.PresentedHecke
import Paper20.HeckeTailProducts

namespace Paper20.PresentedHecke
open Paper20.HeckeNormalForm
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

section Ring
variable (R : Type*) [CommRing R] (n : ℕ) (z : R)

/-- The actual inclusion of the smaller Hecke presentation into the next
one; injectivity is not assumed in constructing this homomorphism. -/
def inclusion : Presented R n z →ₐ[R] Presented R (n+1) z :=
  lift R n z (fun i => generator R (n+1) z ⟨i.val,by omega⟩)
    (by intro i; exact generator_quadratic R (n+1) z _)
    (by intro i j h; exact generator_braid R (n+1) z _ _ h)
    (by intro i j h; exact generator_commute R (n+1) z _ _ h)

@[simp] theorem inclusion_generator (i : Fin (n-1)) :
    inclusion R n z (generator R n z i)=generator R (n+1) z ⟨i.val,by omega⟩ :=
  lift_generator _ _ _ _ _ _ _ i

/-- Induction on the actual quotient, obtained from the honest free
algebra and the surjective quotient map. -/
theorem induction_on {P : Presented R n z → Prop}
    (scalar : ∀ r : R, P (algebraMap R _ r)) (gen : ∀ i, P (generator R n z i))
    (mul : ∀ a b, P a → P b → P (a*b)) (add : ∀ a b, P a → P b → P (a+b))
    (x : Presented R n z) : P x := by
  obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective (A:=FreeAlgebra R (Fin (n-1))) (S:=R) (Relations R n z) x
  induction a using FreeAlgebra.induction with
  | grade0 r => simpa only [AlgHom.commutes] using scalar r
  | grade1 i => exact gen i
  | mul a b ha hb => simpa only [map_mul] using mul _ _ ha hb
  | add a b ha hb => simpa only [map_add] using add _ _ ha hb

end Ring

/-- Factorial many genuine tower normal-word indices. -/
def Code : ℕ → Type
  | 0 => PUnit
  | n+1 => Fin (n+1) × Code n

instance codeFintype : ∀ n, Fintype (Code n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n+1 => by
    letI := codeFintype n
    change Fintype (Fin (n+1) × Code n)
    infer_instance

theorem code_card (n : ℕ) : Fintype.card (Code n)=n.factorial := by
  induction n with
  | zero => change Fintype.card PUnit=Nat.factorial 0; simp
  | succ n ih =>
    change Fintype.card (Fin (n+1) × Code n)=_
    rw [Fintype.card_prod,Fintype.card_fin,ih,Nat.factorial_succ]

section Ring
variable (R : Type*) [CommRing R] (z : R)

/-- An actual tower normal word, a coset tail followed by an included
smaller normal word. This is a concrete product in the honest quotient. -/
def normalWord : (n : ℕ) → Code n → Presented R n z
  | 0,_ => 1
  | n+1,c => tailProduct (generator R (n+1) z) c.1.val*
      inclusion R n z (normalWord n c.2)

def normalSpan (n : ℕ) : Submodule R (Presented R n z) :=
  Submodule.span R (Set.range (normalWord R z n))

theorem normalWord_mem (n : ℕ) (c : Code n) : normalWord R z n c ∈ normalSpan R z n :=
  Submodule.subset_span (Set.mem_range_self c)

def identityCode : (n : ℕ) → Code n
  | 0 => PUnit.unit
  | n+1 => ⟨Fin.last n,identityCode n⟩

theorem normalWord_identity (n : ℕ) : normalWord R z n (identityCode n)=1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change tailProduct (generator R (n+1) z) n*inclusion R n z (normalWord R z n (identityCode n))=1
    rw [tail_ge _ n le_rfl,ih,map_one,one_mul]

theorem normalSpan_one (n : ℕ) : (1:Presented R n z) ∈ normalSpan R z n := by
  rw [← normalWord_identity R z n]
  exact normalWord_mem R z n _

/-- Once lower-rank words span, every actual included lower-rank element
following a fixed coset tail belongs to the higher normal-word span. -/
theorem tail_lower_mem (n : ℕ) (hspan : normalSpan R z n=⊤) (j : Fin (n+1))
    (a : Presented R n z) :
    tailProduct (generator R (n+1) z) j.val*inclusion R n z a ∈ normalSpan R z (n+1) := by
  have ha : a ∈ Submodule.span R (Set.range (normalWord R z n)) := by
    change a ∈ normalSpan R z n
    rw [hspan]
    trivial
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c,rfl⟩ := hx
    exact normalWord_mem R z (n+1) (j,c)
  | zero => rw [map_zero,mul_zero]; exact (normalSpan R z (n+1)).zero_mem
  | add a b ha hb ia ib =>
    rw [map_add,mul_add]
    exact (normalSpan R z (n+1)).add_mem ia ib
  | smul c a ha ia =>
    rw [map_smul,mul_smul_comm]
    exact (normalSpan R z (n+1)).smul_mem c ia

end Ring
end
end Paper20.PresentedHecke

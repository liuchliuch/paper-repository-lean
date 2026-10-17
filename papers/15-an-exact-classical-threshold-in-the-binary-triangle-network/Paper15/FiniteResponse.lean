import Paper15.FiniteLaws

noncomputable section
namespace Paper15
open Finset BigOperators

def momentAt (a b c : ℝ) (u : Fin 3) : ℝ :=
  if u=0 then (a+b+c)/3 else if u=1 then (a*b+b*c+c*a)/3 else a*b*c

structure FiniteResponse (α β γ : Type*) where
  A : β → γ → ℝ
  B : γ → α → ℝ
  C : α → β → ℝ
  A_mem : ∀y z, A y z ∈ Set.Icc (-1:ℝ) 1
  B_mem : ∀z x, B z x ∈ Set.Icc (-1:ℝ) 1
  C_mem : ∀x y, C x y ∈ Set.Icc (-1:ℝ) 1

namespace FiniteResponse
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def moments (F : FiniteResponse α β γ) (qx : Law α) (qy : Law β) (qz : Law γ)
    (u : Fin 3) : ℝ :=
  qx.avg (fun x => qy.avg (fun y => qz.avg (fun z => momentAt (F.A y z) (F.B z x) (F.C x y) u)))

def Deterministic (F : FiniteResponse α β γ) : Prop :=
  (∀y z, legalSign (F.A y z)) ∧ (∀z x, legalSign (F.B z x)) ∧ (∀x y, legalSign (F.C x y))

def seedLaw {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (hf : ∀i, f i ∈ Set.Icc (-1:ℝ) 1) :
    Law (ι → Bool) := Law.pi (fun i => Law.binary (f i) (hf i))

lemma seedLaw_avg {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (hf : ∀i, f i ∈ Set.Icc (-1:ℝ) 1) (i : ι) :
    (seedLaw f hf).avg (fun s => Law.boolSign (s i)) = f i := by
  exact (Law.avg_pi_coordinate (fun j => Law.binary (f j) (hf j)) i Law.boolSign).trans (Law.binary_avg _ _)

lemma avg_moment_a {ι : Type*} [Fintype ι] (q : Law ι) (a : ι → ℝ) (b : ℝ) (c : ℝ) (u : Fin 3) :
    q.avg (fun i => momentAt (a i) b c u) = momentAt (q.avg a) b c u := by
  fin_cases u
  · change q.avg (fun i => _) = _
    calc
      _ = q.avg (fun i => (1/3) * a i + ((b+c)/3)) := by
        congr 1; funext i; simp [momentAt] <;> ring
      _ = (1/3) * q.avg a + ((b+c)/3) := by
        rw [Law.avg_add,Law.avg_mul,Law.avg_const]
      _ = _ := by simp [momentAt] <;> ring
  · change q.avg (fun i => _) = _
    calc
      _ = q.avg (fun i => ((b+c)/3) * a i + (b*c/3)) := by
        congr 1; funext i; simp [momentAt] <;> ring
      _ = ((b+c)/3) * q.avg a + (b*c/3) := by
        rw [Law.avg_add,Law.avg_mul,Law.avg_const]
      _ = _ := by simp [momentAt] <;> ring
  · change q.avg (fun i => _) = _
    calc
      _ = q.avg (fun i => (b*c) * a i + 0) := by
        congr 1; funext i; simp [momentAt] <;> ring
      _ = (b*c) * q.avg a + 0 := by
        rw [Law.avg_add,Law.avg_mul,Law.avg_const]
      _ = _ := by simp [momentAt] <;> ring
lemma avg_moment_b {ι : Type*} [Fintype ι] (q : Law ι) (b : ι → ℝ) (a : ℝ) (c : ℝ) (u : Fin 3) :
    q.avg (fun i => momentAt a (b i) c u) = momentAt a (q.avg b) c u := by
  fin_cases u
  · change q.avg (fun i => _) = _
    calc
      _ = q.avg (fun i => (1/3) * b i + ((a+c)/3)) := by
        congr 1; funext i; simp [momentAt] <;> ring
      _ = (1/3) * q.avg b + ((a+c)/3) := by
        rw [Law.avg_add,Law.avg_mul,Law.avg_const]
      _ = _ := by simp [momentAt] <;> ring
  · change q.avg (fun i => _) = _
    calc
      _ = q.avg (fun i => ((a+c)/3) * b i + (a*c/3)) := by
        congr 1; funext i; simp [momentAt] <;> ring
      _ = ((a+c)/3) * q.avg b + (a*c/3) := by
        rw [Law.avg_add,Law.avg_mul,Law.avg_const]
      _ = _ := by simp [momentAt] <;> ring
  · change q.avg (fun i => _) = _
    calc
      _ = q.avg (fun i => (a*c) * b i + 0) := by
        congr 1; funext i; simp [momentAt] <;> ring
      _ = (a*c) * q.avg b + 0 := by
        rw [Law.avg_add,Law.avg_mul,Law.avg_const]
      _ = _ := by simp [momentAt] <;> ring
lemma avg_moment_c {ι : Type*} [Fintype ι] (q : Law ι) (c : ι → ℝ) (a : ℝ) (b : ℝ) (u : Fin 3) :
    q.avg (fun i => momentAt a b (c i) u) = momentAt a b (q.avg c) u := by
  fin_cases u
  · change q.avg (fun i => _) = _
    calc
      _ = q.avg (fun i => (1/3) * c i + ((a+b)/3)) := by
        congr 1; funext i; simp [momentAt] <;> ring
      _ = (1/3) * q.avg c + ((a+b)/3) := by
        rw [Law.avg_add,Law.avg_mul,Law.avg_const]
      _ = _ := by simp [momentAt] <;> ring
  · change q.avg (fun i => _) = _
    calc
      _ = q.avg (fun i => ((a+b)/3) * c i + (a*b/3)) := by
        congr 1; funext i; simp [momentAt] <;> ring
      _ = ((a+b)/3) * q.avg c + (a*b/3) := by
        rw [Law.avg_add,Law.avg_mul,Law.avg_const]
      _ = _ := by simp [momentAt] <;> ring
  · change q.avg (fun i => _) = _
    calc
      _ = q.avg (fun i => (a*b) * c i + 0) := by
        congr 1; funext i; simp [momentAt] <;> ring
      _ = (a*b) * q.avg c + 0 := by
        rw [Law.avg_add,Law.avg_mul,Law.avg_const]
      _ = _ := by simp [momentAt] <;> ring

/-- Put an independent table of private binary response coins into one of
 each party's incident sources. The other recipient ignores that table. -/
def deterministicLift (F : FiniteResponse α β γ) :
    FiniteResponse (α × (γ × α → Bool)) (β × (α × β → Bool)) (γ × (β × γ → Bool)) where
  A y z := Law.boolSign (z.2 (y.1,z.1))
  B z x := Law.boolSign (x.2 (z.1,x.1))
  C x y := Law.boolSign (y.2 (x.1,y.1))
  A_mem y z := by rcases Law.boolSign_legal (z.2 (y.1,z.1)) with h|h <;> rw [h] <;> constructor <;> norm_num
  B_mem z x := by rcases Law.boolSign_legal (x.2 (z.1,x.1)) with h|h <;> rw [h] <;> constructor <;> norm_num
  C_mem x y := by rcases Law.boolSign_legal (y.2 (x.1,y.1)) with h|h <;> rw [h] <;> constructor <;> norm_num

lemma deterministicLift_legal (F : FiniteResponse α β γ) : F.deterministicLift.Deterministic :=
  ⟨fun _ _ => Law.boolSign_legal _,fun _ _ => Law.boolSign_legal _,fun _ _ => Law.boolSign_legal _⟩

set_option maxHeartbeats 0 in
lemma deterministicLift_moments (F : FiniteResponse α β γ)
    (qx : Law α) (qy : Law β) (qz : Law γ) :
    let sa := seedLaw (Function.uncurry F.A) (fun p => F.A_mem p.1 p.2)
    let sb := seedLaw (Function.uncurry F.B) (fun p => F.B_mem p.1 p.2)
    let sc := seedLaw (Function.uncurry F.C) (fun p => F.C_mem p.1 p.2)
    ∀ u, F.deterministicLift.moments (qx.prod sb) (qy.prod sc) (qz.prod sa) u = F.moments qx qy qz u := by
  classical
  intro sa sb sc u
  simp only [moments,Law.avg_prod,deterministicLift]
  simp_rw [Law.avg_comm sb qy,Law.avg_comm sc qz,Law.avg_comm sb qz]
  dsimp [sa,sb,sc]
  simp only [avg_moment_a,seedLaw_avg,avg_moment_c,avg_moment_b]
  rfl

end FiniteResponse
end Paper15

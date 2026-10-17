import Paper19.UniformCoding
import Paper19.PathIso

namespace Paper19
open UniformOracleComputable
open scoped symmDiff

def groupOracle {T : Tree} (c : CoherentIso T) : Stream := fun n =>
  @Encodable.encode (Finset Node) (Primcodable.toEncodable) (c.h n)

def walkProgram (o : Stream) : ℕ → Node
  | 0 => []
  | n+1 => FiniteCoding.childPick (n,Denumerable.ofNat (Finset Node) (o (n+1)),walkProgram o n)

theorem walk_uniform : UniformOracleComputable walkProgram := by
  have hi : UniformOracleComputable (fun _ (p : ℕ × (ℕ × Node)) => p.2.1) := fst.comp snd
  have hv : UniformOracleComputable (fun o (p : ℕ × (ℕ × Node)) =>
      Denumerable.ofNat (Finset Node) (o (p.2.1+1))) :=
    (base (Primrec.ofNat (Finset Node)).to_comp).comp (query.comp ((base Computable.succ).comp hi))
  have hc := (base FiniteCoding.childPick_primrec.to_comp).comp
    (hi.pair (hv.pair (snd.comp snd)))
  have hh := UniformOracleComputable.nat_rec
    (id : UniformOracleComputable (fun _ => @id ℕ)) (const ([] : Node)) hc
  apply hh.of_eq
  intro o n
  induction n with
  | zero => rfl
  | succ n ih =>
    change FiniteCoding.childPick (n,_,Nat.rec (motive := fun _ => Node) []
      (fun i σ => FiniteCoding.childPick (i,Denumerable.ofNat (Finset Node) (o (i+1)),σ)) n) = _
    change Nat.rec (motive := fun _ => Node) []
      (fun i σ => FiniteCoding.childPick (i,Denumerable.ofNat (Finset Node) (o (i+1)),σ)) n = _ at ih
    rw [ih]
    rfl

theorem walkProgram_correct {T : Tree} (c : CoherentIso T) (n : ℕ) :
    walkProgram (groupOracle c) n = nodeSeq c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [walkProgram, groupOracle, Denumerable.ofNat_encode, ih, nodeSeq, leastChild]

def liftPathProgram (o : Stream) (i : ℕ) : ℕ := (walkProgram o (i+1)).getD i 0

theorem liftPath_uniform : UniformOracleComputable liftPathProgram :=
  (base (Primrec.list_getD 0).to_comp).comp
    ((walk_uniform.comp (base Computable.succ)).pair id)

theorem liftPathProgram_correct {T : Tree} (c : CoherentIso T)
    (hG : ∀ n, GMem T n (c.h n)) :
    liftPathProgram (groupOracle c) = pathOfCoherent c hG := by
  funext i
  simp [liftPathProgram, walkProgram_correct, pathOfCoherent]

/-- Uniformly compute the coherent singleton translations from a T-path. -/
def singletonProgram (o : Stream) (n : ℕ) : ℕ :=
  @Encodable.encode (Finset Node) (Primcodable.toEncodable)
    ({List.ofFn (fun i : Fin n => pairStream (binaryOf o) (decodeBoundOf o) i)} : Finset Node)

theorem singleton_uniform : UniformOracleComputable singletonProgram := by
  have hc : Computable (fun σ : Node => @Encodable.encode (Finset Node) (Primcodable.toEncodable)
      ({σ} : Finset Node)) := Primrec.encode.to_comp.comp FiniteCoding.singleton_computable
  exact (base hc).comp (prefix_uniform.substitute pathCode_uniform)

/-- A coherent translation is applied to any vector by this fixed program. -/
def translateProgram (o : Stream) (p : ℕ × Finset Node) : Finset Node :=
  p.2 ∆ Denumerable.ofNat (Finset Node) (o p.1)

def translateCode (o : Stream) (p : ℕ × ℕ) : ℕ :=
  FiniteCoding.symmDiffCodes (p.2,o p.1)

theorem translate_uniform : UniformOracleComputable translateCode :=
  (base FiniteCoding.symmDiffCodes_computable).comp (snd.pair (query.comp fst))

def originalPathProgram (o : Stream) : Stream :=
  pathOfQT (streamBits (liftPathProgram o)) (streamBounds (liftPathProgram o))

theorem originalPath_uniform : UniformOracleComputable originalPathProgram :=
  pathDecode_uniform.substitute liftPath_uniform

end Paper19

import Paper19.Reduction
import Paper19.EffectiveSyntax
import Paper19.Highness
import Paper19.OrdinalBound
import Paper19.FullTheorem
import Paper19.UniformLemma5
import Paper19.UniformNormalForm

/-! Independently readable contracts. All objects are the genuine carrier,
finite-language isomorphisms, ordinal ranks, and explicit infinitary syntax.
No highness claim is replaced by pointwise domination or a tautology. -/
namespace Paper19.Spec
open Paper19 Paper19.Infinitary
open scoped symmDiff

def Lemma2_PathConversions : Prop :=
  ∀ T : Tree,
    (∀ f, T.IsPath f → (STree T).IsPath (pairStream (binaryOf f) (decodeBoundOf f))) ∧
    (∀ g, (STree T).IsPath g → T.IsPath (pathOfQT (streamBits g) (streamBounds g)))

def Lemma2_NormalForm : Prop :=
  ∀ T : Tree, ComputablePred T.mem → ComputablePred (STree T).mem ∧
    ∀ n, PrimrecPred (fun σ : Node => σ ∈ extLevel (STree T) n)

def Lemma2_UrhoBasis : Prop :=
  ∀ (T : Tree) (n : ℕ) (ρ : BinVec n),
    ∃ M : Finset (BoundVec n), ∀ u, u ∈ Urho T ρ ↔ ∃ v ∈ M, ∀ j, v j ≤ u j

def Lemma3_RankBound : Prop :=
  ∀ T : Tree, ComputablePred T.mem → ∀ n,
    ∃ w : RecursiveWellOrder, ∀ σ ∈ deadLevel (STree T) n,
      ∀ hs : Acc (fun τ σ => SChild T σ τ) σ, hs.rank < w.val

def Lemma4_IsoChar : Prop :=
  ∀ (T : Tree) (f : PresentationIso T (Carrier.zeroVec 0) Carrier.rootOne),
    ∃ c : ValidIso T, ∀ x, f.map x = Carrier.translate c.val.h c.property x

def Lemma4_IsoConverse : Prop :=
  ∀ (T : Tree) (c : ValidIso T),
    ∃ f : PresentationIso T (Carrier.zeroVec 0) Carrier.rootOne,
      ∀ x, f.map x = Carrier.translate c.val.h c.property x

def Lemma4_AutChar : Prop :=
  ∀ (T : Tree) (tag : Bool) (f : PresentationIso T (namedRoot T tag) (namedRoot T tag)),
    ∃ c : ValidAut T, ∀ x, f.map x = Carrier.translate c.val.h c.property x

def Lemma4_AutConverse : Prop :=
  ∀ (T : Tree) (tag : Bool) (c : ValidAut T),
    ∃ f : PresentationIso T (namedRoot T tag) (namedRoot T tag),
      ∀ x, f.map x = Carrier.translate c.val.h c.property x

def Lemma4_HomProj : Prop :=
  ∀ (T : Tree) (n : ℕ) (F G : Finset Node), LenN1 n F → LenN1 n G →
    proj T n (F ∆ G) = proj T n F ∆ proj T n G

def Lemma5_PathToIso : Prop :=
  ∀ (T : Tree) (f : Stream), (STree T).IsPath f →
    Nonempty (PresentationIso T (Carrier.zeroVec 0) Carrier.rootOne)

def Lemma5_IsoToPath : Prop :=
  ∀ (T : Tree) (f : PresentationIso T (Carrier.zeroVec 0) Carrier.rootOne),
    (STree T).IsPath (pathOfCoherent f.toValidIso.val f.toValidIso.property)

def Lemma6_InfiniteLift : Prop :=
  ∀ (T : Tree) (n : ℕ) (F : Finset Node),
    (∀ σ ∈ F, σ ∈ extLevel (STree T) n) ↔ HasInfiniteLiftG (Dom.vec n F : Dom T)

def Lemma6_DeadRank : Prop :=
  ∀ (T : Tree) (n : ℕ) (F : Finset Node) (σ : Node), GMem T n F →
    σ ∈ F → ¬(STree T).IsExtendible σ →
    ∃ (hs : Acc (fun τ σ => SChild T σ τ) σ)
      (hF : Acc (fun y x : Dom T => IsChildG x y) (.vec n F)), hF.rank ≤ hs.rank

def Thm1_Isomorphic : Prop :=
  ∀ T : Tree, Nonempty (PresentationIso T (Carrier.zeroVec 0) Carrier.rootOne) ↔
    ∃ f, T.IsPath f

def Thm1_OrbitDefinitions : Prop :=
  ∀ T : Tree, ComputablePred T.mem → ∀ tag m (a : Fin m → Carrier T),
    ∃ φ : Formula, ComputablyPresented φ ∧ ∀ b : Fin m → Carrier T,
      φ.Realize tag (tupleEnv b) ↔ ActualTupleOrbit T tag a b

/-- Correctness of the two explicit executable programs. Machine-index
uniformity is a separate certification obligation, not inferred from this
proposition's quantifier order. -/
def Thm1_ProgramsCorrect : Prop :=
  ∀ T : Tree, ∀ f : PresentationIso T (Carrier.zeroVec 0) Carrier.rootOne,
    T.IsPath (presentationToPath f)

/-- The substantive injection-path argument in S5.p3. -/
def Cor7_InjectionTree : Prop :=
  ∀ (L : Highness.Lang) (C D : Highness.Pres L),
    Nonempty (Highness.InjPath C D) ↔ Nonempty (Highness.Iso C.toStruct D.toStruct)

end Paper19.Spec

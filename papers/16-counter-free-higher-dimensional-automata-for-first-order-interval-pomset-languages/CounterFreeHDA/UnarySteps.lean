import CounterFreeHDA.ResidualSubsetTable

namespace CounterFreeHDA.Appendix.Unary
open Cubical
abbrev zero := Completion.emptyCube
abbrev one := Completion.oneCube
def two : Cube Unit 2 := ⟨2,fun _ => ()⟩

def face1 (b : Bool) : Cubical.Face one two where
  sub j := if j.val = 0 then .inl (0 : Fin 1) else .inr b
  vars := by cases b <;> unfold ExistsUnique <;> decide
  ordered := by cases b <;> decide
  labels := by intro j i hi; exact Subsingleton.elim _ _

theorem face1_lower : (face1 false).Lower := by unfold Cubical.Face.Lower; decide
theorem face1_upper : (face1 true).Upper := by unfold Cubical.Face.Upper; decide

def s0 : Step zero one := .start (Completion.endpointFace false) Completion.lowerFace rfl
def t0 : Step one zero := .stop (Completion.endpointFace true) Completion.upperFace rfl
def s1 : Step one two := .start (face1 false) face1_lower rfl
def t1 : Step two one := .stop (face1 true) face1_upper rfl

def a : Word zero zero := .cons s0 (.cons t0 (.nil zero))
def E : Word zero one := .cons s0 (.nil one)
def F : Word zero one := .cons s0 (.cons s1 (.cons t1 (.nil one)))
def G : Word zero one := a.append E

def H : Word zero two := E.append (.cons s1 (.nil two))
def I : Word zero two := G.append (.cons s1 (.nil two))
def dead2 : Word zero two := F.append (.cons s1 (.nil two))
def dead1 : Word zero one := dead2.append (.cons t1 (.nil one))
def dead0 : Word zero zero := dead1.append (.cons t0 (.nil zero))

def end1 : Word one zero := .cons t0 (.nil zero)
def end2 : Word two zero := .cons t1 (.cons t0 (.nil zero))

end CounterFreeHDA.Appendix.Unary

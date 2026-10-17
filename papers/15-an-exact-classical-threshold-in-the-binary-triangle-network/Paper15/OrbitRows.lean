import Paper15.CertificateData.Representatives
namespace Paper15.OrbitCheck
open Exact

structure Choice where
  target : Nat
  code : Nat
  deriving Repr
abbrev Row := Tri (Tri (Tri Choice))

def Row.at (row : Row) (p : Fin 27) : Choice :=
  ((row.get ⟨p.val/9,by omega⟩).get ⟨p.val/3%3,by omega⟩).get ⟨p.val%3,by omega⟩

noncomputable def rowValid (r : Nat) (row : Row) : Bool :=
  slots.all (fun p => transition r p.val (representatives.at (row.at p).target) (row.at p).code)

def HasCheckedNeighbours (r : Nat) : Prop := ∃row : Row,rowValid r row=true
end Paper15.OrbitCheck

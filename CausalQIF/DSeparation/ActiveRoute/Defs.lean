import CausalQIF.DSeparation.BayesBall.Basic

open Finset

namespace CausalQIF.DSeparation

noncomputable section

/-! # ActiveRoute: Stateful Active Paths

An `ActiveRoute` wraps a `BayesBallPath`, providing stateful append and
conversion to an unblocked `Trail`.  Because `BayesBallStep` is `Prop`-valued,
we introduce a parallel `Type`-valued `BayesBallStepT` for recursive
construction.
-/

variable {V : Type} [DecidableEq V] [Fintype V]

namespace BayesBallPath

/-- Append two `BayesBallPath`s at a matching intermediate state. -/
def append {G : Graph.DAG V} {Z : Finset V} {s t u : V × TrailDir}
    (p : BayesBallPath G Z s t) (q : BayesBallPath G Z t u) :
    BayesBallPath G Z s u :=
  match p with
  | nil _ => q
  | cons step rest => cons step (rest.append q)

end BayesBallPath

/-- Type-valued copy of `BayesBallStep` for computational extraction. -/
inductive BayesBallStepT (G : Graph.DAG V) (Z : Finset V) :
    V × TrailDir → V × TrailDir → Type where
  | step {v w : V} {arrival departure : TrailDir}
      (hEdge : TrailDir.edgeIntoCurrent G v w departure)
      (hopen : ¬ directionalTripleBlocked G Z v arrival departure) :
      BayesBallStepT G Z (v, arrival) (w, departure)

/-- Type-valued copy of `BayesBallPath` for computational extraction. -/
inductive BayesBallPathT (G : Graph.DAG V) (Z : Finset V) :
    V × TrailDir → V × TrailDir → Type where
  | nil (s : V × TrailDir) : BayesBallPathT G Z s s
  | cons {s t u : V × TrailDir}
      (step : BayesBallStepT G Z s t)
      (rest : BayesBallPathT G Z t u) :
      BayesBallPathT G Z s u

namespace BayesBallPathT

/-- Append two explicit type-valued paths. -/
def append {G : Graph.DAG V} {Z : Finset V} {s t u : V × TrailDir}
    (p : BayesBallPathT G Z s t) (q : BayesBallPathT G Z t u) :
    BayesBallPathT G Z s u :=
  match p with
  | nil _ => q
  | cons step rest => cons step (rest.append q)

end BayesBallPathT

/-- An ActiveRoute is a BayesBallPath packaged as a route witness. -/
structure ActiveRoute (G : Graph.DAG V) (Z : Finset V)
    (s t : V × TrailDir) : Type where
  path : BayesBallPath G Z s t

end

end CausalQIF.DSeparation

import CausalQIF.DSeparation.ActiveRoute.Defs

open Finset

namespace CausalQIF.DSeparation

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Convert a `Prop`-valued step to a `Type`-valued step. -/
def bayesBallStepT_of_bayesBallStep {G : Graph.DAG V} {Z : Finset V} {s t : V × TrailDir}
    (step : BayesBallStep G Z s t) : BayesBallStepT G Z s t :=
  Classical.choice (show Nonempty (BayesBallStepT G Z s t) from by
    cases step with
    | step hEdge hopen =>
        exact ⟨BayesBallStepT.step hEdge hopen⟩)

/-- Convert a `Prop`-valued path to a `Type`-valued path. -/
def bayesBallPathT_of_bayesBallPath {G : Graph.DAG V} {Z : Finset V} {s t : V × TrailDir}
    (p : BayesBallPath G Z s t) : BayesBallPathT G Z s t := by
  induction p with
  | nil s => exact BayesBallPathT.nil s
  | cons step rest ih =>
      exact BayesBallPathT.cons (bayesBallStepT_of_bayesBallStep step) ih

namespace ActiveRoute

/-- Append two ActiveRoutes when the intermediate state matches exactly. -/
def append {G : Graph.DAG V} {Z : Finset V} {s mid t : V × TrailDir}
    (p : ActiveRoute G Z s mid) (q : ActiveRoute G Z mid t) :
    ActiveRoute G Z s t :=
  ⟨p.path.append q.path⟩

/-- Convert a `BayesBallStepT` to a one-edge Trail segment. -/
def trailOfStep {G : Graph.DAG V} {Z : Finset V} {s t : V × TrailDir}
    (step : BayesBallStepT G Z s t) : Trail G s.1 t.1 := by
  cases step with
  | step hEdge hopen =>
      rename_i v w arrival departure
      cases departure
      · exact Trail.forward (by simpa [TrailDir.edgeIntoCurrent] using hEdge) (Trail.nil _)
      · exact Trail.backward (by simpa [TrailDir.edgeIntoCurrent] using hEdge) (Trail.nil _)

/-- Convert a `BayesBallPathT` to a Trail by concatenating edge segments. -/
def toTrailT {G : Graph.DAG V} {Z : Finset V} {s t : V × TrailDir}
    (p : BayesBallPathT G Z s t) : Trail G s.1 t.1 :=
  match p with
  | BayesBallPathT.nil _ => Trail.nil s.1
  | BayesBallPathT.cons step rest =>
      (trailOfStep step).append (toTrailT rest)

/-- Convert a `BayesBallPath` to a Trail via the type-valued copy. -/
def toTrail {G : Graph.DAG V} {Z : Finset V} {s t : V × TrailDir}
    (p : BayesBallPath G Z s t) : Trail G s.1 t.1 :=
  toTrailT (bayesBallPathT_of_bayesBallPath p)

end ActiveRoute

/-- Existential witness: some `x ∈ X` can reach some `y ∈ Y` via an ActiveRoute
    that starts with direction `outOf`, required when `x ∉ Z`. -/
def ActiveWitness (G : Graph.DAG V) (X Y Z : Finset V) : Prop :=
  ∃ x, x ∈ X ∧ ∃ y, y ∈ Y ∧
    ∃ d, Nonempty (ActiveRoute G Z (x, TrailDir.outOf) (y, d))

end

end CausalQIF.DSeparation

import CausalQIF.DSeparation.Path.Trail

open Finset

namespace CausalQIF.DSeparation

noncomputable section

/-! # Active Trails to Bayes-Ball Bridges

Lemmas that lift an active, non-blocked trail into a Bayes-ball path, both as
reachability and as explicit `BayesBallPath` objects.  These are proof
infrastructure for the moral-graph/trail-blocking equivalence.
-/

variable {V : Type} [DecidableEq V] [Fintype V]

lemma BayesBallStep.of_active_triple {G : Graph.DAG V} {Z : Finset V}
    {a b c : V} {arrival departure : TrailDir}
    (hab : TrailDir.edgeIntoCurrent G a b arrival)
    (hbc : TrailDir.edgeIntoCurrent G b c departure)
    (hactive : ¬ tripleBlocked G Z a b c) :
    BayesBallStep G Z (b, arrival) (c, departure) :=
  BayesBallStep.step hbc
    (by
      rwa [directionalTripleBlocked_iff_tripleBlocked hab hbc])

theorem bayesBallReachable_of_active_trail_from_prev {G : Graph.DAG V} {Z : Finset V}
    {prev u v : V} {arrival : TrailDir}
    (hprev : TrailDir.edgeIntoCurrent G prev u arrival)
    (t : Trail G u v)
    (h_active : ¬ trailBlocked G Z (prev :: t.toList)) :
    ∃ final_dir, BayesBallReachable G Z (u, arrival) (v, final_dir) := by
  induction t generalizing prev arrival with
  | nil v =>
      exact ⟨arrival, Relation.ReflTransGen.refl⟩
  | forward h tail ih =>
      rename_i u0 w0 v0
      have hhead : ¬ tripleBlocked G Z prev u0 w0 :=
        not_tripleBlocked_head_of_not_trailBlocked_trail (t := tail) h_active
      have hstep :
          BayesBallStep G Z (u0, arrival) (w0, TrailDir.into) := by
        exact BayesBallStep.of_active_triple hprev
          (by simpa [TrailDir.edgeIntoCurrent] using h) hhead
      have htail_active : ¬ trailBlocked G Z (u0 :: tail.toList) :=
        not_trailBlocked_tail_of_not_trailBlocked_cons h_active
      rcases ih (prev := u0) (arrival := TrailDir.into)
          (by simpa [TrailDir.edgeIntoCurrent] using h) htail_active with
        ⟨final_dir, htail⟩
      exact ⟨final_dir, (Relation.ReflTransGen.single hstep).trans htail⟩
  | backward h tail ih =>
      rename_i u0 w0 v0
      have hhead : ¬ tripleBlocked G Z prev u0 w0 :=
        not_tripleBlocked_head_of_not_trailBlocked_trail (t := tail) h_active
      have hstep :
          BayesBallStep G Z (u0, arrival) (w0, TrailDir.outOf) := by
        exact BayesBallStep.of_active_triple hprev
          (by simpa [TrailDir.edgeIntoCurrent] using h) hhead
      have htail_active : ¬ trailBlocked G Z (u0 :: tail.toList) :=
        not_trailBlocked_tail_of_not_trailBlocked_cons h_active
      rcases ih (prev := u0) (arrival := TrailDir.outOf)
          (by simpa [TrailDir.edgeIntoCurrent] using h) htail_active with
        ⟨final_dir, htail⟩
      exact ⟨final_dir, (Relation.ReflTransGen.single hstep).trans htail⟩

def bayesBallPath_of_active_trail_from_prev {G : Graph.DAG V} {Z : Finset V}
    {prev u v : V} {arrival : TrailDir}
    (hprev : TrailDir.edgeIntoCurrent G prev u arrival)
    (t : Trail G u v)
    (h_active : ¬ trailBlocked G Z (prev :: t.toList)) :
    Σ final_dir, BayesBallPath G Z (u, arrival) (v, final_dir) := by
  induction t generalizing prev arrival with
  | nil v =>
      exact ⟨arrival, BayesBallPath.nil (v, arrival)⟩
  | forward h tail ih =>
      rename_i u0 w0 v0
      have hhead : ¬ tripleBlocked G Z prev u0 w0 :=
        not_tripleBlocked_head_of_not_trailBlocked_trail (t := tail) h_active
      have hstep :
          BayesBallStep G Z (u0, arrival) (w0, TrailDir.into) := by
        exact BayesBallStep.of_active_triple hprev
          (by simpa [TrailDir.edgeIntoCurrent] using h) hhead
      have htail_active : ¬ trailBlocked G Z (u0 :: tail.toList) :=
        not_trailBlocked_tail_of_not_trailBlocked_cons h_active
      rcases ih (prev := u0) (arrival := TrailDir.into)
          (by simpa [TrailDir.edgeIntoCurrent] using h) htail_active with
        ⟨final_dir, htail⟩
      exact ⟨final_dir, BayesBallPath.cons hstep htail⟩
  | backward h tail ih =>
      rename_i u0 w0 v0
      have hhead : ¬ tripleBlocked G Z prev u0 w0 :=
        not_tripleBlocked_head_of_not_trailBlocked_trail (t := tail) h_active
      have hstep :
          BayesBallStep G Z (u0, arrival) (w0, TrailDir.outOf) := by
        exact BayesBallStep.of_active_triple hprev
          (by simpa [TrailDir.edgeIntoCurrent] using h) hhead
      have htail_active : ¬ trailBlocked G Z (u0 :: tail.toList) :=
        not_trailBlocked_tail_of_not_trailBlocked_cons h_active
      rcases ih (prev := u0) (arrival := TrailDir.outOf)
          (by simpa [TrailDir.edgeIntoCurrent] using h) htail_active with
        ⟨final_dir, htail⟩
      exact ⟨final_dir, BayesBallPath.cons hstep htail⟩

theorem bayesBallReachable_of_active_trail {G : Graph.DAG V} {Z : Finset V} {u v : V}
    (t : Trail G u v)
    (h_active : ¬ t.isBlocked Z)
    (init_dir : TrailDir)
    (h_start : t.startOpen Z init_dir) :
    ∃ final_dir, BayesBallReachable G Z (u, init_dir) (v, final_dir) := by
  cases t with
  | nil v =>
      exact ⟨init_dir, Relation.ReflTransGen.refl⟩
  | forward h tail =>
      rename_i w0
      have hstep :
          BayesBallStep G Z (u, init_dir) (w0, TrailDir.into) :=
        BayesBallStep.step (by simpa [TrailDir.edgeIntoCurrent] using h)
          (by simpa [Trail.startOpen] using h_start)
      have htail_active : ¬ trailBlocked G Z (u :: tail.toList) := by
        simpa [Trail.isBlocked, Trail.toList] using h_active
      rcases bayesBallReachable_of_active_trail_from_prev
          (G := G) (Z := Z) (prev := u) (u := w0) (v := v)
          (arrival := TrailDir.into)
          (by simpa [TrailDir.edgeIntoCurrent] using h) tail htail_active with
        ⟨final_dir, htail⟩
      exact ⟨final_dir, (Relation.ReflTransGen.single hstep).trans htail⟩
  | backward h tail =>
      rename_i w0
      have hstep :
          BayesBallStep G Z (u, init_dir) (w0, TrailDir.outOf) :=
        BayesBallStep.step (by simpa [TrailDir.edgeIntoCurrent] using h)
          (by simpa [Trail.startOpen] using h_start)
      have htail_active : ¬ trailBlocked G Z (u :: tail.toList) := by
        simpa [Trail.isBlocked, Trail.toList] using h_active
      rcases bayesBallReachable_of_active_trail_from_prev
          (G := G) (Z := Z) (prev := u) (u := w0) (v := v)
          (arrival := TrailDir.outOf)
          (by simpa [TrailDir.edgeIntoCurrent] using h) tail htail_active with
        ⟨final_dir, htail⟩
      exact ⟨final_dir, (Relation.ReflTransGen.single hstep).trans htail⟩

def bayesBallPath_of_active_trail {G : Graph.DAG V} {Z : Finset V} {u v : V}
    (t : Trail G u v)
    (h_active : ¬ t.isBlocked Z)
    (init_dir : TrailDir)
    (h_start : t.startOpen Z init_dir) :
    Σ final_dir, BayesBallPath G Z (u, init_dir) (v, final_dir) := by
  cases t with
  | nil v =>
      exact ⟨init_dir, BayesBallPath.nil (u, init_dir)⟩
  | forward h tail =>
      rename_i w0
      have hstep :
          BayesBallStep G Z (u, init_dir) (w0, TrailDir.into) :=
        BayesBallStep.step (by simpa [TrailDir.edgeIntoCurrent] using h)
          (by simpa [Trail.startOpen] using h_start)
      have htail_active : ¬ trailBlocked G Z (u :: tail.toList) := by
        simpa [Trail.isBlocked, Trail.toList] using h_active
      rcases bayesBallPath_of_active_trail_from_prev
          (G := G) (Z := Z) (prev := u) (u := w0) (v := v)
          (arrival := TrailDir.into)
          (by simpa [TrailDir.edgeIntoCurrent] using h) tail htail_active with
        ⟨final_dir, htail⟩
      exact ⟨final_dir, BayesBallPath.cons hstep htail⟩
  | backward h tail =>
      rename_i w0
      have hstep :
          BayesBallStep G Z (u, init_dir) (w0, TrailDir.outOf) :=
        BayesBallStep.step (by simpa [TrailDir.edgeIntoCurrent] using h)
          (by simpa [Trail.startOpen] using h_start)
      have htail_active : ¬ trailBlocked G Z (u :: tail.toList) := by
        simpa [Trail.isBlocked, Trail.toList] using h_active
      rcases bayesBallPath_of_active_trail_from_prev
          (G := G) (Z := Z) (prev := u) (u := w0) (v := v)
          (arrival := TrailDir.outOf)
          (by simpa [TrailDir.edgeIntoCurrent] using h) tail htail_active with
        ⟨final_dir, htail⟩
      exact ⟨final_dir, BayesBallPath.cons hstep htail⟩

lemma Trail.startOpen_outOf_of_not_mem {G : Graph.DAG V} {Z : Finset V} {u v : V}
    {t : Trail G u v} (huZ : u ∉ Z) :
    t.startOpen Z TrailDir.outOf := by
  cases t <;>
    simp [Trail.startOpen, directionalTripleBlocked, TrailDir.colliderAtCurrent, huZ]

theorem bayesBallReachable_of_active_trail_outOf {G : Graph.DAG V} {Z : Finset V}
    {u v : V} (t : Trail G u v)
    (h_active : ¬ t.isBlocked Z) (huZ : u ∉ Z) :
    ∃ final_dir, BayesBallReachable G Z (u, TrailDir.outOf) (v, final_dir) :=
  bayesBallReachable_of_active_trail t h_active TrailDir.outOf
    (Trail.startOpen_outOf_of_not_mem huZ)

def bayesBallPath_of_active_trail_outOf {G : Graph.DAG V} {Z : Finset V}
    {u v : V} (t : Trail G u v)
    (h_active : ¬ t.isBlocked Z) (huZ : u ∉ Z) :
    Σ final_dir, BayesBallPath G Z (u, TrailDir.outOf) (v, final_dir) :=
  bayesBallPath_of_active_trail t h_active TrailDir.outOf
    (Trail.startOpen_outOf_of_not_mem huZ)

end

end CausalQIF.DSeparation

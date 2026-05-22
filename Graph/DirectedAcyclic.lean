import Mathlib

open Finset

namespace CausalQIF.Graph

noncomputable section

/-! # DAG Basic Definitions

Finite directed acyclic graph over generic node labels.
Acyclicity witnessed by well-foundedness.
-/

structure DAG (V : Type) [DecidableEq V] [Fintype V] where
  nodes : Finset V
  edges : Finset (V × V)
  edges_subset : ∀ {u v : V}, (u, v) ∈ edges → u ∈ nodes ∧ v ∈ nodes
  acyclic : WellFounded fun u v => (u, v) ∈ edges

namespace DAG

variable {V : Type} [DecidableEq V] [Fintype V]

def hasEdge (G : DAG V) (u v : V) : Prop :=
  (u, v) ∈ G.edges

def ofRank {V : Type} [DecidableEq V] [Fintype V] (nodes : Finset V) (edges : Finset (V × V)) (rank : V → ℕ)
    (edges_subset : ∀ {u v : V}, (u, v) ∈ edges → u ∈ nodes ∧ v ∈ nodes)
    (rank_increases : ∀ {u v : V}, (u, v) ∈ edges → rank u < rank v) : DAG V where
  nodes := nodes
  edges := edges
  edges_subset := edges_subset
  acyclic :=
    (InvImage.wf rank wellFounded_lt).mono fun _ _ h => rank_increases h

def respectsTopologicalRank (G : DAG V) (rank : V → ℕ) : Prop :=
  ∀ {u v : V}, G.hasEdge u v → rank u < rank v

lemma ne_of_hasEdge (G : DAG V) {u v : V} (h : G.hasEdge u v) : u ≠ v := by
  intro huv
  subst v
  exact (G.acyclic.irrefl.irrefl u) (by simpa [DAG.hasEdge] using h)

lemma not_hasEdge_reverse_of_hasEdge (G : DAG V) {u v : V} (h : G.hasEdge u v) :
    ¬ G.hasEdge v u := by
  intro hrev
  have hcycle : Relation.TransGen (fun a b => G.hasEdge a b) u u :=
    Relation.TransGen.head h (Relation.TransGen.single hrev)
  exact (not_transGen_self_of_wellFounded G.acyclic u) hcycle
where
  not_transGen_self_of_wellFounded {α : Type} {r : α → α → Prop}
      (h : WellFounded r) (a : α) :
      ¬ Relation.TransGen r a a := by
    induction a using h.induction with
    | h x ih =>
        intro hcycle
        rcases Relation.TransGen.tail'_iff.mp hcycle with ⟨y, hxy, hyx⟩
        rcases Relation.reflTransGen_iff_eq_or_transGen.mp hxy with h_eq | htrans
        · subst y
          exact h.irrefl.irrefl x hyx
        · exact ih y hyx (Relation.TransGen.head hyx htrans)

end DAG

variable {V : Type} [DecidableEq V] [Fintype V]

def parents (G : DAG V) (v : V) : Finset V :=
  (G.edges.filter fun e => e.2 = v).image Prod.fst

def children (G : DAG V) (v : V) : Finset V :=
  (G.edges.filter fun e => e.1 = v).image Prod.snd

def isLeaf (G : DAG V) (v : V) : Prop :=
  v ∈ G.nodes ∧ children G v = ∅

def adjacent (G : DAG V) (u v : V) : Prop :=
  G.hasEdge u v ∨ G.hasEdge v u

def consecutive {V : Type} (R : V → V → Prop) : List V → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => R a b ∧ consecutive R (b :: rest)

end

end CausalQIF.Graph

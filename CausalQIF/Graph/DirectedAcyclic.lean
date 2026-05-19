import Mathlib

open Finset

namespace CausalQIF.Graph

noncomputable section

/-! # DAG Basic Definitions

Finite directed acyclic graph over natural-number node labels.
Acyclicity witnessed by well-foundedness.
-/

structure DAG where
  nodes : Finset ℕ
  edges : Finset (ℕ × ℕ)
  edges_subset : ∀ {u v : ℕ}, (u, v) ∈ edges → u ∈ nodes ∧ v ∈ nodes
  acyclic : WellFounded fun u v => (u, v) ∈ edges

namespace DAG

def HasEdge (G : DAG) (u v : ℕ) : Prop :=
  (u, v) ∈ G.edges

def ofRank (nodes : Finset ℕ) (edges : Finset (ℕ × ℕ)) (rank : ℕ → ℕ)
    (edges_subset : ∀ {u v : ℕ}, (u, v) ∈ edges → u ∈ nodes ∧ v ∈ nodes)
    (rank_increases : ∀ {u v : ℕ}, (u, v) ∈ edges → rank u < rank v) : DAG where
  nodes := nodes
  edges := edges
  edges_subset := edges_subset
  acyclic :=
    (InvImage.wf rank wellFounded_lt).mono fun _ _ h => rank_increases h

def RespectsTopologicalRank (G : DAG) (rank : ℕ → ℕ) : Prop :=
  ∀ {u v : ℕ}, G.HasEdge u v → rank u < rank v

lemma ne_of_hasEdge (G : DAG) {u v : ℕ} (h : G.HasEdge u v) : u ≠ v := by
  intro huv
  subst v
  exact (G.acyclic.irrefl.irrefl u) (by simpa [DAG.HasEdge] using h)

lemma not_hasEdge_reverse_of_hasEdge (G : DAG) {u v : ℕ} (h : G.HasEdge u v) :
    ¬ G.HasEdge v u := by
  intro hrev
  have hcycle : Relation.TransGen (fun a b => G.HasEdge a b) u u :=
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

def parents (G : DAG) (v : ℕ) : Finset ℕ :=
  (G.edges.filter fun e => e.2 = v).image Prod.fst

def children (G : DAG) (v : ℕ) : Finset ℕ :=
  (G.edges.filter fun e => e.1 = v).image Prod.snd

def IsLeaf (G : DAG) (v : ℕ) : Prop :=
  v ∈ G.nodes ∧ children G v = ∅

def Adjacent (G : DAG) (u v : ℕ) : Prop :=
  G.HasEdge u v ∨ G.HasEdge v u

def Consecutive (R : ℕ → ℕ → Prop) : List ℕ → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => R a b ∧ Consecutive R (b :: rest)

end

end CausalQIF.Graph

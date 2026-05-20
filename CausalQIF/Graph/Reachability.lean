import CausalQIF.Graph.DirectedAcyclic
import Mathlib.Data.Nat.Basic

open Finset

namespace CausalQIF.Graph

/-! # DAG Reachability

Descendants, ancestors, ancestral subgraph, leaf deletion.
-/

variable {V : Type} [DecidableEq V] [Fintype V]

def reachableStep (G : DAG V) (S : Finset V) : Finset V :=
  S ∪ S.biUnion (fun v => (G.edges.filter (fun e => e.1 = v)).image Prod.snd)

def reachableFinset (G : DAG V) (u : V) : Finset V :=
  (Nat.iterate (reachableStep G) (Fintype.card V)) {u}

lemma reachable_equiv_reachableFinset (G : DAG V) (u v : V) :
    v ∈ reachableFinset G u ↔ Relation.ReflTransGen (fun a b => G.hasEdge a b) u v := by
  sorry

def reachable (G : DAG V) (u v : V) : Prop :=
  Relation.ReflTransGen (fun a b => G.hasEdge a b) u v

instance (G : DAG V) (u v : V) : Decidable (reachable G u v) :=
  decidable_of_iff (v ∈ reachableFinset G u) (reachable_equiv_reachableFinset G u v)

def descendants (G : DAG V) (v : V) : Finset V :=
  G.nodes.filter fun w => w ≠ v ∧ reachable G v w

def ancestors (G : DAG V) (v : V) : Finset V :=
  G.nodes.filter fun u => u ≠ v ∧ reachable G u v

def nonDescendants (G : DAG V) (v : V) : Finset V :=
  G.nodes \ ({v} ∪ descendants G v)

namespace DAG

variable {V : Type} [DecidableEq V] [Fintype V]

def ancestors (G : DAG V) (v : V) : Finset V :=
  G.nodes.filter fun u => reachable G u v

def ancestralSubgraphNodes (G : DAG V) (S : Finset V) : Finset V :=
  S.biUnion fun v => G.ancestors v

def ancestralSubgraph (G : DAG V) (S : Finset V) : DAG V where
  nodes := G.ancestralSubgraphNodes S
  edges := G.edges.filter fun e =>
    e.1 ∈ G.ancestralSubgraphNodes S ∧ e.2 ∈ G.ancestralSubgraphNodes S
  edges_subset := by
    intro u v h
    exact (Finset.mem_filter.mp h).2
  acyclic :=
    G.acyclic.mono fun _ _ h => (Finset.mem_filter.mp h).1

def deleteLeaf (G : DAG V) (v : V) : DAG V where
  nodes := G.nodes.erase v
  edges := G.edges.filter fun e => e.1 ≠ v ∧ e.2 ≠ v
  edges_subset := by
    intro u w h
    rcases Finset.mem_filter.mp h with ⟨hedge, hu_ne, hw_ne⟩
    exact ⟨Finset.mem_erase.mpr ⟨hu_ne, (G.edges_subset hedge).1⟩,
      Finset.mem_erase.mpr ⟨hw_ne, (G.edges_subset hedge).2⟩⟩
  acyclic :=
    G.acyclic.mono fun _ _ h => (Finset.mem_filter.mp h).1

lemma deleteLeaf_card_lt {G : DAG V} {v : V} (hv : v ∈ G.nodes) :
    (G.deleteLeaf v).nodes.card < G.nodes.card := by
  simpa [DAG.deleteLeaf] using Finset.card_erase_lt_of_mem hv

lemma mem_ancestors_self (G : DAG V) {v : V} (hv : v ∈ G.nodes) :
    v ∈ G.ancestors v := by
  simp [DAG.ancestors, reachable, Relation.ReflTransGen.refl, hv]

lemma target_mem_nodes_of_reachable {G : DAG V} {u v : V}
    (hreach : reachable G u v) (hu : u ∈ G.nodes) :
    v ∈ G.nodes := by
  induction hreach with
  | refl =>
      exact hu
  | tail _ hstep _ =>
      exact (G.edges_subset hstep).2

lemma mem_ancestralSubgraphNodes_of_mem {G : DAG V} {S : Finset V} {v : V}
    (hvS : v ∈ S) (hvG : v ∈ G.nodes) :
    v ∈ G.ancestralSubgraphNodes S := by
  exact Finset.mem_biUnion.mpr ⟨v, hvS, G.mem_ancestors_self hvG⟩

lemma mem_ancestors_of_hasEdge_of_mem_ancestors {G : DAG V} {u v s : V}
    (huv : G.hasEdge u v) (hvs : v ∈ G.ancestors s) :
    u ∈ G.ancestors s := by
  have huG : u ∈ G.nodes := (G.edges_subset huv).1
  have hreach_v_s : reachable G v s := (Finset.mem_filter.mp hvs).2
  have hreach_u_s : reachable G u s :=
    (Relation.ReflTransGen.single huv).trans hreach_v_s
  exact Finset.mem_filter.mpr ⟨huG, hreach_u_s⟩

lemma mem_ancestralSubgraphNodes_of_hasEdge_left {G : DAG V} {S : Finset V} {u v : V}
    (huv : G.hasEdge u v) (hv : v ∈ G.ancestralSubgraphNodes S) :
    u ∈ G.ancestralSubgraphNodes S := by
  rcases Finset.mem_biUnion.mp hv with ⟨s, hsS, hvs⟩
  exact Finset.mem_biUnion.mpr
    ⟨s, hsS, mem_ancestors_of_hasEdge_of_mem_ancestors huv hvs⟩

end DAG

end CausalQIF.Graph

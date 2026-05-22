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

private lemma mem_reachableStep_of_mem_of_hasEdge (G : DAG V) {S : Finset V} {a b : V}
    (ha : a ∈ S) (hab : G.hasEdge a b) : b ∈ reachableStep G S := by
  -- `reachableStep` adds all out-neighbors of elements already in `S`.
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_biUnion.mpr
  refine ⟨a, ha, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨(a, b), ?_, rfl⟩
  exact Finset.mem_filter.mpr ⟨hab, rfl⟩

private lemma getLast_mem_iterate_of_isChain (G : DAG V) :
    ∀ {S : Finset V} {a : V} (l : List V),
      a ∈ S →
        List.IsChain (fun x y => G.hasEdge x y) (a :: l) →
          List.getLast (a :: l) (List.cons_ne_nil _ _) ∈ Nat.iterate (reachableStep G) l.length S
  | S, a, [], haS, _ => by
      simpa using haS
  | S, a, b :: rest, haS, hchain => by
      -- Peel one edge `a ⟶ b`, advance the start set by one `reachableStep`, and continue.
      cases hchain with
      | cons_cons hab htail =>
          have hb : b ∈ reachableStep G S :=
            mem_reachableStep_of_mem_of_hasEdge (G := G) haS hab
          -- Reduce to the tail chain starting at `b`.
          have ih :=
            getLast_mem_iterate_of_isChain (G := G) (S := reachableStep G S) (a := b) rest hb htail
          -- Align the `getLast` node and the iterate index.
          simpa [Nat.iterate, List.getLast_cons_cons] using ih

private lemma not_transGen_self_of_wellFounded {α : Type} {r : α → α → Prop}
    (hwf : WellFounded r) (a : α) : ¬ Relation.TransGen r a a := by
  induction a using hwf.induction with
  | h x ih =>
      intro hcycle
      rcases Relation.TransGen.tail'_iff.mp hcycle with ⟨y, hxy, hyx⟩
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp hxy with h_eq | htrans
      · subst y
        exact (hwf.irrefl.irrefl x) hyx
      · exact ih y hyx (Relation.TransGen.head hyx htrans)

private lemma nodup_of_isChain_of_wellFounded {α : Type} {r : α → α → Prop}
    (hwf : WellFounded r) :
    ∀ l : List α, List.IsChain r l → l.Nodup
  | [], _ => by simp
  | [a], _ => by simp
  | a :: b :: rest, hchain => by
      cases hchain with
      | cons_cons hab htail =>
          have ih : (b :: rest).Nodup :=
            nodup_of_isChain_of_wellFounded hwf (b :: rest) htail
          have ha_not_mem : a ∉ b :: rest := by
            intro ha_mem
            -- Anything in the tail is transitively reachable from `a`, hence `a ∈ tail` would
            -- create a nontrivial cycle contradicting well-foundedness.
            have hcycle : Relation.TransGen r a a := by
              -- First step `a ⟶ b`.
              have hab' : Relation.TransGen r a b := Relation.TransGen.single hab
              -- If `a = b`, we already have a 1-step cycle.
              by_cases habEq : b = a
              · subst habEq
                simpa using hab'
              · -- Otherwise `a` appears strictly later in `rest`; propagate transitive reachability
                -- along the tail chain.
                have hprop :
                    ∀ i ∈ rest, Relation.TransGen r a i :=
                  fun i hi =>
                    (List.IsChain.cons_induction (a := b) (l := rest)
                        (p := fun x => Relation.TransGen r a x) htail
                        (carries := fun {x y} hxy hx => Relation.TransGen.tail hx hxy)
                        (initial := hab') i hi)
                have ha_in_rest : a ∈ rest := by
                  have ha_or : a = b ∨ a ∈ rest := by
                    simpa [List.mem_cons] using ha_mem
                  rcases ha_or with hhead | htail_mem
                  · exact (habEq hhead.symm).elim
                  · exact htail_mem
                exact hprop a ha_in_rest
            exact not_transGen_self_of_wellFounded hwf a hcycle
          simp [List.nodup_cons, ha_not_mem, ih]

private lemma mem_iterate_reachableStep_of_mem {G : DAG V} {S : Finset V} {x : V} :
    ∀ k n,
      x ∈ Nat.iterate (reachableStep G) n S →
        x ∈ Nat.iterate (reachableStep G) (n + k) S
  | 0, n, hx => by
      simpa using hx
  | k + 1, n, hx => by
      have hxk : x ∈ Nat.iterate (reachableStep G) (n + k) S :=
        mem_iterate_reachableStep_of_mem (G := G) (S := S) (x := x) k n hx
      have hxstep :
          x ∈ reachableStep G (Nat.iterate (reachableStep G) (n + k) S) :=
        Finset.mem_union.mpr (Or.inl hxk)
      rw [Nat.add_succ, Function.iterate_succ_apply']
      exact hxstep

lemma reachable_equiv_reachableFinset (G : DAG V) (u v : V) :
    v ∈ reachableFinset G u ↔ Relation.ReflTransGen (fun a b => G.hasEdge a b) u v := by
  constructor
  · intro hv
    -- Show membership in the computed closure implies `ReflTransGen` reachability.
    -- We prove the stronger statement for any iteration count and specialize to `card V`.
    have mem_iterate_imp :
        ∀ n {x : V},
          x ∈ Nat.iterate (reachableStep G) n {u} →
            Relation.ReflTransGen (fun a b => G.hasEdge a b) u x := by
      intro n
      induction n with
      | zero =>
          intro x hx
          -- `iterate 0` is the identity.
          have hx_eq : x = u := by
            simpa using (by
              simpa [Function.iterate_zero] using hx : x ∈ ({u} : Finset V))
          subst x
          exact Relation.ReflTransGen.refl
      | succ n ih =>
          intro x hx
          -- `iterate (n+1)` expands one step from `iterate n`.
          have hx' : x ∈ reachableStep G (Nat.iterate (reachableStep G) n {u}) := by
            simpa [Function.iterate_succ_apply'] using hx
          rcases Finset.mem_union.mp hx' with hxS | hxNew
          · exact ih hxS
          · rcases Finset.mem_biUnion.mp hxNew with ⟨a, ha, hxImg⟩
            rcases Finset.mem_image.mp hxImg with ⟨e, he, rfl⟩
            have hea : e ∈ G.edges := (Finset.mem_filter.mp he).1
            have hfst : e.1 = a := (Finset.mem_filter.mp he).2
            subst hfst
            -- `a` was already reachable; take one `hasEdge` step to reach `e.2`.
            exact (ih ha).tail hea
    simpa [reachableFinset] using mem_iterate_imp (Fintype.card V) (x := v) hv
  · intro hreach
    -- Convert the reachability proof into an explicit edge-chain list.
    rcases List.exists_isChain_cons_of_relationReflTransGen hreach with ⟨l, hl_chain, hl_last⟩
    -- The chain cannot repeat nodes in a well-founded relation.
    have hnodup : (u :: l).Nodup :=
      nodup_of_isChain_of_wellFounded (r := fun a b => G.hasEdge a b) G.acyclic (u :: l) hl_chain
    have hlen : l.length ≤ Fintype.card V := by
      -- `length (u :: l) ≤ card V`, hence `length l ≤ card V`.
      have hlen' : (u :: l).length ≤ Fintype.card V :=
        List.Nodup.length_le_card (α := V) hnodup
      exact Nat.le_trans (Nat.le_succ l.length) hlen'
    -- Follow the chain for `l.length` steps from `{u}`.
    have hv_len :
        List.getLast (u :: l) (List.cons_ne_nil _ _) ∈ Nat.iterate (reachableStep G) l.length {u} :=
      getLast_mem_iterate_of_isChain (G := G) (S := ({u} : Finset V)) (a := u) l
        (by simp) hl_chain
    -- Extend membership from `l.length` steps to `card V` steps (reachability steps only grow).
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hlen
    -- `card V = l.length + k`
    have hv_card :
        List.getLast (u :: l) (List.cons_ne_nil _ _) ∈
          Nat.iterate (reachableStep G) (Fintype.card V) {u} := by
      simpa [hk] using
        (mem_iterate_reachableStep_of_mem (G := G) (S := ({u} : Finset V))
          (x := List.getLast (u :: l) (List.cons_ne_nil _ _)) k l.length hv_len)
    -- Replace the `getLast` with `v`.
    -- `getLast (u :: l) = v` from chain extraction.
    simpa [reachableFinset, hl_last] using hv_card

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

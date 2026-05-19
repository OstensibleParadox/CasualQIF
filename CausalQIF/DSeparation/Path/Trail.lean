import CausalQIF.Graph.Moralization

open Finset

namespace CausalQIF.DSeparation

noncomputable section

/-! # Trails and Local Blocking

Core trail syntax, triple predicates, local triple blocking.
-/

def HasTriple (xs : List ℕ) (a b c : ℕ) : Prop :=
  ∃ pre post : List ℕ, xs = pre ++ a :: b :: c :: post

inductive Trail (G : Graph.DAG) : ℕ → ℕ → Type where
  | nil (v : ℕ) : Trail G v v
  | forward {u w v : ℕ} (h : G.HasEdge u w) (tail : Trail G w v) : Trail G u v
  | backward {u w v : ℕ} (h : G.HasEdge w u) (tail : Trail G w v) : Trail G u v

namespace Trail

def toList {G : Graph.DAG} : {u v : ℕ} → Trail G u v → List ℕ
  | _, _, nil v => [v]
  | u, _, forward (u := _) (w := _) (v := _) _ tail => u :: toList tail
  | u, _, backward (u := _) (w := _) (v := _) _ tail => u :: toList tail

def nodes {G : Graph.DAG} {u v : ℕ} (t : Trail G u v) : Finset ℕ :=
  t.toList.toFinset

@[simp]
lemma mem_nodes {G : Graph.DAG} {u v a : ℕ} {t : Trail G u v} :
    a ∈ t.nodes ↔ a ∈ t.toList := by
  simp [nodes]

lemma target_mem_graph_nodes_of_source_mem {G : Graph.DAG} {u v : ℕ}
    (t : Trail G u v) (hu : u ∈ G.nodes) :
    v ∈ G.nodes := by
  induction t with
  | nil _ =>
      exact hu
  | forward h tail ih =>
      exact ih (G.edges_subset h).2
  | backward h tail ih =>
      exact ih (G.edges_subset h).1

def append {G : Graph.DAG} {u v w : ℕ} (p : Trail G u v) (q : Trail G v w) :
    Trail G u w :=
  match p with
  | nil _ => q
  | forward h tail => forward h (tail.append q)
  | backward h tail => backward h (tail.append q)

lemma exists_ofReachableForward {G : Graph.DAG} {u v : ℕ}
    (h : Graph.Reachable G u v) : Nonempty (Trail G u v) := by
  induction h with
  | refl =>
      exact ⟨Trail.nil u⟩
  | tail _ hstep ih =>
      rcases ih with ⟨tail⟩
      exact ⟨tail.append (Trail.forward hstep (Trail.nil _))⟩

lemma exists_ofReachableBackward {G : Graph.DAG} {u v : ℕ}
    (h : Graph.Reachable G u v) : Nonempty (Trail G v u) := by
  induction h with
  | refl =>
      exact ⟨Trail.nil u⟩
  | tail _ hstep ih =>
      rcases ih with ⟨tail⟩
      exact ⟨(Trail.backward hstep (Trail.nil _)).append tail⟩

end Trail

def TripleCollider (G : Graph.DAG) (a b c : ℕ) : Prop :=
  G.HasEdge a b ∧ G.HasEdge c b

def TripleBlocked (G : Graph.DAG) (Z : Finset ℕ) (a b c : ℕ) : Prop :=
  (¬ TripleCollider G a b c ∧ b ∈ Z) ∨
    (TripleCollider G a b c ∧ Disjoint ({b} ∪ Graph.descendants G b) Z)

inductive TrailDir where
  | into
  | outOf
  deriving DecidableEq

namespace TrailDir

def edgeIntoCurrent (G : Graph.DAG) (prev curr : ℕ) : TrailDir → Prop
  | into => G.HasEdge prev curr
  | outOf => G.HasEdge curr prev

def colliderAtCurrent (arrival departure : TrailDir) : Prop :=
  arrival = into ∧ departure = outOf

end TrailDir

def DirectionalTripleBlocked (G : Graph.DAG) (Z : Finset ℕ) (b : ℕ)
    (arrival departure : TrailDir) : Prop :=
  (¬ TrailDir.colliderAtCurrent arrival departure ∧ b ∈ Z) ∨
    (TrailDir.colliderAtCurrent arrival departure ∧
      Disjoint ({b} ∪ Graph.descendants G b) Z)

def TrailBlocked (G : Graph.DAG) (Z : Finset ℕ) (xs : List ℕ) : Prop :=
  ∃ a b c : ℕ, HasTriple xs a b c ∧ TripleBlocked G Z a b c

def Trail.isBlocked {G : Graph.DAG} {u v : ℕ} (Z : Finset ℕ) (t : Trail G u v) : Prop :=
  TrailBlocked G Z t.toList

def Trail.StartOpen {G : Graph.DAG} {u v : ℕ} (Z : Finset ℕ) (init_dir : TrailDir)
    (t : Trail G u v) : Prop :=
  match t with
  | Trail.nil _ => True
  | Trail.forward (u := u) _ _ =>
      ¬ DirectionalTripleBlocked G Z u init_dir TrailDir.into
  | Trail.backward (u := u) _ _ =>
      ¬ DirectionalTripleBlocked G Z u init_dir TrailDir.outOf

def dSeparates (G : Graph.DAG) (X Y Z : Finset ℕ) : Prop :=
  ∀ x, x ∈ X → ∀ y, y ∈ Y → ∀ t : Trail G x y, t.isBlocked Z

def DisjointSets (X Y Z : Finset ℕ) : Prop :=
  Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z

lemma HasTriple.cons {xs : List ℕ} {a b c x : ℕ}
    (h : HasTriple xs a b c) :
    HasTriple (x :: xs) a b c := by
  rcases h with ⟨pre, post, hxs⟩
  exact ⟨x :: pre, post, by simp [hxs, List.cons_append]⟩

lemma HasTriple.head_of_trail {G : Graph.DAG} {a b c v : ℕ} (t : Trail G c v) :
    HasTriple (a :: b :: t.toList) a b c := by
  cases t with
  | nil v =>
      exact ⟨[], [], by simp [Trail.toList]⟩
  | forward h tail =>
      exact ⟨[], tail.toList, by simp [Trail.toList]⟩
  | backward h tail =>
      exact ⟨[], tail.toList, by simp [Trail.toList]⟩

end

end CausalQIF.DSeparation

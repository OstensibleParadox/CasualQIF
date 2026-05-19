# POPL Paper Reframing — 3-Act Structure

**Date:** 2026-05-20
**Status:** Active. Replaces previous "unified end-to-end QIF pipeline" pitch.
**Companion:** `20260520_debt1_factorization.md`, `20260520_debt2_dual_witness.md`.

---

## Title

> Beyond Boolean Intersections: A Verified Bisimulation and Trace Decompiler
> for Causal Graphs

## Three-Act Structure

### Act 1 — The Bug in the Math Textbook

For decades, two textbook characterizations of d-separation — Pearl's
trail-blocking predicate and Lauritzen's moralized ancestral graph — have been
treated as unconditionally equivalent. When we formalized both in Lean 4's
dependent type system, we discovered a **mechanized counterexample**: when an
endpoint lies in the conditioning set Z, the moral-graph construction deletes
that endpoint while the trail predicate still admits the one-edge trail with no
internal triple. The unrestricted equivalence is **false**.

Key theorem (proved, zero-sorry):

```lean
theorem dsep_complete_endpoint_in_Z_counterexample :
    ∃ (G : DAG) (X Y Z : Finset ℕ),
      DAG.dSeparated G X Y Z ∧ ¬ dSeparates G X Y Z
```

Source: `popl27/DSeparation/Counterexample.lean`. Not yet ported to `CasualQIF/`.

The fix: `DisjointSets X Y Z` — a pairwise-disjointness precondition that acts
as an ownership/aliasing guard, ensuring conditioned variables cannot be
double-borrowed by the query endpoints. Under this guard, the equivalence holds.

### Act 2 — The Compiler & Decompiler

To repair the equivalence, we build two verified transformations:

**Forward compiler (Certified Trace Optimizer):**
Given a raw operational trace (active `Trail`), the compiler tracks directional
signal flow (Bayes-Ball typestate), eliminates redundant collider variables, and
compresses the trace into a dense reachability IR (`MAGWalk` → moral-graph
connectivity). This is a peephole optimizer: local triple patterns map to graph
adjacency or co-parent jumps.

```
Trail (¬isBlocked)
  → BayesBallPath
  → MAGWalk
  → dSeparationGraph.Reachable
```

**Reverse decompiler (Exploit Witness Synthesis):**
When the abstract layer asserts connectivity (data-flow leak risk), the
decompiler **constructively synthesizes** an actual exploit trace witness — not
just a `False`, but a concrete `Trail` that demonstrates the information leak.
The core is a **trace rerouting** paradigm with strict termination: each
reroute eliminates a "bad collider" (illegal Bayes-Ball junction) via
`ancestor_escape`, strictly decreasing a well-founded bad-count measure.

```
¬DAG.dSeparated
  → dSeparationGraph.Reachable
  → StaticRoute
  → NormalizedStaticRoute   (via route_improves_of_bad, well-founded descent)
  → OpenTrace
  → ActiveRoute
  → ∃ Trail, ¬isBlocked
  → ¬dSeparates
```

Key theorems (all proved, zero-sorry):

```lean
theorem route_improves_of_bad {G : DAG} {X Y Z : Finset ℕ}
    (w : StaticRouteWitness G X Y Z) (hbad : routeBadCount w ≠ 0) :
    ∃ w' : StaticRouteWitness G X Y Z, routeBadCount w' < routeBadCount w

theorem activeWitness_of_not_dSeparated {G : DAG} {X Y Z : Finset ℕ}
    (hnot : ¬ DAG.dSeparated G X Y Z) :
    ActiveWitness G X Y Z
```

Source: `popl27/DSeparation/TraceSynthesis/Assembly.lean`. Not yet ported to
`CasualQIF/`.

### Act 3 — The Vision: Quantitative Information Flow

The verified graph computation system becomes the **0-sorry foundation** for
Shannon-level quantitative security bounds. With the corrected d-separation
theory in place, downstream systems can mechanically convert graph-structural
constraints into information-theoretic capacity limits.

The QIF pipeline (proved, zero-sorry, in `CasualQIF/`):

```
d-separation
  → conditional independence (Markov bridge)
  → conditional DPI
  → cut-set bound: stateLeakage P ≤ C
  → entropy gap: H(S|T̃) ≤ H(S|T_full) + C
```

Headline theorem:

```lean
theorem certified_leakage_gap_of_dSeparated_graph
    ... : H_S_cond_Ttilde P ≤ H_S_cond_Tfull P + C
```

Two application-layer debts remain as hypotheses (see companion docs):
- **Debt 1**: `FactorizesOverDAG` is the Global Markov Property stated as
  assumption, not derived from product factorization.
- **Debt 2**: `cutCapacity ≤ C` uses a tautological KKT wrapper; real
  sufficiency needs a dual KL witness.

Both are carried as explicit future work. They do not affect the graph-semantic
core (Acts 1–2), which is self-contained and fully proved.

---

## Why This Framing (Not the Old One)

The previous pitch ("unified end-to-end QIF pipeline") buried the bisimulation
as infrastructure and led with an information-theory headline at a PL venue.
Problems:

1. **Undersold the real contribution.** The bisimulation, counterexample, and
   constructive decompiler are the hard math. Framing them as "Layer 1
   soundness backbone" made the paper's strongest result invisible.

2. **Oversold the QIF chain.** The "end-to-end" claim was hollow at two seams
   (`FactorizesOverDAG` assumed, `cutCapacity` tautological). A reviewer who
   reads the Lean type signatures sees the holes immediately.

3. **Wrong venue language.** POPL reviewers care about type safety, compilers,
   decompilers, ownership models, witness synthesis. "Shannon leakage bound" is
   meaningful but not what excites a PL audience.

The 3-act framing fixes all three:
- The counterexample is the hook (memorable, impactful).
- The compiler/decompiler is the core (native PL vocabulary).
- The QIF pipeline is the payoff (but honest about its assumption boundary).

---

## Code Inventory

### Proved, zero-sorry — in `popl27/` (needs porting to `CasualQIF/`)

| File | Content |
|---|---|
| `Counterexample.lean` | Act 1: mechanized counterexample |
| `Trail/Blocking.lean` | `DisjointSets`, `dSeparates`, trail blocking |
| `Trail/Basic/BayesBall.lean` | Forward compiler: Bayes-Ball state tracking |
| `BayesBall/*` | Forward compiler: certified path compression |
| `MAGWalk/*` | MAGWalk IR and graph-connectivity bridge |
| `TraceSynthesis/StaticRoute.lean` | Decompiler IR: static route and MAGWalk bridge |
| `TraceSynthesis/OpenTrace/*` | Decompiler: bad-collider counting, normalization |
| `TraceSynthesis/MinimalWitness.lean` | Decompiler: bad-count minimization |
| `TraceSynthesis/Split.lean` | Decompiler: first-bad-collider extraction |
| `TraceSynthesis/Graph.lean` | Decompiler: `ancestor_escape`, path survival |
| `TraceSynthesis/Assembly.lean` | Decompiler: `route_improves_of_bad`, `activeWitness_of_not_dSeparated` |

### Proved, zero-sorry — in `CasualQIF/` (already in place)

| File | Content |
|---|---|
| `Graph/*` | DAG, reachability, moralization |
| `DSeparation/*` | MAGWalk ↔ Reachable bisimulation, trail-blocking surface |
| `Probability/*` | FinitePMF, entropy, KL, CMI, Markov chain |
| `CausalModel/*` | Factorization bridge, conditional DPI |
| `InformationFlow/*` | Cut-set bound, KKT certificate, state leakage |
| `Main.lean` | Headline theorem: entropy gap inequality |

### Not yet implemented

| Item | Notes |
|---|---|
| `popl27/ → CasualQIF/` merge | Namespace adaptation (`DSeparation.` → `CausalQIF.DSeparation.`, `ℕ` → generic `V`) |
| Debt 1 (product factorization) | Application-layer; see `20260520_debt1_factorization.md` |
| Debt 2 (dual KL witness) | Application-layer; see `20260520_debt2_dual_witness.md` |

---

## Merge Engineering Notes

**Namespace mismatch:** `popl27/` uses `DSeparation.` with `ℕ`-typed nodes.
`CasualQIF/` uses `CausalQIF.DSeparation.` with generic `V : Type` nodes.
Options:
1. Keep `ℕ` specialization for the counterexample and decompiler (they are
   inherently finite-constructive).
2. Generalize to `V` where possible; keep `ℕ` for decidability-dependent proofs.

**Module mapping (proposed):**

| `popl27/` source | `CasualQIF/` target |
|---|---|
| `Counterexample.lean` | `DSeparation/Counterexample.lean` |
| `Trail/Basic/BayesBall.lean` | `DSeparation/Path/BayesBall.lean` |
| `TraceSynthesis/*` | `DSeparation/Synthesis/*` |
| `ActiveRoute.lean` | `DSeparation/Path/ActiveRoute.lean` |
| `Reverse.lean` | Absorbed into Synthesis pipeline |

*Last updated: 2026-05-20. Reflects discovery of complete Act 1 + Act 2 code in popl27/.*

# Debt 1 — Deriving `FactorizesOverDAG` from Product Factorization

**Date:** 2026-05-20
**Status:** Design note, not implemented. Valid as a strategy after the 2026-05-20 corrections below.
**Layer:** Act 3 (QIF application layer). Does not affect Acts 1–2 (bisimulation core).
**Companion:** `20260520_paper_repitch.md`, `20260520_debt2_dual_witness.md`.

> **Note (2026-05-20):** Under the 3-act paper reframing, this debt is an
> application-layer hypothesis in the QIF pipeline (Act 3), not a gap in the
> core graph-semantic bisimulation (Acts 1–2). The bisimulation,
> counterexample, and decompiler are self-contained and fully proved regardless
> of whether this debt is closed.

> **Validity review (2026-05-20):** The diagnosis is correct: the current
> `FactorizesOverDAG` is a semantic Global Markov hypothesis, not product
> factorization. The execution target below must be sharpened, however: the
> main leakage theorem needs the **four-variable conditional Markov premise**
> `Probability.condMarkov (pmf_from_vars P cut)`, not only the older
> three-variable `IsMarkovChain` bridge.

---

## What Debt 1 actually is

*Note: This gap is tracked as an open problem in [README.md:L237](file:///Users/ostensible_paradox/Documents/neurips26/verification/README.md#L237) of the `neurips26/verification` repository, under [FiniteQuerySandbox/MarkovGenerator.lean](file:///Users/ostensible_paradox/Documents/neurips26/verification/FiniteQuerySandbox/MarkovGenerator.lean).*

Inspecting `CausalQIF/CausalModel/Factorization.lean`:

```lean
abbrev CondIndepPredicate (Ω : Type) [Fintype Ω] [DecidableEq Ω]
    (V : Type) [DecidableEq V] [Fintype V] :=
  Probability.FinitePMF Ω → Finset V → Finset V → Finset V → Prop

def FactorizesOverDAG {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    {V : Type} [DecidableEq V] [Fintype V]
    (G : Graph.DAG V) (CI : CondIndepPredicate Ω V)
    (P : Probability.FinitePMF Ω) : Prop :=
  ∀ X Y Z : Finset V, DSeparation.dSeparates G X Y Z → CI P X Y Z
```

`FactorizesOverDAG` is **not** product factorization. It **is** the Global
Markov Property stated as an assumption: "d-separation implies the CI
predicate." It is parameterised by whatever `CI` predicate the caller plugs in
(e.g. `isMarkovChainNodeCI`, which itself is a thin pattern-matched adapter).

The in-repo "bridge" `condMutualInfo_eq_zero_of_factorizes_of_dSeparates` is a
near-tautological unwrap of this hypothesis composed with the genuine
information-theoretic fact `condMutualInfo_eq_zero_of_isMarkovChain`. The
d-sep→CI step is **assumed, not derived**.

Debt 1 = derive `FactorizesOverDAG` from a recursive product factorization
`P(V) = ∏_i P(v_i ∣ parents(v_i))`.

## Why the textbook strategy is the hardest possible route

Textbook route is Lauritzen–Verma–Pearl:

1. Define product factorization on `(v : V) → Ω v`.
2. Prove Local Markov: each node ⊥⊥ non-descendants ∣ parents.
3. Prove Local ⇒ Global Markov (d-separation soundness).

Step 3 in full DAG generality is the **ordered-Markov / topological-order /
moralization metatheorem**. This is a mathlib-scale formalization, not a port.
It is exactly the scientific content the old paper deferred on purpose.

## Representation problem — bigger than first sketched

Not merely "flat `α` vs `(v : V) → Ω v`." The **entire downstream zero-sorry
chain** is hardwired to flat tuples:

- `pmf_from_vars : FinitePMF (State × VisibleTrace × MissingTrace) → FinitePMF (State × CutVars × MissingTrace × VisibleTrace)`
- `stateLeakage` defined via masses on `State × VisibleTrace × MissingTrace`.
- All four marginal-mass lemmas in `InformationFlow/CutSetBound.lean`.
- `isMarkovChainNodeCI` pattern-matches the specific singleton sets `{v0}`,
  `{v1}`, `{v2}`.

**Do not retype the QIF core.** It is zero-sorry; perturbing it is pure loss.

## Correct architectural seam

Put product factorization **strictly upstream** of `FactorizesOverDAG`, and
provide a marshalling lemma onto the flat tuple PMF the chain consumes.

```
   ProductFactorizes G P       (new module, on Cfg V Ω := (v : V) → Ω v)
            │ prove ⇒
            ▼
   FactorizesOverDAG G CI P    (was an assumption — becomes a derived lemma)
            │  unchanged
            ▼
   zero-sorry QIF chain         (untouched)
```

Target theorem:

```lean
theorem factorizesOverDAG_of_productFactorizes
    {V : Type} [DecidableEq V] [Fintype V]
    {Ω : V → Type} [∀ v, Fintype (Ω v)] [∀ v, DecidableEq (Ω v)]
    (G : Graph.DAG V) (P : Probability.FinitePMF ((v : V) → Ω v))
    (h : ProductFactorizes G P) :
    FactorizesOverDAG G CI (marshall P)
```

This is a schematic architecture statement, not a Lean-ready theorem: `CI` and
`marshall` must be fixed before implementation. For the current main theorem,
the producer actually needed downstream is one of:

```lean
-- Direct producer for the cut-set DPI theorem.
theorem condMarkov_of_productFactorizes_cut_instance
    ... :
    Probability.condMarkov (pmf_from_vars P cut)
```

or:

```lean
-- Producer for the existing semantic interface.
theorem factorizesOverDAG_condMarkov_of_productFactorizes_cut_instance
    ... :
    FactorizesOverDAG G
      (fun P' _ _ _ => Probability.condMarkov P')
      (pmf_from_vars P cut)
```

The three-variable chain bridge remains useful for the standalone
`condMutualInfo_eq_zero_of_factorizes_of_dSeparates` theorem, but it does not by
itself discharge the four-variable leakage theorem. Nothing downstream in
`InformationFlow/` or `Probability/` should change.

## Two levers — both available, both cheaper than the textbook route

### Lever 1 — Reuse the verified moral-graph engine

The artifact already contains `dSeparated_iff_dSeparates` (fully mechanized at [DSeparation/Equivalence.lean:L134](file:///Users/ostensible_paradox/Documents/popl27/DSeparation/Equivalence.lean#L134)) and the moral-graph
bisimulation. That is **exactly** the separation theory Step 3 needs. Route
factorization → Global Markov *through the existing verified moral-graph
reachability* rather than re-deriving separation. Layer 1 (the paper's current
product) becomes the **engine that discharges Debt 1**. Major structural
payoff for the re-pitch: the bisimulation isn't just a front-end contribution
— it is the lever that closes the Verma–Pearl gap.

Correction for implementation: this theorem is not currently available inside
`CausalQIF`. The `popl27` version is over `ℕ`-labelled DAGs and requires
`DisjointSets X Y Z`. Current `CausalQIF` exports only
`DAG.dSeparated ↔ no MAGWalk`; it does **not** yet export
`DAG.dSeparated ↔ dSeparates`. Therefore Lever 1 requires a real port/adaptation
before it can support a general product-factorization theorem.

### Lever 2 — Instance escape hatch

The paper showcases the linear chain `0 → 1 → 2` (`isMarkovChainNodeCI v0 v1 v2`,
`linear_chain_cut_set_bound_from_dag`). For one fixed small DAG,
*product factorization ⇒ `IsMarkovChain P`* is a **direct computation** — no
general metatheorem. That removes the assumed `FactorizesOverDAG` for the
instance the paper actually claims.

Re-pitch consequence (see `20260520_paper_repitch.md`): the headline can read
**"end-to-end on the showcased instance with factorization derived, not
assumed."** Strictly stronger than the old paper, without overclaiming
generality.

## Decision fork

| Route | Effort | Scope cleared | Risk |
|---|---|---|---|
| **General DAG** | Months. Mathlib-scale ordered-Markov / moralization metatheorem. Or reuse Lever 1, which softens it but is still substantial. | All instances. Debt 1 fully closed. | High — formalisation risk + scope creep. |
| **Instance-restricted (chain `0→1→2`)** | Weeks. Direct computation on the showcased DAG. | Showcased instance only. Headline becomes "factorization derived on instance; general derivation = future work." | Low. Bounded scope. |

## Recommended plan

1. Pick **instance-restricted** for POPL submission.
2. Implement upstream module
   `CausalQIF/CausalModel/ProductFactorization.lean`:
   - `ProductFactorizes_chain3 G v0 v1 v2 P` for the older 3-variable CMI
     bridge.
   - `factorizesOverDAG_isMarkovChain_of_productFactorizes_chain3` proving
     `ProductFactorizes_chain3 ... → FactorizesOverDAG G (isMarkovChainNodeCI v0 v1 v2) P`.
   - A separate leakage-instance producer proving either
     `Probability.condMarkov (pmf_from_vars P cut)` directly, or the
     corresponding `FactorizesOverDAG ... (pmf_from_vars P cut)` premise used
     by `stateLeakage_le_of_factorizes_of_dSeparates_of_cutMutualInfo_le`.
     This can be represented as a four-variable conditional chain
     `X ⟂ Z | Y,W`, or as a three-node chain after collapsing `(Y,W)` into one
     middle variable and transporting by an equivalence.
3. Marshalling: for the 3-variable bridge, state directly on the flat
   `α × β × γ` type; for the leakage theorem, state directly on the flat
   four-variable cut PMF consumed by `pmf_from_vars`.
4. Defer the general theorem to "Future work — general Verma–Pearl mechanization."
5. Open `CausalQIF.CausalModel.ProductFactorization` namespace; do **not** edit
   `Factorization.lean` (preserve current `FactorizesOverDAG` as the existing
   parametric hypothesis interface; new lemma is a *producer* of that
   hypothesis).

## What to NOT do

- Do not redefine `FinitePMF` over dependent configs. The QIF chain depends on
  flat-tuple `FinitePMF`. Independent representation, marshall at the seam.
- Do not edit any file under `CausalQIF/InformationFlow/` or `CausalQIF/Probability/`.
  The zero-sorry chain is load-bearing; perturbing it risks regression.
- Do not chase the general theorem first. Instance lemma first; general theorem
  as future work.

## Honest framing of the closed scope

Even with the instance route, the paper claim is bounded:

- Closed after implementation: on the showcased instance, explicit product
  factorization produces the exact conditional-independence premise consumed by
  the QIF theorem. For the old 3-variable bridge this is
  `ProductFactorizes_chain3 ⇒ IsMarkovChain ⇒ condMutualInfo = 0`; for the
  leakage theorem this must be the four-variable
  `ProductFactorizes_cut_instance ⇒ condMarkov (pmf_from_vars P cut)`.
- Open: general DAG `FactorizesOverDAG`. Listed as future work.

This matches the paper's existing precedent of using the linear chain as the
worked end-to-end instance (`linear_chain_cut_set_bound_from_dag`).

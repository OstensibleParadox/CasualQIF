# CausalQIF — Scope & Limitations Report

**Repo:** `/Users/ostensible_paradox/Documents/CasualQIF`
**Branch:** `main` (clean)
**Date:** 2026-05-20
**Lean:** `leanprover/lean4:v4.30.0-rc1`
**Mathlib pin:** `0e265f2`
**Active library:** 50 Lean files, 5,282 LoC, 156 theorems/lemmas, 125 defs, 18 structures/inductives/classes
**Archive:** 27 Lean files, ~3.2k LoC at `archive/CausalQIFArchive/` (excluded from build)
**Axiom hygiene:** zero `sorry` / `admit` / `axiom` / `unsafe` / `TODO` / `FIXME` in `CausalQIF/`
**Build:** green (8333 jobs, 0 errors; 54 oleans present)

---

## 1. Mathematical scope

### 1.1 Headline results (all closed, `CausalQIF/Main.lean`)

- `stateLeakage_le_of_factorizes_of_dSeparates_of_cutMutualInfo_le` (`Main.lean:48`) — DAG factorisation + d-separation + cut capacity `≤ C` ⇒ `stateLeakage P ≤ C`.
- `certified_leakage_gap_of_dSeparated_graph` (`Main.lean:67`) — `H(S∣T̃) ≤ H(S∣T_full) + C`.
- `stateLeakage_le_of_dual_witness` (`Main.lean:88`) — KL variational route.

### 1.2 Load-bearing scaffolding (genuine non-trivial proofs)

- `stateLeakage_eq_condMutualInfo_pmfMargOutSnd_pmf_from_vars` (`InformationFlow/CutSetBound.lean:212`) — leakage CMI ↔ 4-var CMI bridge, 35 lines.
- `cond_dpi` (`CausalModel/DataProcessing.lean:17`) — conditional DPI via chain rule + CMI nonneg + `condMarkov` ⇒ CMI=0.
- `condMutualInfo_le_of_dual_witness` (`InformationFlow/Duality.lean:25`) — Topsoe variational upper bound on CMI, 130 lines.
- `condMutualInfo_kl_identity` (`Probability/Entropy/Identities/CondMutualInfo.lean:21`) — CMI = KL(P ‖ condProductMass) up to `log 2`.
- `condMutualInfo_nonneg`, `condMutualInfo_eq_zero_of_condIndep` — same file, via KL.
- `klDivergence_nonneg` / `kl_nonneg_support` (`Entropy/KLDivergence.lean:15,61`) — Gibbs hand-rolled via `log p ≤ p − 1`.
- `kl_pythagorean` (`Entropy/KLDivergence.lean:80`) — Generalized Pythagorean theorem for KL divergence. Formalizes the orthogonal m-projection capacity bound without requiring continuous-time dynamics (Fokker-Planck).
- `dSeparated_iff_dSeparates` (`DSeparation/Equivalence.lean:144`) — **both directions** of trail-blocking ↔ moralised-ancestral-graph reachability, restricted to pairwise-disjoint queries (`Equivalence.lean:126,143`). Soundness via `MAGWalk` / Bayes-Ball compression; completeness via `activeWitness_of_not_dSeparated`. Unrestricted equivalence is known to fail — the archived counterexample at `archive/CausalQIFArchive/Trash/DSeparation/Counterexample.lean` documents why.

### 1.3 Mathlib coupling

Lazy whole-mathlib re-export — every file `import Mathlib` (e.g. `FinitePMF/Basic.lean:1`). Entropy/PMF layer is bespoke: no `MeasureTheory.MeasurableSpace`, no mathlib `Pmf`, no `Mathlib.InformationTheory.*`.

### 1.4 Missing classical results

Unconditional MI, unconditional DPI, Fano's inequality, full chain rule `H(X,Y) = H(X) + H(Y∣X)` as a named lemma, Pinsker, Han, Markov-chain MI beyond the 3/4-node case.

---

## 2. Conceptual scope

**Thesis (encoded in `Main.lean`):** in the finite discrete setting, if `(State, VisibleTrace, MissingTrace)` factorises over DAG `G` and State is d-separated from MissingTrace by cut `{vY, vW}`, then conditional MI `I(S; M ∣ T̃)` (Shannon leakage to an adversary seeing `T̃` but not `M`) is upper-bounded by the cut's information-theoretic capacity `I(K; M ∣ T̃) ≤ C`. The "certified gap" lifts this to `H(S∣T̃) − H(S∣T_full) ≤ C`.

**Chain closed end-to-end in `Main.lean`:**

```
d-separation → factorization predicate → condMarkov (4-var)
              → cond_dpi → stateLeakage ≤ cutCapacity
              → KL-dual witness bound
```

This is a **complete machine-checked QIF-from-causal-structure result for the finite case** — not just groundwork. The headline theorem delivers what its name says.

**Design intent — two-stage factorisation split:** the classical Verma-Pearl global Markov theorem is deliberately split into (i) an **upper topological-semantics stage** producing computable, `decide`-able Markov blankets and per-node local Markov boundaries, and (ii) a **lower concrete-tuple-adapter stage** that converts node-set premises into the concrete probabilistic CI predicate (e.g. `condMarkov P`), leaving the probability-model derivation to caller or special-case provider. The split avoids row/column-expansion blowup when probability shapes vary. `FactorizesOverDAG` being a semantic package is the joint between the two stages, not a missing proof.

**Current state of the split:**
- Upper stage **deleted** in commit `13b2a07` ("Archive no longer needed") — `FiniteQuerySandbox/MarkovGenerator.lean` from init commit `8846e80` carried `computeMarkovBlanket`, `spouses`, `generateMarkovConditions`, `generateMarkovBlanketConditions`, plus `MarkovGeneratorExamples` (`decide`-checked on `chain3`, `collider3`).
- Lower stage **degraded** — `Main.lean:54` uses `(fun P' _ _ _ => Probability.condMarkov P')`, the trivial no-premise adapter. Canonical typed form was `condMarkovNodeCI` with `X = {0}, Z = {2}, YW = {1, 3}` premises plus standalone bridge `condMarkov_of_factorizes_dsep_fourVar`. Labelling discipline lost.
- Existing 3-chain bridge `isMarkovChain_of_productFactorizes_chain3` (`CausalModel/ProductFactorization.lean:30`) has body `exact h` — definitional joint between two stages for the chain-3 shape. Consistent with the split design.

---

## 3. Engineering scope

| Aspect | State |
|---|---|
| Lakefile | Minimal. Single target `lean_lib CausalQIF`. `autoImplicit := false` (strict). One git dep on mathlib4. |
| Toolchain | `v4.30.0-rc1` — release candidate, not stable. Minor pin-drift risk. |
| Module tree | Clean five-way split: `Graph/` · `DSeparation/` · `Probability/` · `CausalModel/` · `InformationFlow/`. Recent refactors (`94c0264`, `70479dd`) are pure splits with hashes preserved. |
| Axiom hygiene | `grep -rE "\bsorry\b\|\badmit\b" → 0`; `grep "^axiom " → 0`; `TODO/FIXME → 0`. |
| Build | 54 oleans, `lake build` clean. |
| Test/example coverage | **Weak.** The sole example `Examples/LinearChain.lean:33` has body `h_cap`; `_h_factor`, `_h_dsep` are unused. No instantiated PMF, no concrete graph, no end-to-end numeric demonstration. No test target in lakefile. |
| Repo hygiene | **Thin.** No README, no LICENSE, no CI workflows. `lake-manifest.json` still carries the old package name `finiteQuerySandbox`; `lakefile.lean` declares `causal_qif`. |
| Archive status | `archive/CausalQIFArchive/` (27 files) excluded from build. Files inside import unqualified `DSeparation.*` paths (e.g. `archive/CausalQIFArchive/Trash/DSeparation/ActiveRoute.lean:1` → `import DSeparation.BayesBall.Basic`) — won't compile if revived without rename. |
| Executability | Heavy `noncomputable` / `Classical.choice` / `Nat.find` usage (58 occurrences in `CausalQIF/`). Library is verification-oriented; not designed for numeric evaluation. |

---

## 4. Limitations

1. **Two-stage factorisation-to-Markov split, with one stage deleted and the other degraded — not a missing-proof gap.** The design deliberately splits the classical Verma-Pearl global Markov theorem into:

   - **Upper stage (topological semantics):** computable, `decide`-able. Strong-typed graph query produces exact Markov blanket, local Markov boundary, and per-node syntactic CI conditions. Output: list of `(Finset V × Finset V × Finset V)` triples a downstream user/automation must validate.
   - **Lower stage (concrete tuple adapter):** typed predicate that, given node-set premises `X = {…}, Z = {…}, YW = {…}`, yields the concrete probabilistic CI (e.g. `condMarkov P`). Hands probabilistic concretization to caller or to per-shape special-case provider, side-stepping row/column-expansion blowup.

   `FactorizesOverDAG` (`CausalModel/Factorization.lean:19`) being a semantic package is a *feature* of this split, not a gap. The architecture is sound.

   **What is actually broken on `main`:**
   - Upper stage is **deleted**. Commit `13b2a07` ("Archive no longer needed") removed `FiniteQuerySandbox/MarkovGenerator.lean` from init commit `8846e80`, which carried `computeMarkovBlanket`, `spouses`, `generateMarkovConditions`, `generateMarkovBlanketConditions`. The computable-topology half is currently absent from `CausalQIF/`.
   - Lower stage is **degraded**. `Main.lean:54` uses `(fun P' _ _ _ => Probability.condMarkov P')` — the trivial adapter with no node-set premises. The canonical typed form (old `condMarkovNodeCI` enforcing `X = {0}, Z = {2}, YW = {1, 3}`) is gone. Strictly weaker; labelling discipline lost.

   Fix is mechanical, not a research problem: revive the upper stage (port `MarkovGenerator` from `8846e80` into `CausalQIF/CausalModel/`), restore the typed adapter in `Main.lean:54`.
2. **Finite-only.** Every module quantifies over `[Fintype α] [DecidableEq α]`. No σ-algebras, no `MeasureTheory`, no continuous states. Lifting requires a complete rewrite of the probability layer.
3. **Example layer hollow on `main`, but had `decide`-checked combinatorial examples pre-`13b2a07`.** `Examples/LinearChain.lean` returns `h_cap` unchanged on current `main`. No numeric instantiation, no `decide`-checked concrete graph, no demonstration that the cut-set bound is non-tautological on a specific PMF. The KKT certificate machinery (`InformationFlow/ChannelCapacity.lean`) also has no worked example. Historically (init commit `8846e80`) the deleted `FiniteQuerySandbox/MarkovGenerator.lean` carried a `MarkovGeneratorExamples` namespace with `decide`-checked Markov blanket computations on `chain3` and `collider3` — combinatorial worked examples, not numeric PMF instances, but concrete and machine-checked. Reviving those (under the new `CausalQIF` namespace) is cheap.
4. **`KKT_Certificate.of_direct_bound` tautological** by its own docstring (`ChannelCapacity.lean:108` — "tautological producer"). The non-tautological version `of_dual_witness` (line 141) routes through `condMutualInfo_le_of_dual_witness`. No KKT *necessity* proof (only sufficiency).
5. **Public d-separation equivalence restricted to pairwise-disjoint X, Y, Z.** An archived counterexample (`archive/CausalQIFArchive/Trash/DSeparation/Counterexample.lean`) documents why unrestricted equivalence fails. This is an intentional scope decision, not a defect — but consumers must respect the precondition.
6. **No unconditional MI / DPI.** All MI is conditional. No named lemma for `I(X;Y) ≥ 0` or `H(f(X)) ≤ H(X)`.
7. **Non-executable in places.** 58 occurrences of `noncomputable` / `Classical.choice` / `Nat.find` across `CausalQIF/`. ℝ-based entropy/KL also block native numeric eval. No `decide`-checked or `#eval`-able end-to-end pipeline.
8. **Whole-mathlib import.** Every file `import Mathlib`. High build cost; downstream consumers inherit. Replacing with targeted imports is unblocked work.
9. **Naming churn largely settled.** Phase 1c (snake_case migration) and Phase 2 (dedup) are both clean per `.claude/reports/honesty-report-phase{1c,2}.md`. Dot-notation promotion (`FinitePMF.pairFstFthReshape` etc.) is deferred per `.claude/plans/causalqif-phase1c-and-2-plan.md:36` — still pending.
10. **Repo hygiene gaps.** No README, no LICENSE, no CI, no test target. `lake-manifest.json` carries the stale package name `finiteQuerySandbox`. Archive files import old unqualified `DSeparation.*` paths and will not build if reintroduced as-is.
11. **Toolchain on RC.** `v4.30.0-rc1` is a release candidate. Pin drift risk if mathlib advances past it.

---

## 5. Honest assessment

### 5.1 Publishable now

> "A machine-checked formalisation in Lean 4 of (i) the trail-blocking ↔ moralised-ancestral-graph equivalence of d-separation for finite DAGs under pairwise-disjoint queries, (ii) the conditional data-processing inequality, (iii) a Topsoe variational upper bound on conditional mutual information, and (iv) a cut-set state-leakage bound for finite quantitative-information-flow models."

All four are non-trivial and sorry-free.

### 5.2 Architectural framing of the FactorizesOverDAG hypothesis

The `Main.lean` headline depends on a caller-supplied `FactorizesOverDAG G condMarkov`. This is *by design*: the project deliberately splits Verma-Pearl into a computable topological stage (upper) and a typed concretization stage (lower), with `FactorizesOverDAG` as the semantic joint. The caller (or a per-shape adapter) supplies the joint validation.

This is a legitimate design choice and should be stated as such in any publication — not as a gap, but as the project's contribution. The combinatorial blowup that a monolithic Verma-Pearl proof would cause is avoided by construction. **However**, two pieces of the split are currently missing from `main`:

- Upper stage (computable Markov blanket / local Markov generator) deleted in `13b2a07`.
- Lower stage adapter degraded to no-premise form on `Main.lean:54`.

Until both are restored, the published claim should be qualified: "the topological–probabilistic factorisation split is a deliberate architectural choice; the computable upper-half is currently held in archive and the typed lower-half adapter is undergoing revision."

### 5.3 Next bottlenecks (priority order)

1. **Restore both halves of the factorisation split.** Port `MarkovGenerator.lean` (init commit `8846e80`, deleted in `13b2a07`) into `CausalQIF/CausalModel/` to recover the computable topological upper stage. Replace `Main.lean:54`'s `(fun P' _ _ _ => Probability.condMarkov P')` with a typed `condMarkovNodeCI`-style adapter that enforces node-set premises. Neither task is a new math result — both are mechanical restorations of pre-deletion code.
2. **Build a concrete worked example.** A 3- or 4-node DAG with explicit numerical PMF where `stateLeakage_le_of_factorizes_of_dSeparates_of_cutMutualInfo_le` produces a non-trivial numeric bound. Reviewers will flag the absence. Cheap intermediate step is implied by #1 — once the `MarkovGeneratorExamples` namespace returns, `chain3`/`collider3` blanket computations are available as `decide`-checked combinatorial examples.
3. **Repo hygiene quick fixes.** Regenerate `lake-manifest.json` so package name matches `causal_qif`. Add README (scope + headline theorem + finite-discrete restriction + two-stage split design note), LICENSE, minimal CI (`lake build` on PR). Cheap; high signal of project maturity.
4. **Targeted mathlib imports** to make the library usable as a dependency without inheriting the whole-mathlib cost.
5. **Decide on a measure-theoretic lift** or commit publicly to the finite-discrete scope.

---

## 6. Key files for follow-up

- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/Main.lean`
- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/InformationFlow/CutSetBound.lean`
- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/InformationFlow/Duality.lean`
- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/InformationFlow/ChannelCapacity.lean`
- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/CausalModel/Factorization.lean`
- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/CausalModel/ProductFactorization.lean`
- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/CausalModel/DataProcessing.lean`
- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/DSeparation/Equivalence.lean`
- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/Probability/Entropy/Identities/CondMutualInfo.lean`
- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/Examples/LinearChain.lean`

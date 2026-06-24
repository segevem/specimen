# Specimen Modularity

Specimen derives generators, enumerators, and checkers from inductive relations.
The derivation pipeline has several axes where behavior can be swapped, extended,
or overridden. This document maps those axes and identifies opportunities for
further modularization.

---

## Current modular axes

### 1. Scoring (fully pluggable)

The scoring framework is the primary modularity success story. Users define a new
score type, implement `Scorable S`, and register a `ScorerBundle`:

```
Scorable S  →  mkScorerBundle  →  registerScoringBundle "myScore"
```

Selected at build time via `set_option specimen.scoreType "myScore"`.

Four independently-replaceable layers compose bottom-up:

| Layer | Signature | Role |
|-------|-----------|------|
| StepScorer | `ScheduleStep → S` | Score one hypothesis step |
| ScheduleScorer | `List S → S` | Fold step scores into a constructor score |
| LeafAggregator | `List S → S` | Combine constructor scores within a coverage-trie leaf |
| InductiveAggregator | `List S → S` | Combine leaf scores across the whole inductive |

Each bundle also declares a `PruneStrategy` controlling branch-and-bound aggressiveness.

### 2. Typeclass instances (user-provided overrides)

Users can hand-write `ArbitrarySizedSuchThat`, `EnumSizedSuchThat`, or `DecOpt`
instances for any sub-relation. If Lean's typeclass resolution finds a
user-provided instance, Specimen uses it instead of deriving one. This is the
primary escape hatch for domain-specific generation strategies.

### 3. Configuration options

| Option | Effect |
|--------|--------|
| `specimen.scoreType` | Active scoring strategy |
| `specimen.multiOutput` | Multi-output production steps |
| `specimen.fuel` | Termination budget |
| `specimen.autoDeriveDeps` | Auto-derive dependency instances |
| `specimen.searchLimit` | Cap on orderings explored per constructor |
| `specimen.richOutput` / `specimen.textOutput` | Output format |

### 4. Mutual derivation

`derive_mutual` co-derives multiple specs that can call each other, allowing
users to decompose complex relations into mutually-recursive pieces.

---

## Opportunities for further modularity

### A. Combinator strategy (how generated code retries)

**Current state:** The code-generation backend hardcodes `backtrack` (try all
constructors) for generators and `enumerate` (lazy-list concat) for enumerators.
The constructor selection strategy is not pluggable.

**What could be modular:**

| Strategy | Behavior | When useful |
|----------|----------|-------------|
| `backtrack` (current) | Try all constructors in random order | Shallow recursion, few dead ends |
| `frequency` (commit-or-fail) | Pick one constructor probabilistically, restart on failure | Deep recursion (Boltzmann-style) |
| `enumerate-within-generate` | Locally enumerate an auxiliary step's outputs before failing the constructor | Auxiliary generators with many dead-end outputs |

A `CombinatorStrategy` parameter on `DeriveSort` (or per-constructor via the
scorer) would let the code generator emit different retry logic without changing
the schedule.

### B. Search algorithm (how orderings are explored)

**Current state:** SCC decomposition → SearchTree (lazy rose tree of
dependency-satisfying orderings) → branch-and-bound with scorer. The search
*structure* is fixed; only the objective function is pluggable.

**What could be modular:**

- **Exploration order within the tree.** Currently depth-first. A best-first or
  beam-search variant could find good schedules faster for relations with many
  hypotheses.
- **Dominance pruning.** Currently compares environments by score. A pluggable
  dominance relation could incorporate structural properties (e.g., "same
  variable-binding set reached via fewer checks always dominates").
- **Termination criterion.** Currently `searchLimit` count. Could instead be
  time-bounded, or stop when score hasn't improved for N iterations.

### C. Code-generation backend (what Lean syntax is emitted)

**Current state:** `MakeConstrainedProducerInstance` emits fixed patterns of
`Gen` or `Enumerator` monad code for each `ScheduleStep`.

**What could be modular:**

- **Target monad.** Today it's either `Gen` or `LazyList`-based. A pluggable
  backend could target other monads (e.g., a probability monad for coverage
  analysis, or a tracing monad for debugging).
- **Step compilation.** Each `ScheduleStep` compiles to a fixed syntax template.
  A hook allowing custom step kinds (or custom compilation of existing steps)
  would enable domain-specific optimizations without modifying the core compiler.

### D. Coverage analysis (how input space is partitioned)

**Current state:** `PatternCoverage` builds a trie that partitions the input
space by constructor patterns. The trie structure is fixed (refine on each
input argument's top constructor).

**What could be modular:**

- **Refinement depth.** Currently refines to a fixed depth. A budget-based or
  information-gain-based refinement policy could focus coverage analysis on the
  most interesting regions.
- **Coverage metric.** The trie labels each leaf with which constructors cover
  it. How to *interpret* that (is one covering constructor enough? do we want
  uniform distribution?) is currently baked into the scorer's leaf aggregator.
  Separating the coverage *semantics* from the scoring would let the trie be
  reused for other purposes (e.g., shrinking guidance, mutation targets).

### E. Dependency resolution (how sub-relations are obtained)

**Current state:** When the scheduler encounters a sub-relation, it either finds
an existing typeclass instance or (if `autoDeriveDeps` is set) recursively
derives one. The derivation uses the same scorer and settings as the parent.

**What could be modular:**

- **Per-dependency configuration.** A sub-relation might benefit from a different
  scorer or different `multiOutput` setting than the parent. Currently there's no
  way to express "derive `HasTypeArith` with scorer X but `HasTypeIf` with
  scorer Y."
- **Instance source.** Beyond typeclass resolution and auto-derivation, instances
  could come from a user-provided registry, a cache of previously-derived
  instances, or a foreign function interface (e.g., calling an SMT solver for
  arithmetic constraints).

### F. Runtime adaptation (dynamic tuning during generation)

**Current state:** All decisions are made at derive-time. The generated code uses
fixed weights and a fixed strategy at runtime.

**What could be modular:**

- **Adaptive constructor weights.** The scorer computes static `ctorWeight`
  values. At runtime, the generator could track success rates and shift weight
  toward constructors that produce valid outputs more often.
- **Size policy.** Size currently decrements by 1 at each recursive call. A
  pluggable size policy could implement Boltzmann-style size allocation, or
  split size budgets unevenly across sub-expressions based on type complexity.

---

## Design principles for adding modularity

1. **Typeclass + registry pattern.** Scoring demonstrates the pattern: define a
   typeclass for the abstraction, wrap in a type-erased bundle, register by name,
   select via `set_option`. This works well for anything that varies per-project
   but not per-constructor.

2. **Per-constructor annotations.** For things that should vary within a single
   derivation (combinator strategy, size policy), the scorer already has
   per-step visibility. Extending the schedule representation with annotations
   (rather than adding new options) keeps the configuration local to where it
   matters.

3. **Don't break the pipeline.** The schedule representation (`ScheduleStep`) is
   the narrow waist between the search algorithm and the code generator.
   Modularity above or below this interface is safer than changing the interface
   itself. New step kinds require changes to both search and codegen.

4. **Compose, don't configure.** Where possible, prefer composable pieces
   (a combinator strategy *is* a function, not a flag) over configuration
   switches that interact in complex ways.

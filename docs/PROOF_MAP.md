# Proof map

The selected public interface is `HamiltonicityOracle.query` plus four theorem targets. Its independent statement is `HamParity/RegistryChallenge.lean`; the Solution never imports Challenge. RegistryModel contains the identical fixed mathematical model. RegistryBridge proves representation transports to the substantive development.

| Layer | Principal modules | Obligation discharged |
|---|---|---|
| CNF semantics and gates | CNF, Gate, Circuit, Counting, FullAdder | Actual clauses, unique deterministic helper extensions, exact model counts |
| Component colors | ComponentColors, GraphColors, ComponentEnumeration, GraphColorCNF | Rooted component-constant color count, with component enumeration derived from finite graphs |
| Graph selections and cycles | EdgeSelection, GeneralGraphCounting, GeneralGraphParity, CycleGraph, CycleSelectionCompleteness | Degree-two selections, unrestricted-degree row encoders, disjoint helpers, and cyclic-order soundness/completeness |
| Arithmetic | WeightedRipple, RippleArithmetic, RippleBucketCNF, CarrySave, HeapTripleSearch, HeapCompression, HeapWidth, DenseHeapRows, WeightedBucket | Concrete carry-save normalization, terminal addition, retained carry, target pins and width/size bounds |
| Graph/filter composition | WeightedGraphCounting, WeightedGraphMeaning, WeightedGraphSize | Shared edge identities, edge-only weights and exact filtered color multiplicities |
| Survival | BinaryPolynomial, CycleMonomials, MultilinearPolynomial, GlobalSurvival, CycleSurvival | Nonzero cycle polynomial from a witness, no oriented/rotated duplicates, finite palette survival and an odd bucket |
| Finite decision and amplification | FiniteBucketDecision, IndependentTrials, DecisionAmplification, FairBitDigits, FairBitGrid, ScheduleBounds, ScheduleDecision | Inclusive bucket range, independent trials, fair-bit bijections, error and explicit resource counts |
| Public interface | RegistryModel, RegistryBridge, RegistrySolution, RegistryAudit | Four exact statement proofs and permitted-axiom closure checks |

Module names are file stems in `HamParity/`. Read their imports for the exact dependency graph; the public source checker emits that graph. The copied proof closure is substantive source, not a thin wrapper around an unavailable repository. The package does not use Mathlib or an external counting implementation.

## Statement-to-artifact map

| Public theorem | Meaning | Status |
|---|---|---|
| `query_exact_count` | Emitted CNF count equals independently defined filtered edge/color count | Lean checked and installed Comparator/default-kernel accepted |
| `query_size` | Width ≤3 and stated V/M bounds for the same queries | Same |
| `fair_sample_space` | Complete duplicate-free sample space and exact cardinality | Same |
| `finite_oracle_reduction` | One-sided finite oracle guarantee, failure ≤1/3 and scan-slot bound | Same |

The fuller conditional algorithm manuscript is intentionally outside this candidate. External-counter composition, machine runtime/space, executable sampling/serialization costs and witness recovery are not among these four claims. Supporting canonical-encoding modules in the source tree do not close that external bridge. The separate local-certification lower-bound paper is not included or represented as formalized here.

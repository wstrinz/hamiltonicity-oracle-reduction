# Exact finite theorem

All logarithms in the following bounds are base two. Let n be the vertex count and m the number of indexed undirected edges. Vertices are `Fin n`; an edge list is a function `Fin m → Fin n × Fin n`. Simplicity forbids loops and repeated undirected edges, including reversed duplicates. A root is an explicit element of `Fin n`. A Hamiltonian witness is a duplicate-free spanning cyclic list of length at least three, with every consecutive and closing pair adjacent.

Set

\[
r=\lfloor\sqrt{n-1}\rfloor,\quad L=\max(1,\operatorname{bitlength}(r)),\quad
D=2^L,\quad K=2\cdot4^D,
\]

where natural subtraction is truncated and bitlength(0)=0. Let

\[
b=2(r+1)+\lfloor\log_2(m+1)\rfloor+1.
\]

## The actual query

For every indexed input E, root, exponent assignment w and natural target t, `query E root w t` supplies a declared variable count and a concrete CNF. Its model count counts **every assignment to every declared variable**, even unused variables. It equals the number of pairs (s,c) such that:

1. s selects exactly two incident edges at each vertex;
2. the binary color c is zero at the root and equal across every selected edge;
3. the edge-only integer sum `Σ_e 2^(w(e)) s(e)` equals t.

No helper assignment multiplicity is assumed away: the compiler's deterministic helpers have proved unique extensions. Colors are counted. Exponents are fixed wiring parameters, not extra model variables. This identity is `HamiltonicityOracle.query_exact_count` and requires no simplicity or n≥3 premise beyond the supplied root.

If every exponent is less than D, `query_size` proves, for every target t,

\[
V\le28m+2n+2+5b,\qquad M\le108m+6n+19b+4,
\]

and every clause has width at most three. V and M refer to that same emitted formula, not a surrogate encoding.

## Random input and oracle

Each trial is m blocks of L Boolean bits, decoded little-endian into the D palette values without rejection. There are K trials. `fair_sample_space` proves the complete sample list is duplicate-free, contains exactly the K-trial descriptions, and has cardinality `2^(K*m*L)`. Probability is the uniform finite counting ratio on that list.

The oracle hypothesis `Exact oracle` says: for every declared finite CNF query q, the oracle returns its exact nonnegative integer model count. It is not a SAT, approximate-count, parity-only or time-bound oracle assumption. The procedure uses parity of the returned integer.

For each trial, test every integer bucket from 0 through `n*2^(D-1)`, inclusive. Accept if any returned count is odd.

## Main result

`HamiltonicityOracle.finite_oracle_reduction` assumes E is simple, supplies a root, assumes n≥3 and an exact oracle. It proves:

- acceptance on any trial-description list implies a Hamiltonian witness;
- if E is Hamiltonian, the rejection probability on the uniform K-trial sample space is at most 1/3;
- on every sample, prescribed full-scan slots equal `K*(n*2^(D-1)+1)` and are at most `(n+1)*2^(6*r+7)`.

`run` is a finite Boolean disjunction. `calls` counts prescribed scan slots; short-circuit evaluation may use fewer. The exact bit-description length is K*m*L. This is a finite distribution and count theorem, not an efficient random-source implementation or a machine-operation count.

The theorem does not assert that every positive input has odd unfiltered count. Distinct Hamiltonian edge sets can cancel in parity. The proved random weighted-bucket survival bridge supplies the positive-instance guarantee.

The authoritative definitions and quantifiers are in [RegistryChallenge.lean](../HamParity/RegistryChallenge.lean). The four compared theorems are proved in [RegistrySolution.lean](../HamParity/RegistrySolution.lean). All use only propext, Quot.sound and, where needed, Classical.choice.

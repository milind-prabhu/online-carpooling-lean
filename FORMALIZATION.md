# Online carpooling: Lean formalization

Formalization of results in **The Cube-Root Phenomenon in Online Carpooling**,
Nikhil Bansal, Milind Prabhu, Sahil Singla, and Siddharth M. Sundaram,
[arXiv:2609.21348v1](https://arxiv.org/abs/2609.21348v1).

**Status: all three main theorems are proved in explicit finite forms, including
both stochastic upper bounds and the stochastic lower bound for every admissible
vertex count in its logarithmic-degree regime. The lower theorem includes actual
regular graph construction, nondivisible vertex counts, real-log cube-root scaling,
a vanishing-error modulus, and finite randomized mixtures.**

Every project module builds in Lean 4.24.0. There are no admitted proofs, custom axioms,
or native-decision shortcuts. The transitive axiom audit reports only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`. See `Audit.lean` and `VERIFICATION.txt`.

## Interactive dependency blueprint

Open [the standalone proof blueprint](blueprint/generated/Online_Carpooling_Blueprint.html)
for a PFR-style clickable dependency graph. The overview has 33 nodes; the full view
has all 420 explicitly named source declarations. Click a node to inspect its compiled
Lean statement, source and proof dependencies. Detailed deterministic, stochastic-upper,
and stochastic-lower views are included, along with PDF, SVG and PNG exports.

Arrows are extracted from compiled Lean types and proof terms, with omitted helper
paths collapsed and transitive redundant arrows removed. They are not module-import
arrows. Green marks checked project declarations; mathlib and foundational dependencies
are outside the displayed graph. See [the blueprint documentation](blueprint/README.md)
for the precise extraction method and rebuild commands.

## Results and declarations

| Paper result / proof ingredient | Lean declaration | File |
| --- | --- | --- |
| Weighted Greedy dynamics, arbitrary tie rules | `Move`, `Run`, `Request`, `states` | `Basic.lean`, `Requests.lean` |
| Lemma 3.4, top-sum evolution | `topSum_step` | `TopSums.lean` |
| Lemma 3.3, spreadness | `spreadness` | `Spreadness.lean` |
| Lemma 3.2, positive quadratic potential | `potential_bound` | `Potential.lean` |
| Lemma 3.1, expanding-move bound with constant 4 | `lemma_3_1` | `UpperBounds.lean` |
| Theorem 1.1, every vertex and prefix | `theorem_1_1` | `UpperBounds.lean` |
| Actual Greedy recurrence | `greedy_requests_upper_bound` | `Requests.lean` |
| Lemma 4.2, tree-like requests | `lemma_4_2`, `tree_like_surplus_bound` | `TreeLike.lean` |
| Single-component surplus identity and bound | `Run.local_surplus_identity`, `local_tree_like_bound` | `LocalTreeLike.lean` |
| Graph-respecting witness cover, retaining multiplicities | `Run.component_witness` | `WitnessCover.lean` |
| Spanning-tree extraction from a witness | `Witness.spanning` | `WitnessForest.lean` |
| Witness enumeration, equation (6) | `Witness.families_card_bound` | `WitnessCounting.lean` |
| Multiset occurrence probability, equation (7) | `occurrence_probability_bound` | `FiniteProbability.lean` |
| Refined witness enumeration and cover | `refined_witness_probability`, `refined_cover_of_forest` | `RefinedWitnesses.lean`, `StochasticRefined.lean` |
| Basic stochastic tail and high-probability estimate | `stochastic_upper_tail`, `stochastic_basic_high_probability` | `StochasticBasic.lean` |
| Refined stochastic tail | `stochastic_refined_tail` | `StochasticRefined.lean` |
| Explicit degree-dependent threshold | `stochastic_refined_high_probability` | `RefinedThresholds.lean` |
| Stochastic bounds on mathlib regular simple graphs | `regular_graph_stochastic_basic`, `regular_graph_stochastic_refined` | `RegularGraphs.lean` |
| Linear-horizon batching, basic and refined | `regular_graph_stochastic_batched`, `regular_graph_stochastic_refined_batched` | `RegularGraphs.lean` |
| Discrepancy of every global batched prefix | `aggregate_bound_outside_bad_event`, `refined_aggregate_bound` | `Batched.lean`, `RefinedBatched.lean` |
| Theorem 1.2, one good event controlling every chronological prefix | `theorem_1_2_basic`, `theorem_1_2_refined` | `StochasticTheorem.lean` |
| Theorem 1.2 for the actual batched Greedy recurrence | `theorem_1_2_basic_greedy`, `theorem_1_2_refined_greedy` | `StochasticTheorem.lean` |
| Greedy causality (agreement on earlier requests implies equal state) | `states_prefix_congr` | `StochasticTheorem.lean` |
| Equal-position pigeonhole argument and quadratic-potential growth for arbitrary orientations | `equal_pair_of_bounded_integer_positions`, `equal_endpoint_lower_bound` | `LowerBound.lean` |
| Causal adversarial cube-root lower bound, discrepancy h within 4h³ requests | `adversarial_lower_bound_four_cubes`, `lowerStates_prefix_congr` | `LowerBound.lean` |
| Exact probability of matching adaptive prescriptions, including at selected sampling times | `adaptive_matching_probability`, `selected_matching_probability` | `AdaptiveProbability.lean` |
| Local stochastic lower bound for every causal algorithm on an actual complete graph | `clique_local_lower_probability` | `LocalStochasticLower.lean` |
| Small forced vertex set inside a larger graph | `embedded_local_lower_probability` | `EmbeddedLower.lean` |
| Second-moment amplification of globally adaptive prescriptions | `pairwise_event_amplification`, `adaptive_prescription_amplification` | `Amplification.lean` |
| Lower-bound potential with idle times, and first-L cutoff construction | `charged_potential_lower_bound`, `exists_prefix_cut` | `ChargedLower.lean`, `PrefixCuts.lean` |
| Conditional stochastic lower bound for interleaved cliques, targeting any populated subset | `scheduled_targets_lower_probability_of_counts` | `ScheduledLower.lean` |
| Fixed-horizon occupancy variance and enough-populated-cliques probability | `occupancy_variance`, `few_good_labels_probability` | `Occupancy.lean` |
| Finite averaging over arrival schedules | `uniformProb_mixture_bound` | `FiniteMixtures.lean` |
| Unconditional lower bound in the product sampling model | `iid_cliques_lower_probability` | `StochasticLower.lean` |
| Actual regular disjoint-clique graph and exact uniform edge-sampling equivalence | `disjointCliques_regular`, `cliqueSampleEquiv` | `DisjointCliques.lean` |
| Unconditional lower bound on actual iid graph-edge requests | `regular_cliques_stochastic_lower` | `RegularGraphLower.lean` |
| Explicit cubic/logarithmic lower-bound threshold and failure at most 10/N | `regular_cliques_lower_logarithmic` | `LowerThresholds.lean` |
| Regular graph existence for every admissible size/degree | `exists_regular_graph` | `RegularExistence.lean` |
| Weighted sampling, padding and the lower bound for nondivisible vertex counts | `padded_graph_stochastic_lower`, `padded_graph_lower_logarithmic` | `PaddedLower.lean`, `PaddedThresholds.lean` |
| Theorem 1.3 / 4.3, all parameters, with real-log cube-root scaling | `theorem_1_3`, `StochasticLowerGuarantee` | `FinalLower.lean`, `OnlineLower.lean` |
| Explicit vanishing-error modulus and randomized mixtures | `theorem_1_3_with_error`, `randomized_lower_bound` | `LowerCorollaries.lean` |

All file names in the table are under `Carpooling/`.

## Exact stochastic statements

The code uses integer binary logarithms to make rounding and finite-size assumptions explicit:

- `Nat.clog 2 x` is the ceiling binary logarithm.
- `Nat.log 2 x` is the floor binary logarithm.
- Division in the definition of `p` below is natural-number division.

Let `n = Fintype.card V`, and consider a batch of `B` independent uniform edge samples,
with replacement, from a nonempty regular simple graph of degree `Δ`. Assume `16*B ≤ n`.
Define

```text
L = Nat.clog 2 (2*n^2)
p = 24 * Nat.clog 2 n / Nat.log 2 Δ + 1
```

The basic bound is **discrepancy at most `4*L^(1/3)` at every prefix**, except on an event
of probability at most `1/n`.

For the refined bound, assume additionally

```text
256 ≤ Δ
L^3 ≤ Δ
```

Then **discrepancy is at most `4*p^(1/3) + 2*Nat.log 2 L` at every prefix**, except on an
event of probability at most `3/n`.

These are explicit finite versions of the paper's `O((log n)^(1/3))` and
`O((log n / log Δ)^(1/3) + log log n)` rates. The concrete degree cutoff fixes a sufficient
constant in the paper's `Δ = Ω((log n)^3)` condition. The Lean statements expose the integer
thresholds and cutoffs rather than expressing the conclusion using real-log Big-O notation.

There is also a more general, parameterized refined tail bound, for arbitrary natural `L,p`:

```text
Pr[discrepancy > 4*p^(1/3) + 2*Nat.log 2 L]
  ≤ 2*n / 2^L + 2*n * (L^2 / (8*Δ))^p.
```

The refined bad event controls every legal weighted subrun supported on a submultiset of the
sampled edges. The proof therefore controls all prefixes and is stronger than just fixing a
request order in advance.

For **K batches**, the failure probabilities are at most `K/n` and `3*K/n`, respectively.
The global discrepancy is bounded by K times the corresponding one-batch bound. The
aggregate lemmas represent global chronological prefixes by cutoffs: the full batch length
for completed batches, a prefix length for the current batch, and zero for future batches.
For constant K and a batch length proportional to n, this gives a linear total horizon.

The online algorithm restarts its *local* Greedy state at each batch boundary; the actual
signed discrepancies add over batches. The code does not identify this batched algorithm
with one uninterrupted global Greedy run.

The end-to-end `theorem_1_2_basic_greedy` and `theorem_1_2_refined_greedy` each
produce a single good event with probability at least `1-K/n` and `1-3K/n`,
respectively. On that event the actual recursive policy `batchedGreedyState`
satisfies the corresponding bound at every global time and vertex. The chronological
cutoff for batch j at time t is `min B (t-j*B)`, so completed batches contribute
their final discrepancy and future batches contribute zero. The only request
compatibility assumptions assert adjacency in G and equality of the request edge
multiset with the sample. They contain no component, tail, or discrepancy assumption.
The proved prefix-congruence lemma verifies that local Greedy states depend only on
earlier requests; the probability event is uniform over adaptive weights and tie choices.

## Sampling, weights, and model scope

Probability is represented exactly as `#bad / #sample_space` on the finite type of edge
sequences. Uniform sampling of a function `Fin B → G.edgeSet` is precisely independent
uniform sampling with replacement. The occurrence proofs count distinct sampling times,
so repeated edge labels never get treated as independent copies of one time slot.

The upper-bound bad events quantify over all compatible legal Greedy runs, including all tie choices
and all real weights in `[0,1]`. Thus adaptive weights are covered; the proof does not assume
that weights are independent of the samples. The universal quantification even permits
weights or request reorderings chosen after all samples have been seen.

The exported regular-graph theorems use mathlib's `SimpleGraph`, `IsRegularOfDegree`, and
actual edge set. The degree-sum identity is derived in `regular_edge_balance`. Neither a
witness cover nor a component probability estimate is an input assumption of those theorems.
Empty sampling edge sets are excluded because a uniform edge sample would not be defined.

In the upper-bound model, vertices form an arbitrary finite type; positions and weights are real numbers. A move has
two distinct endpoints, adds the weight at the lower position, subtracts it at the higher
position, and leaves all other coordinates unchanged. Zero weights are allowed.

## Proof correspondence

The deterministic proof follows the positive quadratic potential and top-r spreadness
argument, with the small-discrepancy and zero-expansion cases handled explicitly. It proves
`|d_t(i)| ≤ min(4*t^(1/3), n)` at every prefix.

The tree-like proof uses a verified extension allowing coordinate decreases between legal
moves. This replaces the auxiliary sink's bookkeeping. It shifts positions by twice the
**floor binary logarithm** of component sizes. Merging requests are uncharged; only internal
requests can contribute to the cubic term. The local identity counts those requests as
exactly `edges - (vertices - 1)` in each final component.

The stochastic proof constructs and reroots witness forests, preserving their full edge
multisets. It counts graph-respecting labelings through Catalan tree shapes, proves the
fixed-pattern occurrence bound, and applies finite union bounds. For refined witnesses,
a spanning tree is extracted inside the full witness, and each surplus edge is encoded by
two indices among the core tree's vertices. The cover and all counting estimates are proved.

## Build and audit

Pinned versions:

- Lean `v4.24.0`.
- mathlib `v4.24.0`, commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
- Transitive dependency revisions in `lake-manifest.json`.

With Lean installed through elan:

```bash
bash bootstrap.sh
bash check.sh
```

Or, after dependencies and caches are available:

```bash
lake build
lake env lean Audit.lean
```

The archive contains source, dependency revisions, provenance hashes, and verification
output. Downloaded mathlib sources and build products are excluded.

## Lower bounds now proved

`adversarial_cubic_lower_bound` constructs an adaptive unit-weight adversary on
`2*h+2` vertices. For every `h > 0` and every sequence of orientation choices,
some vertex has integer absolute discrepancy at least h by time `(2*h+2)*h^2`.
`adversarial_lower_bound_four_cubes` gives the simpler horizon `4*h^3`.
The construction uses only previous orientation choices, as verified by
`lowerStates_prefix_congr`. No Greedy ordering assumption is made: either
orientation of an equal-discrepancy pair raises the quadratic potential by two.
The result holds pathwise for every realized sequence of randomized choices.

The adaptive probability lemmas use independent uniform samples from a finite
alphabet E. A prescription at time t can depend on the entire preceding sample
prefix. The probability of matching at every time in an arbitrary fixed set I
is exactly `1 / (#E)^I.card`; the other sampling times remain unrestricted.
The proof constructs a bijection between matching sample sequences and the
unrestricted coordinates. This avoids assuming independence of the prescriptions.

`clique_local_lower_probability` considers an arbitrary causal online algorithm
on the complete graph with `2*h+2` vertices and T iid uniform edge arrivals.
If `(2*h+2)*h^2 < 2*T`, the probability of attaining discrepancy h at some
prefix is at least `1 / (choose(2*h+2,2))^T`. The algorithm supplies only legal
unit-weight updates, the identity of the sampled edge, zero initialization,
and prefix causality. No deterministic or probabilistic lower bound is a premise.

The new embedding theorem allows the small `2*h+2` vertex set to lie inside
an arbitrarily larger graph. Its likelihood uses the full ambient edge alphabet
size q, whereas its horizon remains `(2*h+2)*h^2 < 2*T`.

For K disjoint sets of L sampling times, `adaptive_prescription_amplification`
proves a failure probability at most `q^L/K`. All prescriptions can depend on
the full earlier chronological sample history. The proof derives pairwise
intersection probabilities from the selected-coordinate counting bijection,
then proves and applies a finite second-moment inequality. Mutual independence
of clique events is not assumed.

`scheduled_targets_lower_probability_of_counts` connects those estimates to
actual unit-weight orientation runs on vertices `J × U`, where J indexes
cliques. Fix any schedule of which clique receives each global request. If K
chosen cliques each receive at least L requests, and
`(2*h+2)*h^2 < 2*L`, then the probability of failing to reach discrepancy h
anywhere is at most `q^L/K`. Here local edge labels are iid uniform from E,
`q = #E`, and E encodes edges on U containing a complete forced set of size
`2*h+2`. The algorithm can use global history across all cliques. It supplies
only legal updates, correct sampled-edge identities, zero initialization,
and causality. First-L cutoffs and forcing events are constructed in the proof.
Other cliques and subsequent arrivals remain in the run; no assumption that
all cliques are sufficiently populated is needed. For a clique of degree Δ,
the natural local alphabet has `q = choose(Δ+1,2)`.

## Unconditional stochastic lower bound now proved

Let the graph consist of M disjoint cliques of size N. It has n = MN vertices
and is (N-1)-regular, as proved using mathlib's `SimpleGraph` model. Consider
exactly n iid uniform graph-edge arrivals, with unit weights, and any causal
online orientation algorithm. The sample-space bijection and uniform sampling
identification are proved, rather than assumed as probability hypotheses.

For any forced discrepancy h and number of local requests L satisfying

```text
2*h+2 ≤ N
2*L ≤ N
(2*h+2)*h^2 < 2*L
```

`regular_cliques_stochastic_lower` proves that the probability of never reaching
discrepancy h is at most

```text
8/N + 2*(choose(N,2))^L/M.
```

The finite theorem `regular_cliques_lower_logarithmic` sets
`L = (h+1)*h^2+1` and derives the more convenient conclusion: for M>0, h>0,

```text
6*h^3 ≤ N
12*h^3 ≤ Nat.log N M
```

imply failure probability at most `10/N`. Thus integer h of cube-root order
in `log_N M` is attained with high probability as N tends to infinity, under
the displayed degree/size cutoff. `Nat.log N M` is the floor logarithm in base N;
the theorem states all finite thresholds directly, rather than using real-log
Big-Omega notation. In the nontrivial small-degree regime, `log_N M` has the
same order as the paper's `log n / log Δ`. The final all-parameter theorem
below proves the real-log rate comparison directly.

The occupancy proof works at the fixed horizon MN. Each clique receives N
requests in expectation and has variance at most N. Chebyshev's inequality
gives probability at most 4/N of receiving fewer than L requests; a first-moment
bound gives probability at most 8/N that fewer than half the cliques are
sufficiently populated. Averaging the checked conditional lower bound over
all schedules gives the displayed unconditional estimate. This route does
not require Poissonization or a random-horizon transfer.

## Completed all-parameter stochastic lower bound

The final declaration is `Carpooling.theorem_1_3`. For natural parameters n, Δ, a,
its complete numerical assumptions are

```text
2 ≤ Δ < n
(n*Δ) % 2 = 0
48 ≤ a
6 * Nat.log 2 n ≤ a*(Δ+1)
```

It constructs a finite simple graph G with **exactly n vertices**, regular of
**degree Δ**, and an integer h>0, before quantifying over the online algorithm.
For every causal unit-weight orientation rule receiving exactly n independent
uniform graph-edge requests, the probability of never reaching absolute
vertex discrepancy h is at most `10/(Δ+1)`. The same h satisfies

```text
(log n / log Δ)^(1/3) ≤ (64*a)^(1/3) * h.
```

Here `log` is the real natural logarithm. Consequently the attained discrepancy
is at least `(64*a)^(-1/3) * (log n/log Δ)^(1/3)`. The rate constant depends only
on the fixed scale parameter a. The assumption involving `Nat.log 2 n` is an
explicit constant version of Δ=Ω(log n); every such degree sequence admits a
fixed sufficiently large a for all sufficiently large n.

`theorem_1_3_with_error` makes the `1-o(1)` probability quantitative: for any
k>0, the additional condition `2^(2*a*k) ≤ n` guarantees failure probability
at most `1/k`, using the same rate constant. No limit notation or unproved
concentration assumption is needed in this finite statement.

The graph consists of M full cliques of size N=Δ+1 and a remainder of size
`N + n % N`, with `M = n/N-1`. The remainder has an explicitly proved
Δ-regular circulant construction: paired positive/negative jumps, plus an
antipodal jump when Δ is odd. Parity of its required degree sum is derived
from the admissibility of (n,Δ). Its size lies in [N,2N), so this construction
handles all divisibility cases. Weighted occupancy estimates and a sampler
with constant-size fibers establish the uniform graph-edge probability law.
When the cubic threshold is below one, the first unit request supplies the
required constant discrepancy, covering the large-degree regime.

`UnitOnlineRule` bundles only zero initialization, legal unit updates, correct
sampled-edge identities, and dependence on earlier requests. It contains no
discrepancy or probability assumption. `randomized_lower_bound` proves the
same probability bound for arbitrary finite normalized nonnegative mixtures
of these rules, allowing nonuniform independent random seeds. At a finite
horizon, distributions over deterministic finite-history policies have this
form. The main proof also holds uniformly for each fixed random seed.

The project uses finite probability ratios throughout. The paper's Poissonization
argument is replaced by the checked fixed-horizon occupancy argument; a separate
Poisson-process formalization is not required for any exported main theorem.
The asymptotic claims are represented by the stronger explicit thresholds,
real-log inequality, and vanishing-error modulus above. The pinned paper
version is identified in the introduction and provenance file.

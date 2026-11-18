import Carpooling.Batched
import Carpooling.RefinedBatched
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace Carpooling
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma regular_edge_balance (G : SimpleGraph V) [DecidableRel G.Adj]
    {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) :
    2 * Fintype.card G.edgeSet = Fintype.card V * Δ := by
  calc
    2 * Fintype.card G.edgeSet = ∑ v, G.degree v := by
      simpa only [G.edgeFinset_card] using G.sum_degrees_eq_twice_card_edges.symm
    _ = Fintype.card V * Δ := by
      calc
        (∑ v, G.degree v) = ∑ _v : V, Δ := sum_congr rfl (fun v _ => hreg v)
        _ = _ := by simp

/-- Basic stochastic upper bound on an actual regular simple graph, including repeated sampling.
No component, witness-cover, or probability estimate is a hypothesis. -/
theorem regular_graph_stochastic_basic (G : SimpleGraph V)
    [DecidableRel G.Adj] [Nonempty G.edgeSet]
    {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) (hpos : 0 < Δ)
    (T : ℕ) (hT : 16*T ≤ Fintype.card V) (hn : 0 < Fintype.card V) :
    uniformProb (badDiscrepancyEvent (fun v => G.neighborFinset v) (fun e : G.edgeSet => e.val) T
      (stochasticThreshold (Fintype.card V))) ≤ 1 / (Fintype.card V : ℝ) := by
  apply stochastic_basic_high_probability (fun v => G.neighborFinset v)
    (fun v => by rw [G.card_neighborFinset_eq_degree, hreg v]) hpos
    (fun {u v} hv => by simpa only [G.mem_neighborFinset] using G.symm ((G.mem_neighborFinset u v).mp hv))
    (fun e : G.edgeSet => e.val) Subtype.val_injective (regular_edge_balance G hreg) T hT hn

/-- Batched form for a linear total number of requests. The failure bound is K/n,
and the global discrepancy bound supplied by `aggregate_bound_outside_bad_event`
is `4*K*(clog 2 (2*n^2))^(1/3)`. -/
theorem regular_graph_stochastic_batched (G : SimpleGraph V)
    [DecidableRel G.Adj] [Nonempty G.edgeSet]
    {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) (hpos : 0 < Δ)
    (K B : ℕ) (hB : 16*B ≤ Fintype.card V) (hn : 0 < Fintype.card V) :
    uniformProb (badBatchEvent (fun v => G.neighborFinset v) (fun e : G.edgeSet => e.val) K B
      (stochasticThreshold (Fintype.card V))) ≤ (K : ℝ) / Fintype.card V := by
  apply stochastic_batched_high_probability (fun v => G.neighborFinset v)
    (fun v => by rw [G.card_neighborFinset_eq_degree, hreg v]) hpos
    (fun {u v} hv => by simpa only [G.mem_neighborFinset] using G.symm ((G.mem_neighborFinset u v).mp hv))
    (fun e : G.edgeSet => e.val) Subtype.val_injective (regular_edge_balance G hreg) K B hB hn

/-- Semantic reading of the bad-discrepancy event. Its complement certifies every prefix
for every compatible weighted Greedy run, uniformly over all weight assignments. -/
theorem bound_outside_bad_discrepancy {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
    {T L : ℕ} (N : V → Finset V) (g : E → Sym2 V) (x : Fin T → E)
    (hx : x ∉ badDiscrepancyEvent N g T L) (R : Run V T)
    (hi : ∀ k, R.d 0 k = 0)
    (hAdj : ∀ s (hs : s < T), (R.step s hs).v ∈ N (R.step s hs).u)
    (hbag : R.edgeBag T = sampleBag g x) {t : ℕ} (ht : t ≤ T) (k : V) :
    |R.d t k| ≤ 4*(L : ℝ)^((1:ℝ)/3) := by
  by_contra hn
  apply hx
  exact mem_filter.mpr ⟨mem_univ _, R, hi, hAdj, hbag, t, ht, k, lt_of_not_ge hn⟩

/-- Refined degree-dependent stochastic bound on a regular simple graph.
The integer-log formulation fixes all constants and finite-size cutoffs. -/
theorem regular_graph_stochastic_refined (G : SimpleGraph V)
    [DecidableRel G.Adj] [Nonempty G.edgeSet]
    {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) (hpos : 0 < Δ)
    (T : ℕ) (hT : 16*T ≤ Fintype.card V) (hn : 0 < Fintype.card V)
    (hlarge : 256 ≤ Δ) (hdegree : (stochasticThreshold (Fintype.card V))^3 ≤ Δ) :
    uniformProb (badRefinedEvent (fun v => G.neighborFinset v) (fun e : G.edgeSet => e.val) T
      (stochasticThreshold (Fintype.card V)) (refinedThreshold (Fintype.card V) Δ)) ≤
      3/(Fintype.card V:ℝ) := by
  exact stochastic_refined_high_probability (fun v => G.neighborFinset v)
    (fun v => by rw [G.card_neighborFinset_eq_degree,hreg v]) hpos
    (fun {u v} hv => by simpa only [G.mem_neighborFinset] using G.symm ((G.mem_neighborFinset u v).mp hv))
    (fun e : G.edgeSet => e.val) Subtype.val_injective (regular_edge_balance G hreg) T hT hn hlarge hdegree

/-- Refined form for K batches, hence a linear total number of arrivals.
The failure probability is at most 3K/n. -/
theorem regular_graph_stochastic_refined_batched (G : SimpleGraph V)
    [DecidableRel G.Adj] [Nonempty G.edgeSet]
    {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) (hpos : 0 < Δ)
    (K B : ℕ) (hB : 16*B ≤ Fintype.card V) (hn : 0 < Fintype.card V)
    (hlarge : 256 ≤ Δ) (hdegree : (stochasticThreshold (Fintype.card V))^3 ≤ Δ) :
    uniformProb (badRefinedBatchEvent (fun v => G.neighborFinset v) (fun e : G.edgeSet => e.val) K B
      (stochasticThreshold (Fintype.card V)) (refinedThreshold (Fintype.card V) Δ)) ≤
      3*K/(Fintype.card V:ℝ) := by
  exact stochastic_refined_batched_probability (fun v => G.neighborFinset v)
    (fun v => by rw [G.card_neighborFinset_eq_degree,hreg v]) hpos
    (fun {u v} hv => by simpa only [G.mem_neighborFinset] using G.symm ((G.mem_neighborFinset u v).mp hv))
    (fun e : G.edgeSet => e.val) Subtype.val_injective (regular_edge_balance G hreg) K B hB hn hlarge hdegree

end Carpooling

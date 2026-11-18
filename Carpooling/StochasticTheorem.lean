import Carpooling.RegularGraphs
import Carpooling.Requests

/-! End-to-end finite versions of Theorem 1.2. A single exceptional event
controls every chronological prefix, every compatible request order, and all
adaptive weights. Greedy is restarted locally at each batch boundary. -/
namespace Carpooling
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Number of requests from batch j processed by global time t. -/
def batchCutoff (B t : ℕ) (j : ℕ) : ℕ := min B (t - j*B)

lemma batchCutoff_le (B t j : ℕ) : batchCutoff B t j ≤ B := min_le_left _ _

lemma batchCutoff_before {B t j : ℕ} (h : t ≤ j*B) : batchCutoff B t j = 0 := by
  simp [batchCutoff, Nat.sub_eq_zero_of_le h]

lemma batchCutoff_after {B t j : ℕ} (h : (j+1)*B ≤ t) : batchCutoff B t j = B := by
  unfold batchCutoff
  apply min_eq_left
  rw [Nat.add_mul] at h
  omega

/-- Actual total signed discrepancy of the locally restarted Greedy policy.
Only the first `batchCutoff B t j` requests of batch j affect this state. -/
noncomputable def batchedGreedyState {K : ℕ} (B : ℕ)
    (q : Fin K → ℕ → Request V) (t : ℕ) (v : V) : ℝ :=
  ∑ j, states (q j) (batchCutoff B t j.val) v

omit [Fintype V] in
/-- Causality: no request at time t or later affects the state at time t. -/
lemma states_prefix_congr (q q' : ℕ → Request V) (t : ℕ)
    (h : ∀ s < t, q s = q' s) : states q t = states q' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [states]
    rw [h t (Nat.lt_succ_self t), ih (fun s hs => h s (Nat.lt_succ_of_lt hs))]

omit [Fintype V] in
lemma Request.move_adj (G : SimpleGraph V) (q : Request V) (x : V → ℝ)
    (h : G.Adj q.a q.b) : G.Adj (q.move x).u (q.move x).v := by
  by_cases hx : x q.a ≤ x q.b
  · simpa [Request.move, hx] using h
  · simpa [Request.move, hx] using G.symm h

lemma uniformProb_compl {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (A : Finset Ω) : uniformProb (univ \ A) = 1 - uniformProb A := by
  have hcard : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hle : A.card ≤ Fintype.card Ω := card_le_univ A
  simp only [uniformProb, card_sdiff, inter_univ, card_univ]
  rw [Nat.cast_sub hle, sub_div, div_self (ne_of_gt hcard)]

/-- Basic Theorem 1.2 with explicit constants. The same good event works
simultaneously for all legal runs and every global time. -/
theorem theorem_1_2_basic (G : SimpleGraph V)
    [DecidableRel G.Adj] [Nonempty G.edgeSet]
    {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) (hpos : 0 < Δ)
    (K B : ℕ) (hB : 16*B ≤ Fintype.card V) (hn : 0 < Fintype.card V) :
    ∃ good : Finset (Fin K → Fin B → G.edgeSet),
      1 - (K:ℝ)/(Fintype.card V:ℝ) ≤ uniformProb good ∧
      ∀ x ∈ good, ∀ R : Fin K → Run V B,
        (∀ j v, (R j).d 0 v = 0) →
        (∀ j s (hs : s < B), G.Adj ((R j).step s hs).u ((R j).step s hs).v) →
        (∀ j, (R j).edgeBag B = sampleBag (fun e : G.edgeSet => e.val) (x j)) →
        ∀ t v, |∑ j, (R j).d (batchCutoff B t j.val) v| ≤
          (K:ℝ)*(4*(stochasticThreshold (Fintype.card V):ℝ)^((1:ℝ)/3)) := by
  let bad := badBatchEvent (fun v => G.neighborFinset v) (fun e : G.edgeSet => e.val)
    K B (stochasticThreshold (Fintype.card V))
  refine ⟨univ \ bad, ?_, ?_⟩
  · rw [uniformProb_compl bad]
    have h := regular_graph_stochastic_batched G hreg hpos K B hB hn
    change uniformProb bad ≤ _ at h
    linarith
  · intro x hx R hi hAdj hbag t v
    exact aggregate_bound_outside_bad_event _ _ x (mem_sdiff.mp hx).2 R hi
      (fun j s hs => (G.mem_neighborFinset _ _).mpr (hAdj j s hs)) hbag
      (fun j => batchCutoff B t j.val) (fun j => batchCutoff_le _ _ _) v

/-- Refined Theorem 1.2, with the logarithmic thresholds and all finite-size
conditions explicit. No component or witness estimate is assumed. -/
theorem theorem_1_2_refined (G : SimpleGraph V)
    [DecidableRel G.Adj] [Nonempty G.edgeSet]
    {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) (hpos : 0 < Δ)
    (K B : ℕ) (hB : 16*B ≤ Fintype.card V) (hn : 0 < Fintype.card V)
    (hlarge : 256 ≤ Δ) (hdegree : (stochasticThreshold (Fintype.card V))^3 ≤ Δ) :
    ∃ good : Finset (Fin K → Fin B → G.edgeSet),
      1 - 3*(K:ℝ)/(Fintype.card V:ℝ) ≤ uniformProb good ∧
      ∀ x ∈ good, ∀ R : Fin K → Run V B,
        (∀ j v, (R j).d 0 v = 0) →
        (∀ j s (hs : s < B), G.Adj ((R j).step s hs).u ((R j).step s hs).v) →
        (∀ j, (R j).edgeBag B = sampleBag (fun e : G.edgeSet => e.val) (x j)) →
        ∀ t v, |∑ j, (R j).d (batchCutoff B t j.val) v| ≤
          (K:ℝ)*(4*(refinedThreshold (Fintype.card V) Δ:ℝ)^((1:ℝ)/3) +
            2*(Nat.log 2 (stochasticThreshold (Fintype.card V)):ℝ)) := by
  let bad := badRefinedBatchEvent (fun v => G.neighborFinset v) (fun e : G.edgeSet => e.val)
    K B (stochasticThreshold (Fintype.card V)) (refinedThreshold (Fintype.card V) Δ)
  refine ⟨univ \ bad, ?_, ?_⟩
  · rw [uniformProb_compl bad]
    have h := regular_graph_stochastic_refined_batched G hreg hpos K B hB hn hlarge hdegree
    change uniformProb bad ≤ _ at h
    linarith
  · intro x hx R hi hAdj hbag t v
    exact refined_aggregate_bound _ _ x (mem_sdiff.mp hx).2 R hi
      (fun j s hs => (G.mem_neighborFinset _ _).mpr (hAdj j s hs)) hbag
      (fun j => batchCutoff B t j.val) (fun j => batchCutoff_le _ _ _) v

/-- The basic result for the actual recursive online policy. -/
theorem theorem_1_2_basic_greedy (G : SimpleGraph V)
    [DecidableRel G.Adj] [Nonempty G.edgeSet]
    {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) (hpos : 0 < Δ)
    (K B : ℕ) (hB : 16*B ≤ Fintype.card V) (hn : 0 < Fintype.card V) :
    ∃ good : Finset (Fin K → Fin B → G.edgeSet),
      1 - (K:ℝ)/(Fintype.card V:ℝ) ≤ uniformProb good ∧
      ∀ x ∈ good, ∀ q : Fin K → ℕ → Request V,
        (∀ j s, s < B → G.Adj (q j s).a (q j s).b) →
        (∀ j, (runRequests (q j) B).edgeBag B =
          sampleBag (fun e : G.edgeSet => e.val) (x j)) →
        ∀ t v, |batchedGreedyState B q t v| ≤
          (K:ℝ)*(4*(stochasticThreshold (Fintype.card V):ℝ)^((1:ℝ)/3)) := by
  obtain ⟨good, hp, hb⟩ := theorem_1_2_basic G hreg hpos K B hB hn
  refine ⟨good, hp, ?_⟩
  intro x hx q hAdj hbag t v
  exact hb x hx (fun j => runRequests (q j) B) (fun _ _ => rfl)
    (fun j s hs => (q j s).move_adj G _ (hAdj j s hs)) hbag t v

/-- The refined result for the actual recursive online policy, rather than
an abstract run. The bag equality only identifies the arrivals with the
sampled edges; no probabilistic or discrepancy premise is supplied. -/
theorem theorem_1_2_refined_greedy (G : SimpleGraph V)
    [DecidableRel G.Adj] [Nonempty G.edgeSet]
    {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) (hpos : 0 < Δ)
    (K B : ℕ) (hB : 16*B ≤ Fintype.card V) (hn : 0 < Fintype.card V)
    (hlarge : 256 ≤ Δ) (hdegree : (stochasticThreshold (Fintype.card V))^3 ≤ Δ) :
    ∃ good : Finset (Fin K → Fin B → G.edgeSet),
      1 - 3*(K:ℝ)/(Fintype.card V:ℝ) ≤ uniformProb good ∧
      ∀ x ∈ good, ∀ q : Fin K → ℕ → Request V,
        (∀ j s, s < B → G.Adj (q j s).a (q j s).b) →
        (∀ j, (runRequests (q j) B).edgeBag B =
          sampleBag (fun e : G.edgeSet => e.val) (x j)) →
        ∀ t v, |batchedGreedyState B q t v| ≤
          (K:ℝ)*(4*(refinedThreshold (Fintype.card V) Δ:ℝ)^((1:ℝ)/3) +
            2*(Nat.log 2 (stochasticThreshold (Fintype.card V)):ℝ)) := by
  obtain ⟨good, hp, hb⟩ := theorem_1_2_refined G hreg hpos K B hB hn hlarge hdegree
  refine ⟨good, hp, ?_⟩
  intro x hx q hAdj hbag t v
  exact hb x hx (fun j => runRequests (q j) B) (fun _ _ => rfl)
    (fun j s hs => (q j s).move_adj G _ (hAdj j s hs)) hbag t v

end Carpooling

import Carpooling.StochasticBasic

namespace Carpooling
open Finset
open scoped Classical
variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Nonempty E]

noncomputable def badBatchEvent (N : V → Finset V) (g : E → Sym2 V) (K B L : ℕ) :
    Finset (Fin K → Fin B → E) :=
  univ.biUnion fun j => evaluationEvent (badDiscrepancyEvent N g B L) j

/-- The probability estimate for any fixed number of subcritical batches.
Taking a constant K permits a linear total number K*B of requests. -/
theorem stochastic_batched_high_probability (N : V → Finset V) {Δ : ℕ}
    (hΔ : ∀ v, (N v).card ≤ Δ) (hpos : 0 < Δ)
    (hsymm : ∀ {u v}, v ∈ N u → u ∈ N v)
    (g : E → Sym2 V) (hg : Function.Injective g)
    (hbalance : 2 * Fintype.card E = Fintype.card V * Δ)
    (K B : ℕ) (hB : 16*B ≤ Fintype.card V) (hn : 0 < Fintype.card V) :
    uniformProb (badBatchEvent N g K B (stochasticThreshold (Fintype.card V))) ≤
      (K : ℝ) / Fintype.card V := by
  have h := batch_failure_bound (K := K)
    (badDiscrepancyEvent N g B (stochasticThreshold (Fintype.card V)))
  have hp := stochastic_basic_high_probability N hΔ hpos hsymm g hg hbalance B hB hn
  calc
    _ ≤ (K : ℝ) * uniformProb (badDiscrepancyEvent N g B (stochasticThreshold (Fintype.card V))) := h
    _ ≤ (K : ℝ) * (1/(Fintype.card V : ℝ)) := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
    _ = _ := by ring

/-- Global discrepancies add over completed batches and the current batch.
Every chronological prefix is represented by cutoffs: B for completed batches,
the current position for one batch, and zero for the future batches. -/
theorem aggregate_bound_outside_bad_event {K B L : ℕ} (N : V → Finset V) (g : E → Sym2 V)
    (x : Fin K → Fin B → E) (hx : x ∉ badBatchEvent N g K B L)
    (R : Fin K → Run V B)
    (hi : ∀ j k, (R j).d 0 k = 0)
    (hAdj : ∀ j s (hs : s < B), ((R j).step s hs).v ∈ N ((R j).step s hs).u)
    (hbag : ∀ j, (R j).edgeBag B = sampleBag g (x j))
    (cutoff : Fin K → ℕ) (hcut : ∀ j, cutoff j ≤ B) (k : V) :
    |∑ j, (R j).d (cutoff j) k| ≤ (K : ℝ) * (4*(L : ℝ)^((1:ℝ)/3)) := by
  have hlocal : ∀ j, |(R j).d (cutoff j) k| ≤ 4*(L : ℝ)^((1:ℝ)/3) := by
    intro j
    by_contra hn
    have hjbad : x j ∈ badDiscrepancyEvent N g B L := by
      apply mem_filter.mpr
      exact ⟨mem_univ _, R j, hi j, hAdj j, hbag j, cutoff j, hcut j, k, lt_of_not_ge hn⟩
    apply hx
    apply mem_biUnion.mpr
    exact ⟨j, mem_univ _, mem_filter.mpr ⟨mem_univ _, hjbad⟩⟩
  calc
    |∑ j, (R j).d (cutoff j) k| ≤ ∑ j, |(R j).d (cutoff j) k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin K, 4*(L : ℝ)^((1:ℝ)/3) := sum_le_sum fun j _ => hlocal j
    _ = _ := by simp

end Carpooling

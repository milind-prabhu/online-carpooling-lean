import Carpooling.RefinedThresholds

namespace Carpooling
open Finset
open scoped Classical
variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Nonempty E]

noncomputable def badRefinedBatchEvent (N : V → Finset V) (g : E → Sym2 V) (K B L p : ℕ) :
    Finset (Fin K → Fin B → E) :=
  univ.biUnion fun j => evaluationEvent (badRefinedEvent N g B L p) j

theorem stochastic_refined_batched_probability (N : V → Finset V) {Δ : ℕ}
    (hΔ : ∀ v, (N v).card ≤ Δ) (hpos : 0 < Δ)
    (hsymm : ∀ {u v}, v ∈ N u → u ∈ N v)
    (g : E → Sym2 V) (hg : Function.Injective g)
    (hbalance : 2 * Fintype.card E = Fintype.card V * Δ)
    (K B : ℕ) (hB : 16*B ≤ Fintype.card V) (hn : 0 < Fintype.card V)
    (hlarge : 256 ≤ Δ) (hdegree : (stochasticThreshold (Fintype.card V))^3 ≤ Δ) :
    uniformProb (badRefinedBatchEvent N g K B (stochasticThreshold (Fintype.card V))
      (refinedThreshold (Fintype.card V) Δ)) ≤ 3*K/(Fintype.card V:ℝ) := by
  have h := batch_failure_bound (K := K)
    (badRefinedEvent N g B (stochasticThreshold (Fintype.card V)) (refinedThreshold (Fintype.card V) Δ))
  have hp := stochastic_refined_high_probability N hΔ hpos hsymm g hg hbalance B hB hn hlarge hdegree
  calc
    _ ≤ (K:ℝ)*uniformProb (badRefinedEvent N g B (stochasticThreshold (Fintype.card V))
      (refinedThreshold (Fintype.card V) Δ)) := h
    _ ≤ (K:ℝ)*(3/(Fintype.card V:ℝ)) := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
    _ = _ := by ring

theorem refined_bound_outside_bad_event {T L p : ℕ} (N : V → Finset V) (g : E → Sym2 V)
    (x : Fin T → E) (hx : x ∉ badRefinedEvent N g T L p) (R : Run V T)
    (hi : ∀ k, R.d 0 k = 0)
    (hAdj : ∀ s (hs : s < T), (R.step s hs).v ∈ N (R.step s hs).u)
    (hbag : R.edgeBag T ≤ sampleBag g x) {t : ℕ} (ht : t ≤ T) (k : V) :
    |R.d t k| ≤ 4*(p:ℝ)^((1:ℝ)/3) + 2*(Nat.log 2 L:ℝ) := by
  by_contra hn
  apply hx
  apply mem_filter.mpr
  refine ⟨mem_univ _,t,ht,R.prefix t ht,hi,?_,?_,k,lt_of_not_ge hn⟩
  · intro s hs; exact hAdj s (lt_of_lt_of_le hs ht)
  · rw [R.edgeBag_prefix ht (le_refl t)]
    exact (R.edgeBag_mono ht).trans hbag

/-- A deterministic certificate for every global prefix of the batched online algorithm. -/
theorem refined_aggregate_bound {K B L p : ℕ} (N : V → Finset V) (g : E → Sym2 V)
    (x : Fin K → Fin B → E) (hx : x ∉ badRefinedBatchEvent N g K B L p)
    (R : Fin K → Run V B) (hi : ∀ j k, (R j).d 0 k = 0)
    (hAdj : ∀ j s (hs : s < B), ((R j).step s hs).v ∈ N ((R j).step s hs).u)
    (hbag : ∀ j, (R j).edgeBag B = sampleBag g (x j))
    (cutoff : Fin K → ℕ) (hcut : ∀ j, cutoff j ≤ B) (k : V) :
    |∑ j, (R j).d (cutoff j) k| ≤ (K:ℝ)*(4*(p:ℝ)^((1:ℝ)/3)+2*(Nat.log 2 L:ℝ)) := by
  have hlocal : ∀ j, |(R j).d (cutoff j) k| ≤ 4*(p:ℝ)^((1:ℝ)/3)+2*(Nat.log 2 L:ℝ) := by
    intro j
    apply refined_bound_outside_bad_event N g (x j) _ (R j) (hi j) (hAdj j) (le_of_eq (hbag j)) (hcut j) k
    intro hj
    apply hx
    exact mem_biUnion.mpr ⟨j,mem_univ _,mem_filter.mpr ⟨mem_univ _,hj⟩⟩
  calc
    |∑ j, (R j).d (cutoff j) k| ≤ ∑ j, |(R j).d (cutoff j) k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin K, (4*(p:ℝ)^((1:ℝ)/3)+2*(Nat.log 2 L:ℝ)) := sum_le_sum fun j _ => hlocal j
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]

end Carpooling

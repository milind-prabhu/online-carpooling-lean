import Carpooling.UpperBounds

namespace Carpooling
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- No arrival crosses C. Every component of the sampled multigraph has this property. -/
def Run.Closed {T : ℕ} (R : Run V T) (C : Finset V) : Prop :=
  ∀ t (ht : t < T), (R.step t ht).u ∈ C ↔ (R.step t ht).v ∈ C

/-- Ignore moves outside C by replacing their weight by zero. -/
noncomputable def Run.mask {T : ℕ} (R : Run V T) (C : Finset V)
    (hC : R.Closed C) : Run V T where
  d := fun t k => if k ∈ C then R.d t k else 0
  step := fun t ht => by
    let e := R.step t ht
    have hc : e.u ∈ C ↔ e.v ∈ C := hC t ht
    refine ⟨e.u, e.v, e.distinct, if e.u ∈ C then e.weight else 0, ?_, ?_, ?_, ?_⟩
    · split_ifs <;> linarith [e.weight_nonneg]
    · split_ifs <;> linarith [e.weight_le_one]
    · by_cases hu : e.u ∈ C
      · simp only [if_pos hu, if_pos (hc.mp hu)]; exact e.ordered
      · have hv : e.v ∉ C := fun hv => hu (hc.mpr hv)
        simp [hu, hv]
    · intro k
      by_cases hu : e.u ∈ C
      · have hv := hc.mp hu
        by_cases hk : k ∈ C
        · simp only [if_pos hu, if_pos hk]; exact e.update k
        · have hku : k ≠ e.u := fun h => hk (h ▸ hu)
          have hkv : k ≠ e.v := fun h => hk (h ▸ hv)
          simp [hk, hku, hkv]
      · have hv : e.v ∉ C := fun h => hu (hc.mpr h)
        by_cases hk : k ∈ C
        · have hku : k ≠ e.u := fun h => hu (h ▸ hk)
          have hkv : k ≠ e.v := fun h => hv (h ▸ hk)
          simp only [if_pos hk, if_neg hu]
          simpa [hku, hkv] using e.update k
        · simp [hk, hu]

noncomputable def internalCount {T : ℕ} (R : Run V T) (C : Finset V) (t : ℕ) : ℕ :=
  ((range t).filter fun s => ∃ h : s < T, (R.step s h).u ∈ C).card

lemma mask_expandingCount_le {T : ℕ} (R : Run V T) (C : Finset V)
    (hC : R.Closed C) (t : ℕ) :
    expandingCount (R.mask C hC) t ≤ internalCount R C t := by
  apply card_le_card
  intro s hs
  obtain ⟨hsrange, h, he⟩ := mem_filter.mp hs
  apply mem_filter.mpr
  refine ⟨hsrange, h, ?_⟩
  by_contra hu
  have hv : (R.step s h).v ∉ C := fun hv => hu ((hC s h).mpr hv)
  have : ¬((R.mask C hC).step s h).Expanding := by
    simp [Move.Expanding, Run.mask, hu, hv]
  exact this he

/-- Deterministic ingredient of Theorem 1.2: only arrivals in a closed component count.
No random-graph estimate is assumed to have been proved by this theorem. -/
theorem closed_component_bound {T L : ℕ} (R : Run V T) (C : Finset V)
    (hC : R.Closed C) (hinit : ∀ k, R.d 0 k = 0)
    (hL : internalCount R C T ≤ L) {i : V} (hi : i ∈ C) :
    |R.d T i| ≤ 4 * (L : ℝ)^((1:ℝ)/3) := by
  let M := R.mask C hC
  have hm : ∀ k, M.d 0 k = 0 := by intro k; simp [M, Run.mask, hinit]
  have hcube := abs_cube_bound_expanding M hm i
  have hcount : (expandingCount M T : ℝ) ≤ L := by
    exact_mod_cast le_trans (mask_expandingCount_le R C hC T) hL
  have hd : M.d T i = R.d T i := by simp [M, Run.mask, hi]
  rw [hd] at hcube
  apply le_four_cuberoot (abs_nonneg _) (Nat.cast_nonneg _)
  linarith

end Carpooling

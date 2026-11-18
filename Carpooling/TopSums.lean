import Carpooling.Basic

namespace Carpooling
open scoped Classical
open Finset
variable {V : Type*} [Fintype V]

lemma exists_top_set (x : V → ℝ) {r : ℕ} (hr : r ≤ Fintype.card V) :
    ∃ R : Finset V, R.card = r ∧
      ∀ Q : Finset V, Q.card = r → (∑ k ∈ Q, x k) ≤ ∑ k ∈ R, x k := by
  obtain ⟨Q, hQ, hc⟩ := exists_subset_card_eq (s := (univ : Finset V)) (by simpa using hr)
  have hn : ((univ : Finset V).powersetCard r).Nonempty := ⟨Q, by simp [hc]⟩
  obtain ⟨R, hR, hm⟩ := exists_max_image ((univ : Finset V).powersetCard r)
    (fun R => ∑ k ∈ R, x k) hn
  exact ⟨R, (mem_powersetCard.mp hR).2, fun Q hc => hm Q (by simp [hc])⟩

noncomputable def topSet (x : V → ℝ) (r : ℕ) : Finset V :=
  if h : r ≤ Fintype.card V then (exists_top_set x h).choose else ∅

noncomputable def topSum (x : V → ℝ) (r : ℕ) : ℝ := ∑ k ∈ topSet x r, x k

lemma topSet_spec (x : V → ℝ) {r : ℕ} (hr : r ≤ Fintype.card V) :
    (topSet x r).card = r ∧ ∀ Q : Finset V, Q.card = r →
      (∑ k ∈ Q, x k) ≤ topSum x r := by
  simp only [topSum, topSet, dif_pos hr]
  exact (exists_top_set x hr).choose_spec

lemma sum_le_topSum (x : V → ℝ) (Q : Finset V) :
    (∑ k ∈ Q, x k) ≤ topSum x Q.card :=
  (topSet_spec x (card_le_univ Q)).2 Q rfl

@[simp] lemma topSum_zero (x : V → ℝ) : topSum x 0 = 0 := by
  have h := (topSet_spec x (Nat.zero_le (Fintype.card V))).1
  have : topSet x 0 = ∅ := card_eq_zero.mp h
  simp [topSum, this]

lemma topSum_nonpos {x : V → ℝ} (hx : ∀ k, x k ≤ 0) (r : ℕ) :
    topSum x r ≤ 0 := sum_nonpos fun k _ => hx k

lemma topSum_all (x : V → ℝ) : topSum x (Fintype.card V) = ∑ k, x k := by
  have h := (topSet_spec x (le_refl (Fintype.card V))).1
  have : topSet x (Fintype.card V) = univ := eq_univ_of_card _ h
  simp [topSum, this]

lemma le_topSum_one (x : V → ℝ) (k : V) : x k ≤ topSum x 1 := by
  simpa using sum_le_topSum x {k}

variable [DecidableEq V]

/-- Lemma 3.4, including the boundary rank r = n-1. -/
theorem topSum_step {x y : V → ℝ} (e : Move x y) {r : ℕ}
    (_hr : 1 ≤ r) (hrn : r < Fintype.card V)
    (hinc : topSum x r < topSum y r) :
    2 * topSum y r - topSum y (r-1) - 2 ≤ topSum x (r+1) := by
  let R := topSet y r
  have hcard : R.card = r := (topSet_spec y (Nat.le_of_lt hrn)).1
  have hsum : (∑ k ∈ R, y k) = topSum y r := rfl
  have hbefore : (∑ k ∈ R, x k) ≤ topSum x r := by
    simpa [hcard] using sum_le_topSum x R
  have hchange := e.sum_update R
  have hu : e.u ∈ R := by
    by_contra h
    by_cases hv : e.v ∈ R
    · simp only [if_neg h, if_pos hv] at hchange
      linarith [e.weight_nonneg]
    · simp only [if_neg h, if_neg hv] at hchange
      linarith
  have hv : e.v ∉ R := by
    intro h
    simp only [if_pos hu, if_pos h] at hchange
    linarith
  have hrem : (R.erase e.u).card = r-1 := by simp [card_erase_of_mem hu, hcard]
  have hsmall := sum_le_topSum y (R.erase e.u)
  rw [hrem, sum_erase_eq_sub hu] at hsmall
  have huval : topSum y r - topSum y (r-1) ≤ y e.u := by linarith
  have hgap : y e.u - y e.v ≤ 2 := by
    rw [e.at_u, e.at_v]
    linarith [e.ordered, e.weight_le_one]
  have hunion : (insert e.v R).card = r+1 := by simp [hv, hcard]
  have hlarge := sum_le_topSum x (insert e.v R)
  rw [hunion] at hlarge
  have hsame : (∑ k ∈ insert e.v R, y k) = ∑ k ∈ insert e.v R, x k := by
    simpa [hu] using e.sum_update (insert e.v R)
  rw [sum_insert hv, hsum] at hsame
  linarith

end Carpooling

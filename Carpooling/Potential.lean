import Carpooling.Basic

namespace Carpooling
open scoped Classical
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def posSq (a : ℝ) : ℝ := (max a 0)^2
noncomputable def potential (x : V → ℝ) : ℝ := ∑ k, posSq (x k)

lemma posSq_nonneg (a : ℝ) : 0 ≤ posSq a := sq_nonneg _

lemma posSq_add_le (a b : ℝ) :
    posSq (a+b) ≤ posSq a + 2 * max a 0 * b + b^2 := by
  unfold posSq
  simp only [max_def]
  split_ifs <;> nlinarith

lemma posSq_contracting {a b w : ℝ} (_hab : a ≤ b)
    (hw : 0 ≤ w) (hc : a+w ≤ b) :
    posSq (a+w) + posSq (b-w) ≤ posSq a + posSq b := by
  unfold posSq
  simp only [max_def]
  split_ifs <;> nlinarith

lemma posSq_step_le {a b w : ℝ} (hab : a ≤ b)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    posSq (a+w) + posSq (b-w) ≤ posSq a + posSq b + 2 := by
  have ha := posSq_add_le a w
  have hb := posSq_add_le b (-w)
  rw [← sub_eq_add_neg] at hb
  have hmax : max a 0 ≤ max b 0 := max_le_max hab (le_refl 0)
  have hprod : 0 ≤ (max b 0 - max a 0) * w := mul_nonneg (by linarith) hw
  have hsq : w^2 ≤ 1 := by nlinarith
  nlinarith

lemma Move.potential_change {x y : V → ℝ} (e : Move x y) :
    potential y = potential x - posSq (x e.u) - posSq (x e.v) +
      posSq (x e.u + e.weight) + posSq (x e.v - e.weight) := by
  have h : ∀ k, posSq (y k) = posSq (x k) +
      (if k = e.u then posSq (x e.u + e.weight) - posSq (x e.u) else 0) +
      (if k = e.v then posSq (x e.v - e.weight) - posSq (x e.v) else 0) := by
    intro k
    by_cases hu : k = e.u
    · subst k; rw [e.at_u]; simp [e.distinct]
    · by_cases hv : k = e.v
      · subst k; rw [e.at_v]; simp [Ne.symm e.distinct]
      · rw [e.update]; simp [hu, hv]
  unfold potential
  simp_rw [h, sum_add_distrib]
  simp; ring

lemma Move.potential_le {x y : V → ℝ} (e : Move x y) :
    potential y ≤ potential x + (if e.Expanding then 2 else 0) := by
  classical
  rw [e.potential_change]
  by_cases h : e.Expanding
  · rw [if_pos h]
    linarith [posSq_step_le e.ordered e.weight_nonneg e.weight_le_one]
  · rw [if_neg h]
    have hc : x e.u + e.weight ≤ x e.v := le_of_not_gt h
    linarith [posSq_contracting e.ordered e.weight_nonneg hc]

lemma expandingCount_succ {T : ℕ} (R : Run V T) {t : ℕ} (ht : t < T) :
    expandingCount R (t+1) = expandingCount R t +
      (if (R.step t ht).Expanding then 1 else 0) := by
  classical
  unfold expandingCount
  rw [range_add_one, filter_insert]
  by_cases h : (R.step t ht).Expanding
  · simp [ht, h]
  · simp [ht, h]

/-- Lemma 3.2 with the exact prefix count. -/
theorem potential_bound {T : ℕ} (R : Run V T) (hinit : ∀ k, R.d 0 k ≤ 0)
    {t : ℕ} (ht : t ≤ T) : potential (R.d t) ≤ 2 * (expandingCount R t : ℝ) := by
  induction t with
  | zero =>
    have hz : potential (R.d 0) = 0 := by
      apply sum_eq_zero
      intro k _
      simp [posSq, max_eq_right (hinit k)]
    simp [hz, expandingCount]
  | succ t ih =>
    have hs := (R.step t (by omega)).potential_le
    have hp := ih (by omega)
    rw [expandingCount_succ R (by omega), Nat.cast_add]
    split_ifs at * <;> norm_num at * <;> linarith

end Carpooling

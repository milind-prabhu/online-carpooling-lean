import Carpooling.TopSums

namespace Carpooling
open scoped Classical

def threshold (D : ℝ) (r : ℕ) : ℝ := (r : ℝ) * (D - r + 1)

/-- The first-crossing argument, separated from the finite-set bookkeeping.
All hypotheses are established for actual top sums below. -/
theorem threshold_crossing {S : ℕ → ℕ → ℝ} {T m : ℕ} {D : ℝ}
    (hm : 1 ≤ m) (hmD : (m : ℝ) ≤ D)
    (hzero : ∀ t, S t 0 = 0)
    (hinit : ∀ r, S 0 r ≤ 0)
    (hstep : ∀ t < T, ∀ r, 1 ≤ r → r < m → S t r < S (t+1) r →
      2 * S (t+1) r - S (t+1) (r-1) - 2 ≤ S t (r+1))
    (hend : D ≤ S T 1) :
    ∃ t ≤ T, threshold D m ≤ S t m := by
  by_contra hn
  have hnever : ∀ t ≤ T, S t m < threshold D m := by
    intro t ht
    exact lt_of_not_ge fun h => hn ⟨t, ht, h⟩
  have hinv : ∀ t ≤ T, ∀ r, 1 ≤ r → r ≤ m → S t r < threshold D r := by
    intro t
    induction t with
    | zero =>
      intro ht r hr hrm
      have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
      have hrD : (r : ℝ) ≤ D := le_trans (by exact_mod_cast hrm) hmD
      have hpos : 0 < threshold D r := by unfold threshold; nlinarith
      exact lt_of_le_of_lt (hinit r) hpos
    | succ t ih =>
      intro ht r
      induction r using Nat.strong_induction_on with
      | h r ihr =>
        intro hr hrm
        by_cases heq : r = m
        · subst r; exact hnever _ ht
        have hrlt : r < m := by omega
        by_contra hnlt
        have hcross : threshold D r ≤ S (t+1) r := le_of_not_gt hnlt
        have hold := ih (by omega) r hr hrm
        have hsmall : S (t+1) (r-1) ≤ threshold D (r-1) := by
          by_cases hone : r = 1
          · subst r; simp [hzero, threshold]
          · exact le_of_lt (ihr (r-1) (by omega) (by omega) (by omega))
        have hnext := hstep t (by omega) r hr hrlt (lt_of_lt_of_le hold hcross)
        have hprev := ih (by omega) (r+1) (by omega) (by omega)
        have hrsub : ((r-1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
          rw [Nat.cast_sub hr]; norm_num
        have hrec : 2 * threshold D r - threshold D (r-1) - 2 =
            threshold D (r+1) := by
          unfold threshold
          rw [hrsub, Nat.cast_add, Nat.cast_one]
          ring
        linarith
  have hlast := hinv T (le_refl T) 1 (le_refl 1) hm
  simp only [threshold, Nat.cast_one] at hlast
  linarith

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Lemma 3.3. A lower bound D on one chip suffices; D need not be the maximum. -/
theorem spreadness {T : ℕ} (R : Run V T)
    (hinit : ∀ k, R.d 0 k ≤ 0) {D : ℝ} {i : V}
    (hD : D ≤ R.d T i) {r : ℕ} (hr : 1 ≤ r)
    (hrn : r ≤ Fintype.card V) (hrD : (r : ℝ) ≤ D) :
    ∃ t ≤ T, (r : ℝ) * (D - r + 1) ≤ topSum (R.d t) r := by
  apply threshold_crossing (S := fun t r => topSum (R.d t) r) hr hrD
  · intro t; exact topSum_zero _
  · intro s; exact topSum_nonpos hinit s
  · intro t ht s hs hsr hinc
    exact topSum_step (R.step t ht) hs (lt_of_lt_of_le hsr hrn) hinc
  · exact le_trans hD (le_topSum_one _ i)

end Carpooling
